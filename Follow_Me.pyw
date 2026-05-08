"""
代码编辑器临摹应用
功能: 基于PyQt6的代码编辑器，具备代码高亮和AI辅助临摹功能
"""

import sys
import os
import json
import difflib
import keyword
import re
from typing import Optional, List, Tuple, Dict, Any

from PyQt6.QtCore import (
    Qt, QSize, QTimer, pyqtSignal, QThread, pyqtSignal, 
    QPoint, QRect, QPropertyAnimation, QEasingCurve,
    QRegularExpression, QEvent
)
from PyQt6.QtGui import (
    QFont, QFontDatabase, QColor, QPalette, QAction, 
    QKeySequence, QTextCharFormat, QSyntaxHighlighter, 
    QTextDocument, QIcon, QPixmap, QPainter, QBrush,
    QLinearGradient, QTextCursor, QTextBlockFormat,
    QTextFormat, QKeyEvent, QPaintEvent, QResizeEvent,
    QFontMetrics, QTextOption, QTextDocument, QTextBlock,
    QTextLayout, QTextLine, QGuiApplication, QCursor
)
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, 
    QHBoxLayout, QTextEdit, QPushButton, QLabel, 
    QMessageBox, QFileDialog, QInputDialog, QToolBar,
    QStatusBar, QSplitter, QFrame, QScrollArea, 
    QTextBrowser, QDialog, QVBoxLayout, QLineEdit,
    QDialogButtonBox, QListWidget, QListWidgetItem,
    QStyleFactory, QStyle, QSizePolicy, QMenu, QMenuBar,
    QProgressBar, QToolTip, QPlainTextEdit, QComboBox,
    QGroupBox, QRadioButton, QCheckBox, QSpinBox,
    QTabWidget, QTabBar, QFormLayout, QGridLayout
)

# AI相关
import requests
import threading
import time

# ============================
# 1. Python语法高亮器
# ============================
class PythonHighlighter(QSyntaxHighlighter):
    """Python语法高亮器"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        
        # 定义各种语法格式
        self.highlighting_rules = []
        
        # 关键字
        keyword_format = QTextCharFormat()
        keyword_format.setForeground(QColor("#0000FF"))
        keyword_format.setFontWeight(QFont.Weight.Bold)
        
        keywords = keyword.kwlist
        for word in keywords:
            pattern = r'\b' + word + r'\b'
            self.highlighting_rules.append((QRegularExpression(pattern), keyword_format))
        
        # 字符串
        string_format = QTextCharFormat()
        string_format.setForeground(QColor("#008000"))
        self.highlighting_rules.append((QRegularExpression(r'\".*\"'), string_format))
        self.highlighting_rules.append((QRegularExpression(r"\'.*\'"), string_format))
        
        # 注释
        comment_format = QTextCharFormat()
        comment_format.setForeground(QColor("#808080"))
        comment_format.setFontItalic(True)
        self.highlighting_rules.append((QRegularExpression(r'#.*'), comment_format))
        
        # 数字
        number_format = QTextCharFormat()
        number_format.setForeground(QColor("#FF00FF"))
        self.highlighting_rules.append((QRegularExpression(r'\b[0-9]+\b'), number_format))
        
        # 函数
        function_format = QTextCharFormat()
        function_format.setForeground(QColor("#000080"))
        function_format.setFontWeight(QFont.Weight.Bold)
        self.highlighting_rules.append((QRegularExpression(r'\b[A-Za-z_][A-Za-z0-9_]*\s*(?=\()'), function_format))
        
        # 类名
        class_format = QTextCharFormat()
        class_format.setForeground(QColor("#0000A0"))
        class_format.setFontWeight(QFont.Weight.Bold)
        self.highlighting_rules.append((QRegularExpression(r'\bclass\s+([A-Za-z_][A-Za-z0-9_]*)'), class_format))
        
    def highlightBlock(self, text):
        """高亮文本块"""
        for pattern, format in self.highlighting_rules:
            match_iterator = pattern.globalMatch(text)
            while match_iterator.hasNext():
                match = match_iterator.next()
                self.setFormat(match.capturedStart(), match.capturedLength(), format)
        
        # 处理多行字符串
        self.setCurrentBlockState(0)
        
        # 处理三引号字符串
        triple_single = QRegularExpression(r"'''")
        triple_double = QRegularExpression(r'"""')
        
        start = 0
        if self.previousBlockState() != 1:
            start = triple_single.match(text).capturedStart()
            if start >= 0:
                self.setCurrentBlockState(1)
            else:
                start = triple_double.match(text).capturedStart()
                if start >= 0:
                    self.setCurrentBlockState(2)
        
        while start >= 0:
            if self.currentBlockState() == 1:
                end_match = triple_single.match(text, start + 3)
            else:
                end_match = triple_double.match(text, start + 3)
                
            if end_match.hasMatch():
                end = end_match.capturedEnd()
                length = end - start
            else:
                end = len(text)
                length = end - start
                self.setCurrentBlockState(0)
                
            string_format = QTextCharFormat()
            string_format.setForeground(QColor("#008000"))
            self.setFormat(start, length, string_format)
            
            if self.currentBlockState() == 0:
                if self.currentBlockState() == 1:
                    start = triple_single.match(text, end).capturedStart()
                else:
                    start = triple_double.match(text, end).capturedStart()
            else:
                break


# ============================
# 2. 代码编辑器（基于QPlainTextEdit）
# ============================
class CodeEditor(QPlainTextEdit):
    """自定义代码编辑器，基于QPlainTextEdit实现"""
    
    # 自定义信号
    text_changed = pyqtSignal()
    line_verified = pyqtSignal(int, bool)  # 行号, 是否正确
    imitation_completed = pyqtSignal(bool)  # 是否完成所有代码
    request_force_newline = pyqtSignal(int, str, str)  # 行号, 用户输入, 模板
    
    def __init__(self, main_window=None):
        super().__init__(main_window)
        
        # 主窗口引用，用于控制提示标签
        self.main_window = main_window
        
        # 编辑器状态
        self.is_imitation_mode = False
        self.template_lines = []  # 模板代码行
        self.current_imitation_line = 0  # 当前临摹的行号
        self.allow_force_newline = False  # 是否允许强制换行
        self.error_lines = set()  # 错误的行号
        self.template_formats = {}  # 模板行格式
        self.error_formats = {}  # 错误行格式
        
        # 颜色定义（必须在highlight_current_line之前）
        self.COLORS = {
            "background": QColor("#ffffff"),
            "foreground": QColor("#000000"),
            "line_number_bg": QColor("#f0f0f0"),
            "line_number_fg": QColor("#888888"),
            "current_line_bg": QColor("#f5f5f5"),
            "selection_bg": QColor("#c0e0ff"),
            "template_text": QColor("#888888"),  # 模板文本颜色
            "error_text": QColor("#ff4444"),     # 错误文本颜色
            "error_flag": QColor("#ff4444"),     # 错误标志颜色
            "correct_text": QColor("#000000"),   # 正确文本颜色
        }
        
        # 跟踪错误行
        self.error_lines = set()
        
        # 跟踪被忽略的错误行（黄色）
        self.ignore_lines = set()
        
        # 设置字体
        font = QFont("Consolas" if sys.platform == "win32" else "Monospace", 12)
        self.setFont(font)
        
        # 设置行号区域
        self.line_number_area = LineNumberArea(self)
        
        # 设置高亮器
        self.highlighter = PythonHighlighter(self.document())
        
        # 连接信号
        self.blockCountChanged.connect(self.update_line_number_area_width)
        self.updateRequest.connect(self.update_line_number_area)
        self.cursorPositionChanged.connect(self.highlight_current_line)
        self.cursorPositionChanged.connect(self._on_imitation_cursor_moved)
        self.textChanged.connect(self._on_imitation_text_changed)
        
        # 初始更新
        self.update_line_number_area_width(0)
        self.highlight_current_line()
        
        # 设置编辑器属性
        self.setTabStopDistance(40)  # 4个字符的宽度
        self.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        
        # 设置样式
        self.setStyleSheet(f"""
            QPlainTextEdit {{
                background-color: {self.COLORS['background'].name()};
                color: {self.COLORS['foreground'].name()};
                selection-background-color: {self.COLORS['selection_bg'].name()};
                font-family: 'Consolas', 'Monospace';
                font-size: 12px;
            }}
        """)
        
    def line_number_area_width(self):
        """计算行号区域的宽度"""
        digits = 1
        count = max(1, self.blockCount())
        while count >= 10:
            count //= 10
            digits += 1
        space = 10 + self.fontMetrics().horizontalAdvance('9') * digits
        return space
    
    def update_line_number_area_width(self, _):
        """更新行号区域宽度"""
        self.setViewportMargins(self.line_number_area_width(), 0, 0, 0)
    
    def update_line_number_area(self, rect, dy):
        """更新行号区域"""
        if dy:
            self.line_number_area.scroll(0, dy)
        else:
            self.line_number_area.update(0, rect.y(), 
                                        self.line_number_area.width(), rect.height())
        
        if rect.contains(self.viewport().rect()):
            self.update_line_number_area_width(0)
    
    def resizeEvent(self, event):
        """重设大小事件"""
        super().resizeEvent(event)
        cr = self.contentsRect()
        self.line_number_area.setGeometry(
            QRect(cr.left(), cr.top(), 
                 self.line_number_area_width(), cr.height())
        )
    
    def highlight_current_line(self):
        """高亮当前行"""
        extra_selections = []
        
        if not self.isReadOnly():
            selection = QTextEdit.ExtraSelection()
            line_color = self.COLORS["current_line_bg"]
            selection.format.setBackground(line_color)
            selection.format.setProperty(QTextFormat.Property.FullWidthSelection, True)
            selection.cursor = self.textCursor()
            selection.cursor.clearSelection()
            extra_selections.append(selection)
        
        self.setExtraSelections(extra_selections)
    
    def line_number_area_paint_event(self, event):
        """绘制行号区域"""
        painter = QPainter(self.line_number_area)
        painter.fillRect(event.rect(), self.COLORS["line_number_bg"])
        
        block = self.firstVisibleBlock()
        block_number = block.blockNumber()
        top = self.blockBoundingGeometry(block).translated(self.contentOffset()).top()
        bottom = top + self.blockBoundingRect(block).height()
        
        while block.isValid() and top <= event.rect().bottom():
            if block.isVisible() and bottom >= event.rect().top():
                number = str(block_number + 1)
                
                # 如果该行有错误，在左侧画一个圆圈标记
                if block_number in self.error_lines and self.is_imitation_mode:
                    # 检查是否被忽略（黄色）
                    if block_number in self.ignore_lines:
                        painter.setBrush(QColor("#ffaa00"))  # 黄色
                    else:
                        painter.setBrush(self.COLORS["error_flag"])  # 红色
                    painter.setPen(Qt.PenStyle.NoPen)
                    circle_radius = 7  # 圆圈大小
                    circle_y = int(top + (self.fontMetrics().height() / 2))
                    painter.drawEllipse(
                        2,  # x 位置（在行号左侧）
                        circle_y - circle_radius,  # y 位置
                        circle_radius * 2,  # 宽度
                        circle_radius * 2   # 高度
                    )
                
                # 绘制行号
                painter.setPen(self.COLORS["line_number_fg"])
                painter.drawText(0, int(top), 
                               self.line_number_area.width() - 5, 
                               self.fontMetrics().height(),
                               Qt.AlignmentFlag.AlignRight, number)
            
            block = block.next()
            top = bottom
            bottom = top + self.blockBoundingRect(block).height()
            block_number += 1
    
    def enter_imitation_mode(self, template_code: str):
        """进入临摹模式"""
        self.is_imitation_mode = True
        self.current_imitation_line = 0
        self.allow_force_newline = False
        self.error_lines.clear()
        self.template_formats.clear()
        self.error_formats.clear()

        # 保存模板代码
        self.template_lines = template_code.split('\n')

        # 清空编辑器
        self.clear()

        # 设置为非只读
        self.setReadOnly(False)

        # 在独立提示标签中显示当前行参考代码
        if len(self.template_lines) > 0:
            self._update_hint_label(0)
        
    def exit_imitation_mode(self, completed=False):
        """退出临摹模式"""
        # 保存当前光标位置
        cursor = self.textCursor()
        cursor_pos = cursor.position()
        
        self.is_imitation_mode = False
        self.template_lines = []
        self.current_imitation_line = 0
        self.allow_force_newline = False
        self.error_lines.clear()
        self.template_formats.clear()
        self.error_formats.clear()
        self.ignore_lines.clear()
        
        # 恢复正常编辑
        self.setReadOnly(False)
        
        # 清除所有特殊样式
        self._clear_all_styles()
        
        # 恢复光标位置
        cursor.setPosition(cursor_pos)
        self.setTextCursor(cursor)
        
        # 隐藏提示标签
        if self.main_window:
            self.main_window.imitation_hint_label.hide()
        
        # 发射信号（携带是否完成的信息）
        self.imitation_completed.emit(completed)

    def _update_hint_label(self, line_index: int):
        """更新提示标签显示当前行参考代码"""
        if self.main_window:
            if line_index < len(self.template_lines):
                hint_text = f"参考代码 (第{line_index + 1}行): {self.template_lines[line_index]}"
                self.main_window.imitation_hint_label.setText(hint_text)
                self.main_window.imitation_hint_label.show()
            else:
                self.main_window.imitation_hint_label.hide()
        
        self.current_imitation_line = line_index

    def _on_imitation_cursor_moved(self):
        """当光标位置变化时，更新提示标签显示当前行的参考代码"""
        if not self.is_imitation_mode:
            return
        
        cursor = self.textCursor()
        current_line = cursor.blockNumber()
        
        # 如果当前行与提示标签显示的行不同，则更新
        if current_line != self.current_imitation_line:
            if current_line < len(self.template_lines):
                self._update_hint_label(current_line)

    def _on_imitation_text_changed(self):
        """当文本变化时，检查并标红不匹配的行"""
        if not self.is_imitation_mode:
            return
        
        # 阻止信号递归触发
        self.blockSignals(True)
        
        try:
            # 遍历已输入的每一行，检查是否匹配
            for i in range(min(self.blockCount(), len(self.template_lines))):
                block = self.document().findBlockByNumber(i)
                user_text = block.text()
                template_line = self.template_lines[i]
                
                # 检查是否匹配（忽略空格和注释差异）
                is_correct = self._is_line_matching(user_text, template_line)
                
                if not is_correct and user_text.strip():
                    # 不匹配且非空行，添加到错误行集合并标红
                    self.error_lines.add(i)
                    self._highlight_line_red(i)
                else:
                    # 匹配或空行，从错误行集合移除并清除红色
                    self.error_lines.discard(i)
                    self._clear_line_highlight(i)
            
            # 触发行号区域重绘，以更新错误标志
            self.line_number_area.update()
        finally:
            # 恢复信号
            self.blockSignals(False)

    def _highlight_line_red(self, line_index: int):
        """将指定行标红"""
        block = self.document().findBlockByNumber(line_index)
        cursor = QTextCursor(block)
        
        # 选择整行
        cursor.select(QTextCursor.SelectionType.BlockUnderCursor)
        
        # 设置红色格式
        fmt = QTextCharFormat()
        fmt.setForeground(QColor("#ff0000"))
        cursor.setCharFormat(fmt)

    def _clear_line_highlight(self, line_index: int):
        """清除指定行的红色标记（恢复默认颜色）"""
        block = self.document().findBlockByNumber(line_index)
        cursor = QTextCursor(block)
        
        # 选择整行
        cursor.select(QTextCursor.SelectionType.BlockUnderCursor)
        
        # 恢复默认格式
        fmt = QTextCharFormat()
        fmt.setForeground(self.COLORS["foreground"])
        cursor.setCharFormat(fmt)

    def _apply_template_style(self):
        """应用模板样式（灰色）到整个文档"""
        cursor = QTextCursor(self.document())
        cursor.select(QTextCursor.SelectionType.Document)
        
        # 创建灰色文本格式
        fmt = QTextCharFormat()
        fmt.setForeground(self.COLORS["template_text"])
        
        # 应用格式
        cursor.mergeCharFormat(fmt)
        
    def _clear_all_styles(self):
        """清除所有特殊样式（保留 Python 语法高亮）"""
        # 重新设置高亮器以恢复语法高亮
        self.highlighter.rehighlight()
        
    def _lock_to_current_line(self):
        """锁定到当前行，不允许编辑其他行"""
        # 在临摹模式下，我们通过事件过滤来控制
        pass
        
    def _update_line_style(self, line: int, is_correct: bool):
        """更新行样式"""
        if line < 0 or line >= self.document().blockCount():
            return
            
        # 获取指定行的文本块
        block = self.document().findBlockByNumber(line)
        cursor = QTextCursor(block)
        cursor.select(QTextCursor.SelectionType.BlockUnderCursor)
        
        # 创建格式
        fmt = QTextCharFormat()
        
        if is_correct:
            # 正确：黑色
            fmt.setForeground(self.COLORS["correct_text"])
        else:
            # 错误：红色
            fmt.setForeground(self.COLORS["error_text"])
            self.error_lines.add(line)
        
        # 应用格式
        cursor.mergeCharFormat(fmt)
        
    def keyPressEvent(self, event: QKeyEvent):
        """处理键盘事件，实现临摹模式的特殊逻辑和缩进功能"""
        # 处理 Tab 和 Shift+Tab 缩进（只在有选中内容时）
        if event.key() == Qt.Key.Key_Tab and self.textCursor().hasSelection():
            self._handle_tab_indent(event)
            return
        
        if not self.is_imitation_mode:
            super().keyPressEvent(event)
            return

        # 获取当前行
        cursor = self.textCursor()
        current_line = cursor.blockNumber()
        block = cursor.block()
        user_text = block.text()

        # 检查是否是回车键
        if event.key() == Qt.Key.Key_Return or event.key() == Qt.Key.Key_Enter:
            # 获取模板行
            if current_line < len(self.template_lines):
                template_line = self.template_lines[current_line]

                # 检查是否匹配（忽略空格和注释差异）
                is_correct = self._is_line_matching(user_text, template_line)

                if is_correct or not user_text.strip():
                    # 正确或为空：正常换行
                    self.allow_force_newline = False
                    super().keyPressEvent(event)
                    new_line_index = current_line + 1

                    # 检查是否完成所有行
                    if new_line_index >= len(self.template_lines):
                        self.exit_imitation_mode(True)
                    else:
                        # 更新提示标签显示下一行参考代码
                        self._update_hint_label(new_line_index)
                else:
                    # 不一致：检查是否可以强制换行
                    if self.allow_force_newline:
                        # 第二次回车，强制换行
                        self.allow_force_newline = False
                        super().keyPressEvent(event)
                        new_line_index = current_line + 1

                        if new_line_index >= len(self.template_lines):
                            self.exit_imitation_mode(True)
                        else:
                            self._update_hint_label(new_line_index)
                    else:
                        # 第一次回车，显示提示
                        self.allow_force_newline = True
                        self.request_force_newline.emit(
                            current_line, user_text, template_line
                        )
                        return
            else:
                # 超出模板行数，正常换行
                super().keyPressEvent(event)
        else:
            # 其他按键，正常处理
            super().keyPressEvent(event)
    
    def _handle_tab_indent(self, event):
        """处理 Tab 和 Ctrl+Tab 缩进"""
        cursor = self.textCursor()
        start_pos = cursor.selectionStart()
        end_pos = cursor.selectionEnd()
        
        if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
            # Ctrl+Tab：减少缩进
            self._unindent_selected_lines(start_pos, end_pos)
        else:
            # Tab：增加缩进
            self._indent_selected_lines(start_pos, end_pos)
    
    def _indent_selected_lines(self, start_pos, end_pos):
        """为选中的行添加缩进"""
        start_block = self.document().findBlock(start_pos)
        end_block = self.document().findBlock(end_pos)
        
        cursor = QTextCursor(self.document())
        
        block = start_block
        while block.isValid() and block <= end_block:
            cursor.setPosition(block.position())
            cursor.insertText("    ")  # 添加4个空格作为缩进
            block = block.next()
    
    def _unindent_selected_lines(self, start_pos, end_pos):
        """为选中的行减少缩进"""
        start_block = self.document().findBlock(start_pos)
        end_block = self.document().findBlock(end_pos)
        
        cursor = QTextCursor(self.document())
        
        block = start_block
        while block.isValid() and block <= end_block:
            text = block.text()
            if text.startswith("    "):
                # 移除4个空格
                cursor.setPosition(block.position())
                cursor.movePosition(QTextCursor.MoveOperation.Right, QTextCursor.MoveMode.KeepAnchor, 4)
                cursor.removeSelectedText()
            elif text.startswith(" "):
                # 移除单个空格
                cursor.setPosition(block.position())
                cursor.movePosition(QTextCursor.MoveOperation.Right, QTextCursor.MoveMode.KeepAnchor)
                cursor.removeSelectedText()
            block = block.next()

    def _is_line_matching(self, user_text: str, template_line: str) -> bool:
        """检查用户输入与模板行是否匹配（忽略空格和注释差异）"""
        import re

        # 提取代码部分（去除注释）
        def remove_comment(line):
            if '#' in line:
                return line.split('#')[0]
            return line

        user_code = remove_comment(user_text)
        template_code = remove_comment(template_line)

        # 规范化空格：去除首尾空格，将连续空格替换为单个空格
        user_normalized = re.sub(r'\s+', ' ', user_code.strip())
        template_normalized = re.sub(r'\s+', ' ', template_code.strip())

        # 比较规范化后的代码
        return user_normalized == template_normalized


class LineNumberArea(QWidget):
    """行号区域部件"""
    
    def __init__(self, editor):
        super().__init__(editor)
        self.editor = editor
    
    def sizeHint(self):
        return QSize(self.editor.line_number_area_width(), 0)
    
    def paintEvent(self, event):
        self.editor.line_number_area_paint_event(event)
    
    def mousePressEvent(self, event):
        """处理鼠标点击事件"""
        if not self.editor.is_imitation_mode:
            super().mousePressEvent(event)
            return

        # 获取点击位置对应的行号
        cursor_pos = self.mapToGlobal(event.pos())
        editor_pos = self.editor.mapFromGlobal(cursor_pos)
        cursor = self.editor.cursorForPosition(editor_pos)
        line_number = cursor.blockNumber()

        # 如果点击的是错误行，切换忽略状态
        if line_number in self.editor.error_lines:
            if line_number in self.editor.ignore_lines:
                # 从忽略列表移除（恢复红色）
                self.editor.ignore_lines.discard(line_number)
            else:
                # 添加到忽略列表（变为黄色）并清除红色标红
                self.editor.ignore_lines.add(line_number)
                self.editor._clear_line_highlight(line_number)

            # 重绘行号区域
            self.update()


# ============================
# 3. AI服务模块
# ============================
class AIService:
    """AI服务，用于调用智谱API生成代码"""
    
    # 硬编码的API密钥和URL
    API_KEY = "e7509fc557394a619bc89d9bc44172ce.qY4uSyCofHoCfQSX"
    API_URL = "https://open.bigmodel.cn/api/paas/v4/chat/completions"
    
    @staticmethod
    def generate_code_from_prompt(user_prompt: str, max_tokens: int = 2000) -> str:
        """
        根据用户需求生成代码
        
        参数:
            user_prompt: 用户的需求描述
            max_tokens: 最大token数
            
        返回:
            生成的代码字符串
        """
        # 构建系统提示词
        system_prompt = """你是一个专业的Python程序员，请根据用户的需求，生成完整、可运行、无错误的Python代码。
        要求：
        1. 只返回代码与注释，不要有任何解释或额外文本
        2. 代码必须是完整的，可以直接复制运行
        3. 确保代码符合PEP8规范
        4. 如果有需要导入的模块，请包含在代码中
        5. 代码应该包含一个可执行的入口点（if __name__ == "__main__":）"""
        
        # 构建完整的用户提示词
        full_prompt = f"""请根据以下需求编写一个完整的应用程序：
        
        需求：{user_prompt}
        
        请确保代码完整、可运行，并且遵循最佳实践。"""
        
        # 准备请求头
        headers = {
            "Authorization": f"Bearer {AIService.API_KEY}",
            "Content-Type": "application/json"
        }
        
        # 准备请求数据
        data = {
            "model": "glm-4",
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": full_prompt}
            ],
            "max_tokens": max_tokens,
            "temperature": 0.7,
            "top_p": 0.9
        }
        
        try:
            # 发送请求
            response = requests.post(
                AIService.API_URL, 
                headers=headers, 
                json=data, 
                timeout=30
            )
            
            # 检查响应状态
            if response.status_code == 200:
                result = response.json()
                if "choices" in result and len(result["choices"]) > 0:
                    content = result["choices"][0]["message"]["content"]
                    
                    # 清理内容
                    if "```python" in content:
                        parts = content.split("```python")
                        if len(parts) > 1:
                            code_part = parts[1].split("```")[0]
                            return code_part.strip()
                    elif "```" in content:
                        parts = content.split("```")
                        if len(parts) > 1:
                            code_part = parts[1]
                            return code_part.strip()
                    
                    return content.strip()
                else:
                    return f"# AI响应格式错误: {result}"
            else:
                return f"# API请求失败: {response.status_code}\n# 错误详情: {response.text}"
                
        except requests.exceptions.Timeout:
            return "# 错误: AI请求超时，请检查网络连接"
        except requests.exceptions.RequestException as e:
            return f"# 网络请求错误: {str(e)}"
        except Exception as e:
            return f"# 未知错误: {str(e)}"


# ============================
# 4. AI代码生成线程
# ============================
class CodeGenerationThread(QThread):
    """AI代码生成线程，避免阻塞UI"""
    
    # 自定义信号
    generation_started = pyqtSignal()
    generation_finished = pyqtSignal(str)
    generation_error = pyqtSignal(str)
    
    def __init__(self, prompt: str):
        super().__init__()
        self.prompt = prompt
        
    def run(self):
        """线程运行函数"""
        self.generation_started.emit()
        
        try:
            generated_code = AIService.generate_code_from_prompt(self.prompt)
            self.generation_finished.emit(generated_code)
        except Exception as e:
            self.generation_error.emit(str(e))


# ============================
# 5. 主窗口
# ============================
class MainWindow(QMainWindow):
    """主窗口"""
    
    def __init__(self):
        super().__init__()
        
        # 窗口设置
        self.setWindowTitle("Follow Me")
        self.setGeometry(100, 100, 1200, 800)
        
        # 设置窗口图标（读取当前目录下的icon.ico）
        icon_path = os.path.join(os.path.dirname(__file__), "icon.ico")
        if os.path.exists(icon_path):
            self.setWindowIcon(QIcon(icon_path))
        
        # 应用浅色主题
        self._apply_light_theme()
        
        # 初始化UI
        self._init_ui()
        
        # 状态变量
        self.current_file = None
        self.is_imitation_mode = False
        self.generation_thread = None
        
    def _apply_light_theme(self):
        """应用浅色主题"""
        QApplication.setStyle(QStyleFactory.create("Fusion"))
        
        palette = QPalette()
        palette.setColor(QPalette.ColorRole.Window, QColor("#f5f5f5"))
        palette.setColor(QPalette.ColorRole.WindowText, QColor("#333333"))
        palette.setColor(QPalette.ColorRole.Base, QColor("#ffffff"))
        palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#f0f0f0"))
        palette.setColor(QPalette.ColorRole.ToolTipBase, QColor("#ffffff"))
        palette.setColor(QPalette.ColorRole.ToolTipText, QColor("#333333"))
        palette.setColor(QPalette.ColorRole.Text, QColor("#333333"))
        palette.setColor(QPalette.ColorRole.Button, QColor("#e0e0e0"))
        palette.setColor(QPalette.ColorRole.ButtonText, QColor("#333333"))
        palette.setColor(QPalette.ColorRole.BrightText, Qt.GlobalColor.red)
        palette.setColor(QPalette.ColorRole.Link, QColor("#0066cc"))
        palette.setColor(QPalette.ColorRole.Highlight, QColor("#80cbc4"))
        palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
        
        QApplication.setPalette(palette)
        
    def _init_ui(self):
        """初始化UI"""
        # 创建中心部件
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        # 主布局
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        
        # 创建临摹提示标签（独立显示当前行参考代码）
        self.imitation_hint_label = QLabel()
        self.imitation_hint_label.setStyleSheet("""
            QLabel {
                background-color: #f5f5f5;
                color: #888888;
                padding: 8px;
                font-family: 'Consolas', 'Monospace';
                font-size: 12px;
                border-bottom: 1px solid #e0e0e0;
            }
        """)
        self.imitation_hint_label.hide()
        main_layout.addWidget(self.imitation_hint_label)
        
        # 创建编辑器（必须在创建工具栏之前，因为工具栏需要用到self.editor）
        self.editor = CodeEditor(self)
        main_layout.addWidget(self.editor)
        
        # 创建工具栏
        self._create_toolbar()
        
        # 连接编辑器信号
        self.editor.textChanged.connect(self._on_text_changed)
        self.editor.imitation_completed.connect(self._on_imitation_completed)
        self.editor.request_force_newline.connect(self._show_force_newline_warning)
        
        # 创建状态栏
        self.status_bar = QStatusBar()
        self.setStatusBar(self.status_bar)
        
        # 状态标签
        self.status_label = QLabel("就绪")
        self.status_bar.addWidget(self.status_label)
        
        # 添加提示标签
        self.hint_label = QLabel("提示: 按Ctrl+I开始临摹，Ctrl+S保存文件")
        self.status_bar.addPermanentWidget(self.hint_label)
        
    def _create_toolbar(self):
        """创建工具栏"""
        toolbar = QToolBar("主工具栏")
        toolbar.setMovable(False)
        self.addToolBar(toolbar)
        
        # 文件菜单
        file_menu = self.menuBar().addMenu("文件")
        
        # 新建文件
        new_action = QAction("新建", self)
        new_action.setShortcut(QKeySequence.StandardKey.New)
        new_action.triggered.connect(self._new_file)
        file_menu.addAction(new_action)
        toolbar.addAction(new_action)
        
        # 打开文件
        open_action = QAction("打开", self)
        open_action.setShortcut(QKeySequence.StandardKey.Open)
        open_action.triggered.connect(self._open_file)
        file_menu.addAction(open_action)
        toolbar.addAction(open_action)
        
        # 保存文件
        save_action = QAction("保存", self)
        save_action.setShortcut(QKeySequence.StandardKey.Save)
        save_action.triggered.connect(self._save_file)
        file_menu.addAction(save_action)
        toolbar.addAction(save_action)
        
        # 另存为
        save_as_action = QAction("另存为", self)
        save_as_action.triggered.connect(self._save_file_as)
        file_menu.addAction(save_as_action)
        
        file_menu.addSeparator()
        
        # 退出
        exit_action = QAction("退出", self)
        exit_action.setShortcut(QKeySequence.StandardKey.Quit)
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)
        
        toolbar.addSeparator()
        
        # 编辑菜单
        edit_menu = self.menuBar().addMenu("编辑")
        
        # 撤销
        undo_action = QAction("撤销", self)
        undo_action.setShortcut(QKeySequence.StandardKey.Undo)
        undo_action.triggered.connect(self.editor.undo)
        edit_menu.addAction(undo_action)
        
        # 重做
        redo_action = QAction("重做", self)
        redo_action.setShortcut(QKeySequence.StandardKey.Redo)
        redo_action.triggered.connect(self.editor.redo)
        edit_menu.addAction(redo_action)
        
        edit_menu.addSeparator()
        
        # 复制
        copy_action = QAction("复制", self)
        copy_action.setShortcut(QKeySequence.StandardKey.Copy)
        copy_action.triggered.connect(self.editor.copy)
        edit_menu.addAction(copy_action)
        
        # 剪切
        cut_action = QAction("剪切", self)
        cut_action.setShortcut(QKeySequence.StandardKey.Cut)
        cut_action.triggered.connect(self.editor.cut)
        edit_menu.addAction(cut_action)
        
        # 粘贴
        paste_action = QAction("粘贴", self)
        paste_action.setShortcut(QKeySequence.StandardKey.Paste)
        paste_action.triggered.connect(self.editor.paste)
        edit_menu.addAction(paste_action)
        
        toolbar.addSeparator()
        
        # 临摹模式菜单
        imitation_menu = self.menuBar().addMenu("临摹模式")
        
        # 开始临摹
        start_imitation_action = QAction("开始临摹", self)
        start_imitation_action.setShortcut("Ctrl+I")
        start_imitation_action.triggered.connect(self._start_imitation)
        imitation_menu.addAction(start_imitation_action)
        toolbar.addAction(start_imitation_action)
        
        # 从文件导入临摹代码
        import_imitation_action = QAction("从文件导入临摹", self)
        import_imitation_action.setShortcut("Ctrl+Shift+O")
        import_imitation_action.triggered.connect(self._import_imitation)
        imitation_menu.addAction(import_imitation_action)
        
        # 退出临摹
        exit_imitation_action = QAction("退出临摹", self)
        exit_imitation_action.setShortcut("Ctrl+Shift+I")
        exit_imitation_action.triggered.connect(self._exit_imitation)
        imitation_menu.addAction(exit_imitation_action)
        toolbar.addAction(exit_imitation_action)
        
    def _new_file(self):
        """新建文件"""
        if self._check_save():
            self.editor.clear()
            self.current_file = None
            self.status_label.setText("新建文件")
            
    def _open_file(self):
        """打开文件"""
        if self._check_save():
            file_path, _ = QFileDialog.getOpenFileName(
                self, "打开文件", "", "Python文件 (*.py);;所有文件 (*.*)"
            )
            
            if file_path:
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        
                    self.editor.setPlainText(content)
                    self.current_file = file_path
                    self.status_label.setText(f"已打开: {os.path.basename(file_path)}")
                    
                except Exception as e:
                    QMessageBox.critical(self, "错误", f"无法打开文件: {str(e)}")
                    
    def _save_file(self) -> bool:
        """保存文件"""
        if self.current_file:
            return self._save_to_file(self.current_file)
        else:
            return self._save_file_as()
            
    def _save_file_as(self) -> bool:
        """另存为"""
        file_path, _ = QFileDialog.getSaveFileName(
            self, "保存文件", "", "Python文件 (*.py);;所有文件 (*.*)"
        )
        
        if not file_path:
            return False
        
        if not file_path.endswith('.py'):
            file_path += '.py'
            
        success = self._save_to_file(file_path)
        if success:
            self.current_file = file_path
        return success
            
    def _save_to_file(self, file_path: str) -> bool:
        """保存到文件"""
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(self.editor.toPlainText())
                
            self.status_label.setText(f"已保存: {os.path.basename(file_path)}")
            return True
            
        except Exception as e:
            QMessageBox.critical(self, "错误", f"无法保存文件: {str(e)}")
            return False
            
    def _check_save(self) -> bool:
        """检查是否需要保存"""
        if self.editor.document().isModified():
            reply = QMessageBox.question(
                self, "保存更改", 
                "文档已更改，是否保存？",
                QMessageBox.StandardButton.Yes | 
                QMessageBox.StandardButton.No | 
                QMessageBox.StandardButton.Cancel
            )
            
            if reply == QMessageBox.StandardButton.Yes:
                return self._save_file()
            elif reply == QMessageBox.StandardButton.No:
                return True
            else:
                return False
                
        return True
    
    def _import_imitation(self):
        """从文件导入临摹代码"""
        if self.is_imitation_mode:
            QMessageBox.warning(self, "警告", "已经在临摹模式中！")
            return
        
        # 打开文件选择对话框
        file_path, _ = QFileDialog.getOpenFileName(
            self, "选择代码文件", "", 
            "Python文件 (*.py);;所有文件 (*.*)"
        )
        
        if not file_path:
            return
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                code = f.read()
            
            if not code.strip():
                QMessageBox.warning(self, "警告", "文件内容为空！")
                return
            
            # 进入临摹模式
            self.editor.enter_imitation_mode(code)
            self.is_imitation_mode = True
            self.status_label.setText("临摹模式（从文件导入）")
            
        except Exception as e:
            QMessageBox.critical(self, "错误", f"无法读取文件: {str(e)}")
        
    def _start_imitation(self):
        """开始临摹模式"""
        if self.is_imitation_mode:
            QMessageBox.warning(self, "警告", "已经在临摹模式中！")
            return
            
        # 获取用户需求（使用自定义对话框）
        dialog = PromptInputDialog(self)
        result = dialog.exec()
        
        if result != QDialog.DialogCode.Accepted:
            return
            
        text = dialog.get_text()
        if not text.strip():
            return
            
        # 显示生成中提示
        self.status_label.setText("正在通过AI生成代码，请稍候...")
        QApplication.processEvents()
        
        # 创建进度对话框
        progress_dialog = QDialog(self)
        progress_dialog.setWindowTitle("正在生成代码")
        progress_dialog.setModal(True)
        progress_dialog.setFixedSize(300, 100)
        
        layout = QVBoxLayout(progress_dialog)
        layout.addWidget(QLabel("正在生成代码，这可能需要几秒钟..."))
        
        progress_bar = QProgressBar()
        progress_bar.setRange(0, 0)  # 无限滚动
        layout.addWidget(progress_bar)
        
        progress_dialog.show()
        QApplication.processEvents()
        
        # 创建并启动生成线程
        self.generation_thread = CodeGenerationThread(text.strip())
        self.generation_thread.generation_finished.connect(
            lambda code: self._on_code_generated(code, progress_dialog)
        )
        self.generation_thread.generation_error.connect(
            lambda error: self._on_generation_error(error, progress_dialog)
        )
        self.generation_thread.start()
        
    def _on_code_generated(self, code: str, progress_dialog):
        """代码生成完成"""
        progress_dialog.close()
        
        if code.startswith("# 错误") or code.startswith("# API"):
            QMessageBox.warning(self, "生成失败", 
                              f"代码生成失败：\n{code[:200]}...")
            self.status_label.setText("代码生成失败")
        else:
            # 进入临摹模式
            self.editor.enter_imitation_mode(code)
            self.is_imitation_mode = True
            self.status_label.setText("临摹模式已启动 - 请逐行输入代码")
            
            # 显示提示
            QMessageBox.information(self, "开始临摹", 
                                  "已进入临摹模式！\n\n"
                                  "操作说明：\n"
                                  "1. 灰色文字是AI生成的模板代码\n"
                                  "2. 请在当前行输入代码\n"
                                  "3. 输入正确后按回车进入下一行\n"
                                  "4. 输入错误时按两次回车可强制换行\n"
                                  "5. 错误代码会显示为红色")
            
    def _on_generation_error(self, error: str, progress_dialog):
        """代码生成错误"""
        progress_dialog.close()
        QMessageBox.critical(self, "生成错误", 
                           f"代码生成过程中发生错误：\n{error}")
        self.status_label.setText("代码生成错误")
        
    def _exit_imitation(self):
        """退出临摹模式"""
        if self.is_imitation_mode:
            reply = QMessageBox.question(
                self, "退出临摹", 
                "确定要退出临摹模式吗？\n所有待临摹代码将被清除。",
                QMessageBox.StandardButton.Yes | 
                QMessageBox.StandardButton.No
            )
            
            if reply == QMessageBox.StandardButton.Yes:
                self.editor.exit_imitation_mode()
                self.is_imitation_mode = False
                self.status_label.setText("已退出临摹模式")
                
    def _show_force_newline_warning(self, line: int, user_text: str, template_text: str):
        """显示强制换行警告"""
        # 在光标位置显示工具提示
        cursor = self.editor.textCursor()
        rect = self.editor.cursorRect(cursor)
        global_pos = self.editor.mapToGlobal(rect.bottomLeft())
        
        QToolTip.showText(
            global_pos,
            "⚠️ 与目标行不一致\n再次按下回车将强制换行（错误将标红）",
            self.editor,
            QRect(),
            2000
        )
        
    def _on_text_changed(self):
        """文本变化时的处理"""
        if not self.is_imitation_mode:
            # 更新状态栏显示修改状态
            if self.editor.document().isModified():
                filename = os.path.basename(self.current_file) if self.current_file else "未命名"
                self.status_label.setText(f"{filename} * (已修改)")
            else:
                filename = os.path.basename(self.current_file) if self.current_file else "未命名"
                self.status_label.setText(filename)
                
    def _on_imitation_completed(self, completed=False):
        """临摹完成时的处理"""
        self.is_imitation_mode = False
        self.status_label.setText("临摹完成！")
        
        # 只有完成所有代码时才显示恭喜信息
        if completed:
            QMessageBox.information(self, "完成", "恭喜！你已经完成了所有代码的临摹。")
        
    def closeEvent(self, event):
        """关闭事件"""
        if self._check_save():
            event.accept()
        else:
            event.ignore()


# ============================
# 6. 需求输入对话框（支持回车提交，Ctrl+回车换行）
# ============================
class PromptInputDialog(QDialog):
    """自定义输入对话框，支持回车提交和Ctrl+回车换行"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("输入需求")
        self.setFixedSize(500, 300)
        
        layout = QVBoxLayout(self)
        
        # 标签
        label = QLabel("请输入你想要生成的应用需求描述：")
        layout.addWidget(label)
        
        # 输入框
        self.text_edit = QTextEdit()
        self.text_edit.setPlaceholderText("（例如：用PyQt6创建一个窗口，包含一个按钮和一个标签）")
        self.text_edit.setFocus()
        layout.addWidget(self.text_edit)
        
        # 为输入框安装事件过滤器，捕获键盘事件
        self.text_edit.installEventFilter(self)
        
        # 提示标签
        hint_label = QLabel("提示：Enter 提交 | Ctrl+Enter 换行")
        hint_label.setStyleSheet("color: #888888; font-size: 12px;")
        layout.addWidget(hint_label)
        
        # 按钮
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | 
            QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        
        # 存储结果
        self.result_text = ""
        
    def eventFilter(self, obj, event):
        """事件过滤器，捕获输入框的键盘事件"""
        if obj == self.text_edit and event.type() == QEvent.Type.KeyPress:
            if event.key() == Qt.Key.Key_Return or event.key() == Qt.Key.Key_Enter:
                if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                    # Ctrl+Enter：手动插入换行符
                    cursor = self.text_edit.textCursor()
                    cursor.insertText("\n")
                    return True
                else:
                    # Enter：提交（拦截并调用accept）
                    self.accept()
                    return True
        return super().eventFilter(obj, event)
            
    def accept(self):
        """确认提交"""
        self.result_text = self.text_edit.toPlainText()
        super().accept()
        
    def get_text(self):
        """获取输入的文本"""
        return self.result_text

# ============================
# 7. 关于对话框
# ============================
class AboutDialog(QDialog):
    """关于对话框"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("关于Follow Me")
        self.setFixedSize(400, 300)
        
        layout = QVBoxLayout(self)
        
        # 标题
        title = QLabel("Follow Me")
        title.setStyleSheet("font-size: 20px; font-weight: bold;")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title)
        
        # 版本信息
        version = QLabel("版本 1.0.0")
        version.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(version)
        
        # 描述
        description = QLabel(
            "这是一个基于PyQt6开发的代码编辑器，具有AI辅助的代码临摹功能。\n\n"
            "主要功能：\n"
            "• 完整的代码编辑器功能\n"
            "• Python语法高亮\n"
            "• 文件保存和打开\n"
            "• AI代码生成\n"
            "• 代码临摹学习模式"
        )
        description.setWordWrap(True)
        layout.addWidget(description)
        
        # 按钮
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok)
        buttons.accepted.connect(self.accept)
        layout.addWidget(buttons)


# ============================
# 7. 应用程序主类
# ============================
class CodeImitationApp:
    """应用程序主类"""
    
    @staticmethod
    def run():
        """运行应用程序"""
        # 创建应用
        app = QApplication(sys.argv)
        app.setApplicationName("Follow Me")

        # 设置应用程序样式
        app.setStyle("Fusion")
        
        # 创建主窗口
        window = MainWindow()
        
        # 添加关于菜单
        help_menu = window.menuBar().addMenu("帮助")
        about_action = help_menu.addAction("关于")
        about_action.triggered.connect(lambda: AboutDialog(window).exec())
        
        # 显示窗口
        window.show()
        
        # 运行应用
        sys.exit(app.exec())


# ============================
# 8. 应用程序入口
# ============================
if __name__ == "__main__":
    # 检查必要的模块
    try:
        from PyQt6 import QtCore, QtWidgets, QtGui
    except ImportError as e:
        print(f"错误: 缺少必要的模块 - {e}")
        print("\n请安装以下模块:")
        print("1. PyQt6: pip install PyQt6")
        print("2. requests: pip install requests")
        sys.exit(1)
        
    # 运行应用程序
    print("正在启动Follow Me...")
    print("版本: 1.0.0")
    print("=" * 50)
    print("注意: 使用智谱AI API生成代码需要网络连接")

    CodeImitationApp.run()