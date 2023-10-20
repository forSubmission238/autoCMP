"""Utility functions."""

def indent(s, num_space, first_line=None):
    """Indent the given string by adding spaces to each line.
    
    Parameters
    ----------
    num_space : int
        Number of spaces to add to each line
    first_line : int, optional
        Number of spaces to add to first line
    """
    if s is None:
        return ""
    lines = s.split('\n')
    if first_line is None:
        return '\n'.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += '\n' + '\n'.join(' ' * num_space + line for line in lines[1:])
        return res
