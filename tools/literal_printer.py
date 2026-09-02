import gdb


class LiteralPrinter:
    def __init__(self, val):
        self.val = val

    def to_string(self):
        rep = int(self.val["rep_"])

        try:
            sign_mask = int(gdb.parse_and_eval("Literal::sign_mask"))
            flag_mask = int(gdb.parse_and_eval("Literal::flag_mask"))
        except gdb.error:
            sign_mask = 2
            flag_mask = 1

        var = rep >> sign_mask
        sign = (rep & sign_mask) != 0
        int_val = -var if sign else var
        str_val = ""
        if var == 0:
            str_val = "T" if not sign else "F"
        flagged = (rep & flag_mask) != 0
        f = "*" if flagged else ""
        return f"{int_val}{f}" if int_val != 0 else f"{str_val}{f}"


def literal_lookup(val):
    # Strip references/typedefs, handle the Literal type
    t = val.type.strip_typedefs()
    if t.code == gdb.TYPE_CODE_REF:
        t = t.target().strip_typedefs()
    if t.tag == "Clasp::Literal":
        return LiteralPrinter(val)
    return None


gdb.pretty_printers.append(literal_lookup)
