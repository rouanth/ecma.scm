Require Import Coq.Strings.String.

Module Characters.
Require Import Ascii.
Open Scope string_scope.

Module Ascii.
Definition CharacterTabulation := "009"%char.
Definition Linefeed            := "010"%char.
Definition LineTabulation      := "011"%char.
Definition FormFeed            := "012"%char.
Definition CarriageReturn      := "013"%char.
Definition Space               := "020"%char.
End Ascii.

Module Unicode.
Definition NextLine           := (* U+0085 *)
    String "194"%char (
    String "133"%char EmptyString).
Definition LineSeparator      := (* U+2028 *)
    String "226"%char (
    String "128"%char (
    String "168"%char EmptyString)).
Definition ParagraphSeparator := (* U+2029 *)
    String "226"%char (
    String "128"%char (
    String "169"%char EmptyString)).
End Unicode.

End Characters.
