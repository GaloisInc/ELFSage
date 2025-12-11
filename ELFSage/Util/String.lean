import ELFSage.Util.List

namespace String

/-- Pad `s : String` with repeated occurrences of `c : Char` until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def leftpad (n : Nat) (c : Char) (s : String) : String :=
  String.ofList (List.leftpad n c s.toList)

end String
