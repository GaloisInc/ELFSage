import Std.Tactic.BVDecide

def ByteArray.getUInt64BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 8) : UInt64 :=
  bs[offset + 0].toUInt64 <<< 0x38 |||
  bs[offset + 1].toUInt64 <<< 0x30 |||
  bs[offset + 2].toUInt64 <<< 0x28 |||
  bs[offset + 3].toUInt64 <<< 0x20 |||
  bs[offset + 4].toUInt64 <<< 0x18 |||
  bs[offset + 5].toUInt64 <<< 0x10 |||
  bs[offset + 6].toUInt64 <<< 0x08 |||
  bs[offset + 7].toUInt64


def UInt64.getBytesBEfrom (i : UInt64) : ByteArray :=
  ⟨#[ (i >>> 0x38).toUInt8
    , (i >>> 0x30).toUInt8
    , (i >>> 0x28).toUInt8
    , (i >>> 0x20).toUInt8
    , (i >>> 0x18).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

def ByteArray.getUInt32BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 4) : UInt32 :=
  bs[offset + 0].toUInt32 <<< 0x18 |||
  bs[offset + 1].toUInt32 <<< 0x10 |||
  bs[offset + 2].toUInt32 <<< 0x08 |||
  bs[offset + 3].toUInt32

def UInt32.getBytesBEfrom (i : UInt32) : ByteArray :=
  ⟨#[ (i >>> 0x18).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

def ByteArray.getUInt16BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 2) : UInt16 :=
  bs[offset + 0].toUInt16 <<< 0x08 |||
  bs[offset + 1].toUInt16

def UInt16.getBytesBEfrom (i : UInt16) : ByteArray :=
  ⟨#[ (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

--LittleEndian

def ByteArray.getUInt64LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 8) : UInt64 :=
  bs[offset + 7].toUInt64 <<< 0x38 |||
  bs[offset + 6].toUInt64 <<< 0x30 |||
  bs[offset + 5].toUInt64 <<< 0x28 |||
  bs[offset + 4].toUInt64 <<< 0x20 |||
  bs[offset + 3].toUInt64 <<< 0x18 |||
  bs[offset + 2].toUInt64 <<< 0x10 |||
  bs[offset + 1].toUInt64 <<< 0x08 |||
  bs[offset + 0].toUInt64

def UInt64.getBytesLEfrom (i : UInt64) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x18).toUInt8
    , (i >>> 0x20).toUInt8
    , (i >>> 0x28).toUInt8
    , (i >>> 0x30).toUInt8
    , (i >>> 0x38).toUInt8
    ]⟩

def ByteArray.getUInt32LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 4) : UInt32 :=
  bs[offset + 3].toUInt32 <<< 0x18 |||
  bs[offset + 2].toUInt32 <<< 0x10 |||
  bs[offset + 1].toUInt32 <<< 0x08 |||
  bs[offset + 0].toUInt32

def UInt32.getBytesLEfrom (i : UInt32) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x18).toUInt8
    ]⟩

def ByteArray.getUInt16LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 2) : UInt16 :=
  bs[offset + 1].toUInt16 <<< 0x08 |||
  bs[offset + 0].toUInt16

def UInt16.getBytesLEfrom (i : UInt16) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    ]⟩

/- An alternative approach is to define a byte parsing monad, à la:

https://github.com/risc0/risc0-lean4/blob/31c956fc9246bbfc84359021d66ed94972afd86b/R0sy/ByteDeserial.lean

And just have some runtime error possibilities, rather than proof obligations.
-/

def ByteArray.getEntriesFrom
  (bs : ByteArray)
  (offset : Nat)
  (num : Nat)
  (entsize : Nat)
  (entreq : Nat)
  (suffSize : entsize ≥ entreq)
  (spaceAvail : bs.size ≥ offset + num * entsize)
  (toEnt :  (offset₂ : Nat) → (bs.size - offset₂ ≥ entreq) → α)
  : List α := recur num [] (by omega)
  where recur (idx : Nat) acc (h₁ : idx ≤ num) : List α
  := match idx with
    | 0 => acc
    | i + 1 =>
      let ent := toEnt (offset + (i * entsize)) $ by
        have h₂ : num * entsize ≥ i * entsize + entsize := by
          conv => rhs; rw [Nat.mul_comm]
          rw [←Nat.mul_succ]
          conv => rhs; rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right entsize h₁
        omega
      recur i (ent :: acc) (by omega)

structure NByteArray (n : Nat) where
  bytes: ByteArray
  sized: bytes.size = n

def NByteArray.get {n : Nat} (bs : NByteArray n) (m: Nat) (p: m < n) :=
  have size := bs.sized
  bs.bytes[m]

instance : Repr (NByteArray n) where
  reprPrec nbs := reprPrec $ nbs.bytes.toList.map λbyte ↦
    Nat.toDigits 16 byte.toNat
    |> (λl ↦ if l.length == 1 then '0' :: l else l)
    |> String.ofList

instance : Repr ByteArray where
  reprPrec nbs := reprPrec $ nbs.data.toList.map λbyte ↦
    Nat.toDigits 16 byte.toNat
    |> (λl ↦ if l.length == 1 then '0' :: l else l)
    |> String.ofList

/-

 These are some simple theorems related to Arrays and ByteArrays. They start
 from the function Array.extract.loop, associated with Array.extract:

 https://github.com/leanprover/lean4/blob/6fce8f7d5cd18a4419bca7fd51780c71c9b1cc5a/src/Init/Prelude.lean#L2722

 `Array.extract.loop src i j dst` essentially returns dst if i is 0 or
 j ≥ src.size, and otherwise calls itself as `Array.extract.loop src (i - 1) (j
 + 1) (dst ++ src[j])`.

 Some things it would be nice to prove, since it would give us an instance of

 https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#AddCancelMonoid

 ∀{a b: ByteArray}, (a ++ b).size = a.size + b.size
 ∀{a b c: ByteArray}, a ++ b = c ++ b ↔ a = c
 ∀{a b c: ByteArray}, a ++ b = a ++ c ↔ b = c
 ∀{a b c: ByteArray}, (a ++ b) ++ c = a ++ (b ++ c)
 ∀{a: ByteArray}, a ++ ByteArray.empty = a
 ∀{a: ByteArray}, ByteArray.empty ++ a = a

 It would also be good to improve NByteArray extract to take an offset in addition to a length

-/

theorem Array.extract_len_aux {src: Array α} :
   ∀b l dst, (b + l ≤ src.size) →
   List.length (Array.extract.loop src b l dst).toList = b + dst.size:= by
   intro b
   induction b
   case zero => simp [Array.extract.loop]
   case succ n ih =>
     intro l dst
     unfold Array.extract.loop
     intro lt
     simp; split
     · have : n + l + 1 ≤ size src := by omega
       simp only [length_toList] at ih
       rw [ih (l + 1) (push dst src[l]) this]
       simp +arith
     · omega

theorem Array.extract_loop_len {src : Array α} :
  ∀ b l dst,
   (b + l ≤ src.size) →
   (Array.extract.loop src b l dst).size = b + dst.size:= by
  intro i s e h
  rw [Array.size]
  apply Array.extract_len_aux _ _ _ h

def NByteArray.extract (bs : ByteArray) (n : Nat) (h : bs.size ≥ n) : NByteArray n :=
  let bytes := bs.extract 0 n
  let proof : bytes.size = n := by
      simp [bytes]
      rw [Nat.min_eq_left]
      trivial
  ⟨bytes, proof⟩

theorem UInt16.ByteArray_size : ∀ i : UInt16, i.getBytesBEfrom.size = 2 := by
  intro i
  rcases 4 <;>
  simp [UInt16.getBytesBEfrom, ByteArray.size]

theorem UInt8_to_UInt16_round {i : UInt8} : i.toUInt16.toUInt8 = i := UInt8.toUInt8_toUInt16 i

theorem UInt16_to_UInt8_round: ∀{i : UInt16}, i.toUInt8.toUInt16 = i % 256:= rfl

theorem Nat.bitwise_sum : ∀{n m k : Nat}, m % 2^n = 0 → k < 2^n → m ||| k = m + k := by
  intro n m k eq lt
  have : 2^n * (m / 2^n) = m := by
    apply Nat.mul_div_cancel'
    exact Nat.dvd_of_mod_eq_zero eq
  rw [←this]
  rw [Nat.two_pow_add_eq_or_of_lt]
  assumption

/--
  OK, so the idea for doing these proofs more systematically would be to prove that

  i = ((i >>> 0x8) <<< 0x8 ) ||| i % 256

  for nat, then use this repeatedly (substituting for i >>> 0x8, i >>> 0x10) to get something like

  i = (((((i >>> 0x8) >>> 0x8) <<< 0x8 ) ||| (i >>> 0x8) % 256) <<< 0x8) ||| i % 256
    = (((i >>> 0x10) <<< 0x8 ) ||| (i >>> 0x8) % 256) <<< 0x8 ||| i % 256             --consolidate
    = (((i >>> 0x10) <<< 0x8 ) << 0x8) ||| ((i >>> 0x8) % 256) <<< 0x8 ||| i % 256    --distribute
    = (((i >>> 0x10) <<< 0x10) ||| ((i >>> 0x8) % 256) <<< 0x8 ||| i % 256            --consolidate
    ... and so on

  and then use these to prove the corresponding UInt facts

-/

theorem UInt16.nullShift : ∀{i : UInt16}, i >>> 0 = i := rfl

@[simp]
theorem Nat.bitwise_zero_left : bitwise f 0 m = if f false true then m else 0 := by
  simp only [bitwise, ↓reduceIte]

@[simp]
theorem Nat.bitwise_zero_right : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split <;> rfl

theorem Nat.shiftLeft_toExp : x <<< n = 2^n * x := by
  rw [Nat.mul_comm]; apply Nat.shiftLeft_eq

theorem Nat.shiftRight_toDiv : x >>> n = x / 2^n := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [Nat.pow_succ 2 n, Nat.shiftRight_succ, ih]
    rw [Nat.div_div_eq_div_mul]

theorem Nat.shiftRightLeft_leq : ∀n : Nat, (x >>> n) <<< n ≤ x := by
  intro n
  rw [Nat.shiftRight_toDiv, Nat.shiftLeft_toExp]
  apply Nat.mul_div_le

private theorem Nat.bitwise_dist_lem : f false false = false → 2 * Nat.bitwise f m n = Nat.bitwise f (2 * m) (2 * n) := by
  intro hyp
  unfold bitwise; split <;> split <;> try split <;> try split <;> try split
  all_goals try simp_all
  all_goals try omega
  (conv => rhs; unfold bitwise)
  simp_all only [ite_false]
  apply Nat.two_mul

theorem Nat.mod_pow_zero : n % m^(succ k) = 0 → n % m = 0 := by
  intro hyp
  rw [Nat.pow_succ] at hyp
  have : n % (m ^ k * m) % m = 0 % m := by rw [hyp]
  simp [Nat.mod_mul_left_mod n (m^k) m] at this
  assumption

theorem Nat.zero_lt_pow : 0 < n → 0 < n^m := by
  intro hyp; induction m
  case zero => simp
  case succ m ih =>
    simp [Nat.pow_succ]
    have := (Nat.mul_lt_mul_right hyp).mpr ih
    simp at this
    assumption

theorem Nat.mod_pow_lt_inner : ∀{l m n k : Nat}, l ≤ m → n % k^m % k^l = n % k^l := by
  intro l m n k hyp; apply Nat.mod_mod_of_dvd; apply Nat.pow_dvd_pow; assumption

theorem Nat.mod_pow_lt_outer : ∀{l m n k : Nat}, 1 < k → l ≤ m → n % k^l % k^m = n % k^l := by
  intro l m n k hyp₁ hyp₂
  cases Nat.le_iff_lt_or_eq.mp hyp₂
  case inl hyp₂ =>
    apply Nat.mod_eq_of_lt
    apply Nat.lt_trans (m := k ^ l)
    · apply Nat.mod_lt; apply Nat.zero_lt_pow; omega
    · apply Nat.pow_lt_pow_of_lt hyp₁; assumption
  case inr hyp₂ => rw [hyp₂, Nat.mod_mod]

theorem Nat.shiftLeft_mod : w + m ≥ k → (n % 2^w) <<< m % 2^k = n <<< m % 2^k := by
  simp_all [Nat.shiftLeft_toExp]
  revert m
  induction k <;> intro m
  case zero => simp [Nat.mod_one]
  case succ k ih_k =>
    intro hyp
    cases m
    case zero => simp_all; exact Nat.mod_pow_lt_inner hyp
    case succ m =>
      simp [Nat.pow_succ]
      suffices 2 * 2 ^ m  * (n % 2 ^ w) % (2 * 2 ^ k) = 2 * 2 ^ m * n % (2 * 2 ^ k) by
        simp_all [Nat.mul_comm]
      suffices 2 * (2 ^ m  * (n % 2 ^ w)) % (2 * 2 ^ k) = 2 * (2 ^ m * n) % (2 * 2 ^ k) by
        simp_all [Nat.mul_assoc]
      simp [Nat.mul_mod_mul_left]
      rw [ih_k]
      simp +arith at hyp
      assumption

--TODO: this should generalize to arbitrary bitwise ops.
theorem Nat.bitwise_mod : Nat.bitwise or m n % 2^k = Nat.bitwise or (m % 2^k) (n % 2^k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_mod_two_pow]
  have h_m := @Nat.mod_lt m (2^k) (by exact Nat.two_pow_pos k)
  have h_n := @Nat.mod_lt n (2^k) (by exact Nat.two_pow_pos k)
  by_cases h : i < k
  case pos =>
    simp only [h, decide_true, Bool.true_and]
    rw [@testBit_bitwise or (by simp only [Bool.or_self]) (m % 2^k) (n % 2^k) i]
    rw [@testBit_bitwise or (by simp only [Bool.or_self]) m n i]
    simp only [testBit_mod_two_pow, h, decide_true, Bool.true_and]
  case neg =>
    simp only [h, decide_false, Bool.false_and, Bool.false_eq]
    have h_k_i : 2^k <= 2^i := by
      apply Nat.pow_le_pow_of_le (by omega) (by omega)
    generalize h_x : (bitwise or (m % 2 ^ k) (n % 2 ^ k)) = x
    have h_lt := @bitwise_lt_two_pow (m % 2^k) k (n % 2^k) or h_m h_n
    apply testBit_lt_two_pow (by omega)

theorem Nat.bitwise_or_mod : (m ||| n) % 2^k = m % 2^k ||| n % 2^k := by
  simp [HOr.hOr]; apply Nat.bitwise_mod

theorem Nat.bitwise_dist : f false false = false → 2^k * Nat.bitwise f m n = Nat.bitwise f (2^k * m) (2^k * n) := by
  induction k
  case zero => simp
  case succ k ih =>
    intro hyp
    simp [Nat.pow_succ, show 2^k * 2 = 2 * 2^k by apply Nat.mul_comm, Nat.mul_assoc]
    conv => rhs; rw [←Nat.bitwise_dist_lem hyp]
    rw [ih hyp]

theorem Nat.or_mul_dist : 2^k * (x ||| y) = 2^k * x ||| 2^k * y := by
  simp [HOr.hOr]; apply Nat.bitwise_dist; simp

theorem Nat.and_mul_dist : 2^k * (x &&& y) = 2^k * x &&& 2^k * y := by
  simp [HAnd.hAnd]; apply Nat.bitwise_dist; simp

theorem Nat.and_xor_dist : 2^k * (x ^^^ y) = 2^k * x ^^^ 2^k * y := by
  simp [HXor.hXor]; apply Nat.bitwise_dist; simp

theorem Nat.shiftLeft_distribute : ∀n : Nat, (x ||| y) <<< n = (x <<< n) ||| (y <<< n) := by
  intro n; simp [Nat.shiftLeft_toExp, Nat.or_mul_dist]

@[simp]
theorem UInt16.byteCeiling :  ∀(i  : UInt16), (i >>> 0x8) % (256 : UInt16) = i >>> 0x8 := by
  bv_decide

theorem Nat.splitBytes : ∀n: Nat, n = n >>> 0x8 <<< 0x8 ||| n % 256 := by
  intro n
  suffices 256 * (n / 256) ||| n % 256 = 256 * (n / 256) + n % 256 by
    simp [Nat.shiftLeft_toExp, Nat.shiftRight_toDiv]
    rw [this, Nat.add_comm, Nat.mod_add_div]
  apply Nat.bitwise_sum (n:=8)
  · rw [Nat.mul_comm]; apply Nat.mul_mod_left
  · apply Nat.mod_lt; trivial

theorem UInt16.shiftUnshift : ∀(i  : UInt16), i = (i >>> 0x8 % 256) <<< 0x8 ||| i % 256 := by
  bv_decide

theorem UInt32.shiftUnshift : ∀(i  : UInt32),
  i = (i >>> 0x18 % 256) <<< 0x18 |||
      (i >>> 0x10 % 256) <<< 0x10 |||
      (i >>> 0x08 % 256) <<< 0x08 |||
      i % 256 := by
  bv_decide

theorem UInt64.shiftUnshift : ∀(i  : UInt64),
  i = (i >>> 0x38 % 256) <<< 0x38 |||
      (i >>> 0x30 % 256) <<< 0x30 |||
      (i >>> 0x28 % 256) <<< 0x28 |||
      (i >>> 0x20 % 256) <<< 0x20 |||
      (i >>> 0x18 % 256) <<< 0x18 |||
      (i >>> 0x10 % 256) <<< 0x10 |||
      (i >>> 0x08 % 256) <<< 0x08 |||
      i % 256 := by
  bv_decide

theorem UInt16.ByteArray_roundtrip :
  ∀ i : UInt16, ∀l, i.getBytesBEfrom.getUInt16BEfrom 0 l = i := by
  intro i l

  simp [
    UInt16.getBytesBEfrom,
    ByteArray.getUInt16BEfrom,
  ]

  apply Eq.symm
  apply UInt16.shiftUnshift i
