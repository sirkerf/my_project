/-
Lean4: Peano System including non-dependent and dependent implementations
-/

-- 非依存型の実装
inductive Peano : Type where
  | zero : Peano            -- 0
  | succ (n : Peano) : Peano  -- 後者関数

namespace Peano

/-- 加算 --/
def add : Peano → Peano → Peano
  | a, zero   => a
  | a, succ b => succ (add a b)

/-- 乗算 --/
def mul : Peano → Peano → Peano
  | _, zero   => zero
  | a, succ b => add (mul a b) a

/-- Peano → Nat 変換 --/
def toNat : Peano → Nat
  | zero    => 0
  | succ n  => toNat n + 1

/-- Nat → Peano 変換 --/
def ofNat : Nat → Peano
  | 0      => zero
  | n + 1  => succ (ofNat n)

@[simp] theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  induction n with
  | zero   => rfl
  | succ k ih => simp [toNat, ofNat, ih]

instance : Repr Peano where
  reprPrec
    | zero, _   => "zero"
    | succ n, _ => "succ (" ++ reprPrec n 0 ++ ")"

instance : Inhabited Peano where
  default := zero

end Peano

-- 依存型を用いた実装
inductive DPeano : Nat → Type where
  | zero : DPeano 0
  | succ {n : Nat} (k : DPeano n) : DPeano (n + 1)

namespace DPeano

/-- 依存型版の加算: 結果の型が (m + n) に依存 --/
def add {m n : Nat} : DPeano m → DPeano n → DPeano (m + n)
  | x, zero    => x
  | x, succ y  => succ (add x y)

/-- 依存型版の乗算: 結果の型が (m * n) に依存 --/
def mul {m n : Nat} : DPeano m → DPeano n → DPeano (m * n)
  | _, zero    => zero
  | x, succ y  => add (mul x y) x

/-- 型引数をそのまま返す toNat --/
def toNat {n : Nat} (_ : DPeano n) : Nat := n

/-- Nat → DPeano 変換 --/
def ofNat : (k : Nat) → DPeano k
  | 0     => zero
  | k + 1 => succ (ofNat k)

@[simp] theorem toNat_ofNat (k : Nat) : toNat (ofNat k) = k := by rfl

end DPeano
