import Std.Data.Set.Lemmas

universe u
namespace Topology

variable {α : Type u}

-- 位相空間の構造
structure TopologicalSpace where
  isOpen          : Set α → Prop
  isOpen_empty    : isOpen ∅
  isOpen_univ     : isOpen Set.univ
  isOpen_inter    : ∀ ⦃s t⦄, isOpen s → isOpen t → isOpen (s ∩ t)
  isOpen_sUnion   : ∀ ⦃S : Set (Set α)⦄, (∀ s ∈ S, isOpen s) → isOpen (⋃₀ S)

attribute [class] TopologicalSpace

-- デフォルトの位相空間を仮定
variable [T : TopologicalSpace α]
include T

/-- 開集合であることを表す述語 -/
def IsOpen (U : Set α) : Prop := T.isOpen U

/-- ∅ は開集合 -/
@[simp] lemma isOpen_empty : IsOpen (∅ : Set α) :=
  T.isOpen_empty

/-- 全体集合は開集合 -/
@[simp] lemma isOpen_univ : IsOpen (Set.univ : Set α) :=
  T.isOpen_univ

/-- ２つの開集合の交叉は開 -/
lemma isOpen_inter {U V : Set α} (h₁ : IsOpen U) (h₂ : IsOpen V) :
  IsOpen (U ∩ V) :=
  T.isOpen_inter h₁ h₂

/-- ２つの開集合の和集合は開 -
  (sUnion を使って {U, V} の和集合として扱う) -/
lemma isOpen_union {U V : Set α} (hU : IsOpen U) (hV : IsOpen V) :
  IsOpen (U ∪ V) := by
  let S : Set (Set α) := {U, V}
  have hS : ∀ s ∈ S, IsOpen s := by
    intros s hs; cases hs <;> assumption
  show IsOpen (⋃₀ S); from T.isOpen_sUnion hS

/-- 任意個の開集合の和集合は開 -/
lemma isOpen_Union {ι : Type u} {f : ι → Set α}
  (h : ∀ i, IsOpen (f i)) :
  IsOpen (⋃ i, f i) := by
  -- ⋃ i, f i = sUnion (range f)
  let S : Set (Set α) := Set.range f
  have hS : ∀ s ∈ S, IsOpen s := by
    rintro _ ⟨i, rfl⟩; apply h
  show IsOpen (⋃₀ S); from T.isOpen_sUnion hS

end Topology
