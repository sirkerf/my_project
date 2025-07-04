universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}


-- 基本的な集合定義
-- Lean4 の core における集合定義
def Set (α : Type _) := α → Prop

namespace Set
  -- 空集合
  def empty : Set α := fun _ => False
  notation "∅" => empty

  -- 合併
  def union (s t : Set α) : Set α := fun a => s a ∨ t a
  infix:65 " ∪ " => union

  -- 交差
  def inter (s t : Set α) : Set α := fun a => s a ∧ t a
  infix:70 " ∩ " => inter

  -- 包含
  def subset (s t : Set α) : Prop := ∀ a, s a → t a
  infix:50 " ⊆ " => subset

  -- 写像の像
  def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, s a ∧ f a = b
  notation f " '' " s => image f s

  -- 写像の原像
  def preimage (f : α → β) (s : Set β) : Set α := fun a => s (f a)
  notation f " ⁻¹' " s => preimage f s
end Set

open Set

-- 基本的な命題証明

-- 空集合の像
theorem image_empty (f : α → β) : f '' ∅ = (∅ : Set β) := by
  funext b; apply Iff.intro
  · intro h; cases h with | intro a ha => cases ha.left
  · intro h; cases h

-- 空集合の原像
theorem preimage_empty (f : α → β) : f ⁻¹' (∅ : Set β) = (∅ : Set α) := by
  funext a; apply Iff.intro
  · intro h; exact h.elim
  · intro h; cases h

-- 合併の像
theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by
  funext b; apply Iff.intro
  · intro h; cases h with | intro a ha =>
      cases ha.left with
      | inl hs => apply Or.inl; exact ⟨a, hs, ha.right⟩
      | inr ht => apply Or.inr; exact ⟨a, ht, ha.right⟩
  · intro h; cases h with
      | inl ⟨a, hs, rfl⟩ => exact ⟨a, Or.inl hs, rfl⟩
      | inr ⟨a, ht, rfl⟩ => exact ⟨a, Or.inr ht, rfl⟩

-- 合併の原像
theorem preimage_union (f : α → β) (s t : Set β) : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := by
  funext a; apply Iff.intro
  · intro h; cases h with
    | inl hs => apply Or.inl; exact hs
    | inr ht => apply Or.inr; exact ht
  · intro h; cases h with
    | inl hs => exact hs
    | inr ht => exact ht

-- 交差の像（写像が単射の場合）
theorem image_inter_of_injective {f : α → β} (hf : Function.Injective f) (s t : Set α) :
  f '' (s ∩ t) = f '' s ∩ f '' t := by
  funext b; apply Iff.intro
  · intro h; cases h with | intro a ha =>
      let ⟨hst, hrt⟩ := ha.left
      have rfl_eq : f a = b := ha.right
      constructor
      · exists a; exact ⟨hst, rfl_eq⟩
      · exists a; exact ⟨hrt, rfl_eq⟩
  · intro h; cases h with | intro ha hb =>
      cases ha with | intro a ha' =>
      cases hb with | intro b hb' =>
      have h_eq : a = b := hf (ha'.right.trans hb'.right.symm)
      subst h_eq
      exists a
      constructor
      · exact And.intro ha'.left hb'.left
      · exact ha'.right

-- 交差の原像
theorem preimage_inter (f : α → β) (s t : Set β) : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  funext a; apply Iff.intro
  · intro h; constructor; exact h.left; exact h.right
  · intro h; cases h; constructor; assumption; assumption

-- 像の単調性
theorem image_subset {f : α → β} {s t : Set α} (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro b; intro h'; cases h' with | intro a ha =>
    exists a
    constructor
    · apply h; exact ha.left
    · exact ha.right

-- 原像の単調性
theorem preimage_subset {f : α → β} {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := by
  intro a; intro hs; apply h; exact hs

-- 合成写像の像
theorem image_comp (g : β → γ) (f : α → β) (s : Set α) :
  (g ∘ f) '' s = g '' (f '' s) := by
  funext c; apply Iff.intro
  · intro h; cases h with | intro a ha =>
      cases ha with | intro s_mem rfl =>
        exists (f a)
        constructor
        · exists a; exact ⟨s_mem, rfl⟩
        · rfl
  · intro h; cases h with | intro b hb =>
      cases hb with | intro a ha =>
        cases ha with | intro s_mem rfl =>
          exists a
          constructor; exact s_mem; rfl
