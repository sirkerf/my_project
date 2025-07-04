namespace BasicSet

variable {α β : Type}

/- Define a set as a predicate -/
def Set (α : Type) := α → Prop

/- Membership relation -/
instance : Membership α (Set α) where
  mem s a := s a

/- Empty and Universal sets -/
def emptySet : Set α := fun _ => False
def universalSet : Set α := fun _ => True

/- Subset relation -/
def subset (A B : Set α) : Prop := ∀ a, a ∈ A → a ∈ B
infix:50 " ⊆ " => subset

/- Union, Intersection, Complement -/
def Union (A B : Set α) : Set α := fun a => a ∈ A ∨ a ∈ B
infix:65 " ∪ " => Union

def Inter (A B : Set α) : Set α := fun a => a ∈ A ∧ a ∈ B
infix:70 " ∩ " => Inter

def Compl (A : Set α) : Set α := fun a => ¬ a ∈ A
postfix:75 "ᶜ" => Compl

/- Basic subset properties -/
theorem subset_refl (A : Set α) : A ⊆ A := by
  intro a ha;
  exact ha

theorem subset_trans {A B C : Set α} : (A ⊆ B) → (B ⊆ C) → (A ⊆ C) := by
  intros hAB hBC a ha;
  apply hBC;
  apply hAB;
  exact ha

/- Unions and subsets -/
theorem subset_union_left (A B : Set α) : A ⊆ A ∪ B := by
  intro a ha;
  apply Or.inl;
  exact ha

theorem subset_union_right (A B : Set α) : B ⊆ A ∪ B := by
  intro a ha;
  apply Or.inr;
  exact ha

theorem union_subset {A B C : Set α} : (A ⊆ C) → (B ⊆ C) → (A ∪ B ⊆ C) := by
  intros hAC hBC a ha; cases ha with
  | inl h => apply hAC; exact h
  | inr h => apply hBC; exact h

/- Define image and preimage of functions -/
def image (f : α → β) (A : Set α) : Set β := fun b => ∃ a, a ∈ A ∧ f a = b
def preimage (f : α → β) (B : Set β) : Set α := fun a => f a ∈ B

/- Membership lemmas -/
theorem mem_image {f : α → β} {A : Set α} {b : β} :
  b ∈ image f A ↔ ∃ a, a ∈ A ∧ f a = b := by rfl

theorem mem_preimage {f : α → β} {B : Set β} {a : α} :
  a ∈ preimage f B ↔ f a ∈ B := by rfl

/- Image of union -/
theorem image_union (f : α → β) (A B : Set α) :
  image f (A ∪ B) = image f A ∪ image f B := by
  funext b; apply propext
  apply Iff.intro
  · intro ⟨a, ha, eq⟩; cases ha with
    | inl h => apply Or.inl; exact ⟨a, h, eq⟩
    | inr h => apply Or.inr; exact ⟨a, h, eq⟩
  · intro h; cases h with
    | inl h' =>
      let ⟨a, h, eq⟩ := h'
      exact ⟨a, Or.inl h, eq⟩
    | inr h' =>
      let ⟨a, h, eq⟩ := h'
      exact ⟨a, Or.inr h, eq⟩

/- Preimage of union -/
theorem preimage_union (f : α → β) (C D : Set β) :
  preimage f (C ∪ D) = preimage f C ∪ preimage f D := by
  funext a; apply propext
  apply Iff.intro
  · intro h
    cases h with
    | inl h1 => apply Or.inl; exact h1
    | inr h2 => apply Or.inr; exact h2
  · intro h
    cases h with
    | inl h1 => apply Or.inl; exact h1
    | inr h2 => apply Or.inr; exact h2

end BasicSet
