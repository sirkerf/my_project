universe u

namespace sirkerf

variable {X Y : Type u}

def inj (f : X → Y) : Prop :=
∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂

def surj (f : X → Y ) : Prop :=
∀ y : Y, ∃ x : X, f x = y

example : inj (λ n : Nat => n + 1) := by
  intros x₁ x₂ h
  apply Nat.succ.inj
  exact h

variable {Z : Type u} {f : X → Y} {g : Y → Z}

theorem inj_of_comp_inj : inj (g ∘ f) → inj f :=
  fun h_inj_comp =>
    fun x₁ x₂ hfx =>
      h_inj_comp x₁ x₂ (congrArg g hfx)

theorem surj_of_comp_surj : surj (g ∘ f) → surj g :=
  fun h_surj_comp y =>
    let ⟨x, hx⟩ := h_surj_comp y
    ⟨f x, hx⟩

def mono (f : X → Y) : Prop := ∀ {A : Type u},
∀ {g₁ g₂ : A → X}, f ∘ g₁ = f ∘ g₂ → g₁ = g₂

def epi (f : X → Y) : Prop := ∀ {A : Type u},
∀ {g₁ g₂ : Y → A}, g₁ ∘ f = g₂ ∘ f  → g₁ = g₂

theorem inj_iff_mono : inj f ↔ mono f :=
by
  constructor
  case mp =>
    intro hinj
    intros A g₁ g₂ hfg
    ext1 a
    apply hinj
    change (f ∘ g₁) a = (f ∘ g₂) a
    rw [hfg]
  case mpr =>
    intro hmono
    intros x₁ x₂ hfx
    let g₁ : X → X := λ _ => x₁
    let g₂ : X → X := λ _ => x₂
    have : f ∘ g₁ = f ∘ g₂ := by ext1; simpa
    have hg := hmono this
    have eq_g₁_g₂ : g₁ = g₂ := hg
    exact congr_arg (fun g => g rfl) eq_g₁_g₂
inductive doubleton : Type u
| fst : doubleton
| snd : doubleton

open doubleton
open classical
local attribute [instance] prop_decidable

theorem surj_iff_epi : surj f ↔ epi f :=
begin
theorem surj_iff_epi : surj f ↔ epi f :=
by
  split
  case mp =>
    intro hsurj
    rw epi
    intros A g₁ g₂ hgf
    ext1 y
    obtain ⟨x, rfl⟩ := hsurj y
    change (g₁ ∘ f) x = (g₂ ∘ f) x
    rw hgf
  case mpr =>
    intro hepi
    rw epi at hepi
    set g₁ : Y → doubleton := λ _, fst with hg₁
    set g₂ : Y → doubleton := λ y, if (∃ x : X, f x = y) then fst else snd with hg₂
    have hg : g₂ ∘ f = g₁ ∘ f := by ext1 x; simp [hg₂]
    replace hg := hepi hg
    intro y
    have := congr_fun hg y
    simp only [ite_eq_left_iff] at this
    by_contra
    exact this h
