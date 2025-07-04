import tactic
import algebra.category.Group.basic
import category_theory.adjunction.basic

universe u
local notation `Set` := Type u
local notation `Group` := Group.{u}

open category_theory

namespace Group.free

variables (α : Set)

inductive gen
| of : α → gen
| mul : gen → gen → gen
| one : gen
| inv : gen → gen

inductive nat
| zero : nat
| succ : nat → nat

instance : has_mul (gen α) := ⟨gen.mul⟩
instance : has_one (gen α) := ⟨gen.one⟩ 
instance : has_inv (gen α) := ⟨gen.inv⟩

inductive rel {α} : gen α → gen α → Prop  
| assoc (a b c) : rel ((a * b) * c) (a * (b * c))
| left_one (a) : rel (1 * a) a
| right_one (a) : rel (a * 1) a
| left_inv (a) : rel (a⁻¹ * a) 1
| right_inv (a) : rel (a * a⁻¹) 1
| mul_congr_left (a₁ a₂ b) :
    rel a₁ a₂ → rel (a₁ * b) (a₂ * b)
| mul_congr_right (a b₁ b₂) :
    rel b₁ b₂ → rel (a * b₁) (a * b₂)
| inv_congr (a b) :
    rel a b → rel a⁻¹ b⁻¹

local infixl ` ∼ `:40 := rel
local notation `〚`:max a `〛` := quot.mk _ a

def free_group := @Group.of (quot (@rel α))
{ 
  mul := quot.map₂ gen.mul
    rel.mul_congr_right rel.mul_congr_left,
  mul_assoc := by
  { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, 
    apply quot.sound,
    exact rel.assoc a b c, },
  one := quot.mk _ gen.one,
  one_mul := by
  { rintros ⟨a⟩, 
    apply quot.sound,
    exact rel.left_one a,
  }
  mul_one := by
  { rintros ⟨a⟩, 
    apply quot.sound,
    exact rel.right_one a},
  inv := quot.map gen.inv rel.inv_congr,
  mul_left_inv := by
  { rintros ⟨a⟩,
    apply quot.sound,
    exact rel.left_inv a,  
  }

variables {α} {G : Group} (f : α ⟶ G )

def gen.lift : gen α ⟶ G
| (gen.of a) := f a
| (gen.mul a b) := (gen.lift a) * (gen.lift b)
| (gen.one) := 1
| (gen.inv a) := (gen.lift a)⁻¹

def lift : free_group α ⟶ G :=
{ to_fun := quot.lift (gen.lift f)
  begin
    intros a b h,
    induction h,
    case assoc { apply mul_assoc},
    case left_one { apply one_mul },
    case right_one { apply mul_one },
    case left_inv { apply mul_left_inv },
    case right_inv { apply mul_right_inv},
    case mul_congr_left : a₁ a₂ b h ih
    { apply congr_arg2 (*) ih rfl },
    case mul_congr_right : a b₁ b₂ h ih
    { apply congr_arg2 (*) rfl ih},
    case inv_congr : a b h ih
    { apply congr_arg group.inv ih },
  end,
  map_one' := by tidy,
  map_mul' := by tidy } 

variables (g : free_group α ⟶ G)

@[simp] lemma map_quot_mk_mul (a b : gen α )
  g 〚a.mul b〛 = g 〚a〛 * g 〚b〛 :=
g.map_mul〚a〛〚b〛

def of : α ⟶ free_group α  :=
λ a, 〚gen.of a〛

lemma hom_ext (f g : free_group α ⟶ G)
  (h : of ≫ f = of ≫ g) :
f = g :=
begin
  ext ⟨a⟩,
  induction a,
  case of : a { apply congr_fun h a },
  case mul : a b iha ihb
  { simp, 
  exact congr_arg2 (*) iha ihb },
end

def free : Set ⥤ Group :=
{ obj := free_group,
  map := λ  α β f, lift (f ≫ of),
  map_id' := _,
  map_comp' := _ }

def adjunction : free ⊣ forget Group :=
adjunction.mk_of_hom_equiv
{ hom_equiv := _,
  hom_equiv_naturality_left_symm' := _,
  hom_equiv_naturality_right' := _ }

instance : is_right_adjoint (forget Group) :=
{ left := free,
  adj := adjunction }

end Group.free