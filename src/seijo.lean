namespace SirkerfNumberTheory

def isDivisible (a : Int)(b : Int): Prop :=
  ∃ c : Int , b = a * c

theorem divided_by_one (b : Int): isDivisible 1 b := by
  rw [isDivisible]
  exists b
  simp
