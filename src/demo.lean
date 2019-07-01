import data.real.basic

-- The natural numbers.
inductive mynat 
| zero : mynat
| succ : mynat → mynat

variable (R : mynat → mynat → Prop)

-- Term mode.
lemma forall_exists_of_exists_forall
: (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) :=
λ ⟨a, Ha⟩ b, ⟨a, Ha b⟩

-- Tactic mode.
lemma forall_exists_of_exists_forall' 
: (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) :=
begin
  intro H,
  intro b,
  cases H with a Ha,
  existsi a,
  exact (Ha b),
end

-- Consider a new relation on ℝ.
variable (R' : ℝ → ℝ → Prop)

-- Suppose R' has the following property.
axiom property : ∀ x, ∃ y, R' x y

-- Classical library example.
noncomputable def find_image
: Π n, {m // R' n m} :=
λ n, classical.choice 
  (let ⟨m, Hm⟩ := property R' n in ⟨⟨m, Hm⟩⟩)
