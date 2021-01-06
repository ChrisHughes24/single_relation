@[reducible] def free_group (α : Type) := list (α × ℤ)

variables {α : Type}

namespace free_group

instance : has_one (free_group α) := ⟨[]⟩

-- inv_core a b is a⁻¹ * b
def inv_core : free_group α → free_group α → free_group α
| []            l  := l
| (⟨i, n⟩::l₁)  l₂ := inv_core l₁ (⟨i, -n⟩::l₂)

instance : has_inv (free_group α) :=
⟨λ l, inv_core l []⟩

def mul_aux [decidable_eq α] : Π (l₁ l₂ : free_group α), free_group α
| []      l₂      := l₂
| (i::l₁) []      := (i :: l₁).reverse
| (i::l₁) (j::l₂) :=
  if hij : i.1 = j.1
    then let c := i.2 * j.2 in
      if c = 1
        then mul_aux l₁ l₂
        else l₁.reverse_core (⟨i.1, c⟩::l₂)
    else l₁.reverse_core (i::j::l₂)

instance [decidable_eq α] : has_mul (free_group α) := ⟨λ l₁ l₂, mul_aux l₁.reverse l₂⟩

def length (w : free_group α) : ℕ :=
w.foldl (λ n a, n + a.2.nat_abs) 0

end free_group
