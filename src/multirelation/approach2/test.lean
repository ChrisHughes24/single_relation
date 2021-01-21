import .tactic

--set_option profiler true
variables {G : Type*} [group G]
  (a b c d e f g h i j k l m n o p q r s t u v w x y z : G)

set_option profiler true
lemma test1
  (h₁ : a * b^2 = b * a)
  (h₂ : b * a^2 = a * b) :
  a = 1 :=
begin
  group_rel [h₁, h₂]
end

lemma test2 (h : a * b * a⁻¹ = 1) : b = 1 :=
by group_rel [h]

lemma test3 (h : a * b = b ^ 2 * a) :
  b * (a ^ 4 * b * a ^ (-4 : ℤ)) =
      (a ^ 4 * b * a ^ (-4 : ℤ)) * b :=
begin
  group_rel [h],

end

lemma test3b
  (h : a * b = b ^ 2 * a)
  (h₁ : d * a * b * a = d * c * a) :
  b * (a ^ 4 * b * a ^ (-4 : ℤ)) =
      (a ^ 3 * c * a ^ (-4 : ℤ)) * b :=
begin
  group_rel [h, h₁],


end

lemma test3c (h : a * b = b ^ 2 * a) :
  b * (a ^ 5 * b * a ^ (-5 : ℤ)) =
      (a ^ 5 * b * a ^ (-5 : ℤ)) * b :=
begin
  group_rel [h],

end

lemma test4 (h : a * b = b ^ 2 * a) (n : ℕ) :
  a ^ n * b * a ^ (-n : ℤ) = b ^ (2 ^ n) :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ' 2, pow_mul],
    group_rel [h, ih] },
end

lemma test6 (h : ∀ g : G, g ^ 2 = 1) : a * b = b * a :=
by group_rel [h a, h b, h (a * b)]

lemma test7a (h : a * b = b * a) : a^10 * b^10 * a^10 = b^9 * a^20 * b :=
by group_rel [h]

#print expr

run_cmd do env ← tactic.get_env, dec ← env.get `test1,
  let n : nat := dec.value.fold 0 (λ _ m n, n + 1),
  tactic.trace n

lemma test7b (h : a * b = b * a) : a^1 * b^2*a^2 = b^ 1* a^3 * b :=
by group_rel [h]

lemma test5 (h : a * b = b^2 * a) : a^2 * b = b^4 * a^2 :=
by group_rel [h]

lemma test8 (m n : nat) : a ^ n * a ^ m = a ^ m * a ^ n :=
by group_rel []

lemma test9 (h : a * b * a * b * a * b * b = 1) : a * b = b * a :=
by group_rel [h]

lemma Q8
  (hi : i^2 = e)
  (hj : j^2 = e)
  (hk : k^2 = e)
  (hijk : i * j * k = e)
  (he : e^2 = 1) :
  j * i * j  = i :=
begin
  group_rel [hi, hj, hk, hijk, he],
end

#print Q8
