import .tactic

variables {G : Type*} [group G]
(a b c d e f g h i j k l m n p q r s t u v w x y z : G)

set_option profiler true

-- lemma test1
--   (h₁ : a * b^2 = b * a)
--   (h₂ : b * a^2 = a * b) :
--   a = 1 :=
-- begin
--   group_rel [h₁, h₂],

-- end

lemma test2 (h : a * b * a⁻¹ = 1) : b = 1 :=
by group_rel [h]

lemma test3 (h : a * b = b ^ 2 * a) :
  b * (a ^ 4 * b * a ^ (-4 : ℤ)) =
      (a ^ 4 * b * a ^ (-4 : ℤ)) * b :=
begin
  group_rel [h],

end

lemma test3b (h : a * b = b ^ 2 * a)
  (h₁ : a * b = c) :
  b * (a ^ 4 * b * a ^ (-4 : ℤ)) =
      (a ^ 4 * c * a ^ (-4 : ℤ)) * b :=
begin
  --group_rel [h, h₁],

end

lemma test3c (h : a * b = b ^ 2 * a) :
  b * (a ^ 5 * b * a ^ (-5 : ℤ)) =
      (a ^ 5 * b * a ^ (-5 : ℤ)) * b :=
begin
  --group_rel [h, h₁],

end


lemma test4 (h : a * b = b ^ 2 * a) (n : ℕ) :
  a ^ n * b = b ^ (2 ^ n) * a ^ n :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, pow_succ', pow_mul],
    have hb : b ^ (2 ^ n) * b = b * b ^ (2 ^ n), from pow_mul_comm' _ _,
    have ha : a ^ n * a = a * a ^ n, from pow_mul_comm' _ _,
    group_rel [h, ih, ha, hb] },
end

lemma test (h : a * b = b * a) : a^100 * b = b * a^100 :=
by group_rel [h]

lemma test5 (h : a * b = b^2 * a) : a^2 * b = b^4 * a^2 :=
by group_rel [h]

lemma test6 (h : a * b * a * b^2 = 1) : a * b = b * a :=
by group_rel [h]
