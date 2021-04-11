import multirelation.approach2.tactic
import tactic.group1r

variables {G : Type} [group G]
  (a b c d e f g h i j k l m n o p q r s t u v w x y z : G)

set_option profiler true

-- example (h : a * b * a * b = 1) :
--   (b * a * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ = 1) :=
-- by group1r using h

-- example (h : a * b * a * b = 1) :
--   (b * a * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ = 1) :=
-- by group_rel [h]

-- example (h : a * b * a * b = 1) :
--   ((b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹)^4  = 1) :=
-- by group1r using h

-- example (h : a * b * a * b = 1) :
--   ((b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹)^4  = 1) :=
-- by group_rel [h]

-- -- example (h : a * b * a * b = 1) :
-- --   ((b * a * b * a)^100  = 1) :=
-- -- by group1r using h

-- -- example (h : a * b * a * b = 1) :
-- --   ((b * a * b * a)^100  = 1) :=
-- -- by group_rel [h]

-- -- example (h : a * b * a * b = 1) :
-- --   ((b * a * b * a)^200  = 1) :=
-- -- by group1r using h

-- example (h : a * b * a * b = 1) :
--   ((b * a * b * a)^200  = 1) :=
-- by group_rel [h]

-- example (h : a * b = b ^ 2 * a) :
--   (a * b * a ^ (-1 : ℤ) * b = b * a * b * a ^ (-1 : ℤ)) :=
-- by group1r using h

-- example (h : a * b = b ^ 2 * a) :
--   (a * b * a ^ (-1 : ℤ) * b = b * a * b * a ^ (-1 : ℤ)) :=
-- by group_rel [h]

-- example (h : a * b = b ^ 2 * a) :
--   (a ^ 5 * b * a ^ (-5 : ℤ) * b = b * a ^ 5 * b * a ^ (-5 : ℤ)) :=
-- by group1r using h

example (h : a * b = b ^ 2 * a) :
  (a ^ 6 * b * a ^ (-6 : ℤ) * b = b * a ^ 6 * b * a ^ (-6 : ℤ)) :=
by group1r using h

-- example (h : a * b = b ^ 2 * a) :
--   (a ^ 5 * b * a ^ (-5 : ℤ) * b = b * a ^ 5 * b * a ^ (-5 : ℤ)) :=
-- by group_rel [h]

-- example (h : a * b = b ^ 2 * a) :
--   (a ^ 2 * b * a ^ (-2 : ℤ) * b = b * a ^ 2 * b * a ^ (-2 : ℤ)) :=
-- by group1r using h

-- example (h : a * b = b ^ 2 * a) :
--   (a ^ 2 * b * a ^ (-2 : ℤ) * b = b * a ^ 2 * b * a ^ (-2 : ℤ)) :=
-- by group_rel [h]

-- example (h : a * b = b * a) :
--   (a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2) :=
-- by group1r using h

-- example (h : a * b = b * a) :
--   (a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2) :=
-- by group_rel [h]

-- example (h : a * b = b * a) :
--   (a ^ 5 * b ^ 5 = b ^ 5 * a ^ 5) :=
-- by group1r using h

-- example (h : a * b = b * a) :
--   (a ^ 5 * b ^ 5 = b ^ 5 * a ^ 5) :=
-- by group_rel [h]

-- example (h : a * b = b * a) :
--   (a ^ 10 * b ^ 10 = b ^ 10 * a ^ 10) :=
-- by group1r using h

-- example (h : a * b = b * a) :
--   (a ^ 10 * b ^ 10 = b ^ 10 * a ^ 10) :=
-- by group_rel [h]

-- example (h : a * b * a ^ (-11 : ℤ) * b ^ 4 = 1) :
--   (a ^ 10 * b * a * b * a ^ (-11 : ℤ) * b ^ 3 * a ^ (-10 : ℤ)
--     * b ^ (-4 : ℤ) * a ^ 11 * b⁻¹ * a⁻¹ = 1) :=
-- by group1r using h

-- example (h : a * b * a ^ (-11 : ℤ) * b ^ 4 = 1) :
--   (a ^ 10 * b * a * b * a ^ (-11 : ℤ) * b ^ 3 * a ^ (-10 : ℤ)
--     * b ^ (-4 : ℤ) * a ^ 11 * b⁻¹ * a⁻¹ = 1) :=
-- by group_rel [h]

-- example (h : a * (b * c) * a⁻¹ * (b * c) ^ (-2 : ℤ) = 1) :
--   a^6 * b * c * a * b * c * a⁻¹ * (b * c)^(-2 : ℤ) * c⁻¹ * b⁻¹ * a^(-5 : ℤ) *
--     (b * c) * a⁻¹ * (b * c) ^ (-2 : ℤ) = 1 :=
-- by group1r using h

-- example (h : a * (b * c) * a⁻¹ * (b * c) ^ (-2 : ℤ) = 1) :
--   a^6 * b * c * a * b * c * a⁻¹ * (b * c)^(-2 : ℤ) * c⁻¹ * b⁻¹ * a^(-5 : ℤ) *
--     (b * c) * a⁻¹ * (b * c) ^ (-2 : ℤ) = 1 :=
-- by group_rel [h]

-- example (h : a * b * a⁻¹ * b ^ (-3 : ℤ) = 1) :
--   a^4 * b * a * b * a⁻¹ * b^(-4 : ℤ) * a^(-3 : ℤ) *
--     b * a⁻¹ * b ^ (-3 : ℤ) = 1 :=
-- by group1r using h

-- example (h : a * b * a⁻¹ * b ^ (-3 : ℤ) = 1) :
--   a^4 * b * a * b * a⁻¹ * b^(-3 : ℤ) * b⁻¹ * a^(-3 : ℤ) *
--     b * a⁻¹ * b ^ (-3 : ℤ) = 1 :=
-- by group_rel [h]

-- example (h : a * b * a⁻¹ * b ^ (-2 : int) = 1) (h1 : b * c * a⁻¹ = 1) :
--   a ^ 2 * b * (a⁻¹)^2 * b * a^2 * b⁻¹ * (a⁻¹)^2 * b⁻¹ = 1 :=
-- by group_rel [h, h1]

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) * b * ((a * c)⁻¹) * b * (a * c) * b⁻¹ * ((a * c)⁻¹) * b⁻¹ = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) * b * ((a * c)⁻¹) * b * (a * c) * b⁻¹ * ((a * c)⁻¹) * b⁻¹ = 1 :=
-- by group1r using h

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) ^ 2 * b * ((a * c)⁻¹)^2 * b * (a * c)^2 * b⁻¹ * ((a * c)⁻¹)^2 * b⁻¹ = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) ^ 2 * b * ((a * c)⁻¹)^2 * b * (a * c)^2 * b⁻¹ * ((a * c)⁻¹)^2 * b⁻¹ = 1 :=
-- by group1r using h

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) ^ 5 * b * ((a * c)⁻¹)^5 * b * (a * c)^5 * b⁻¹ * ((a * c)⁻¹)^5 * b⁻¹ = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b ^ (-2 : int) = 1) :
--   (a * c) ^ 5 * b * ((a * c)⁻¹)^5 * b * (a * c)^5 * b⁻¹ * ((a * c)⁻¹)^5 * b⁻¹ = 1 :=
-- by group1r using h

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^2 * b^2 * (a * c) ^ (-2 : int) * b ^ (-2 : int) = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^2 * b^2 * (a * c) ^ (-2 : int) * b ^ (-2 : int) = 1 :=
-- by group1r using h

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^5 * b^5 * (a * c) ^ (-5 : int) * b ^ (-5 : int) = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^5 * b^5 * (a * c) ^ (-5 : int) * b ^ (-5 : int) = 1 :=
-- by group1r using h

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^10 * b^10 * (a * c) ^ (-10 : int) * b ^ (-10 : int) = 1 :=
-- by group_rel [h]

-- example (h : (a * c) * b * (a * c)⁻¹ * b⁻¹ = 1) :
--   (a * c)^10 * b^10 * (a * c) ^ (-10 : int) * b ^ (-10 : int) = 1 :=
-- by group1r using h

-- example (h : a * b * (a^3)⁻¹ * b^4 = 1) :
--   a^2 * b * a * b * a^(-3 : int) * b^3 * a^(-2 : int)
--   * b^(-4 : int) * a^3 * (a * b)⁻¹ = 1 :=
-- by group_rel [h]

-- example (h : a * b * (a^3)⁻¹ * b^4 = 1) :
--   a^2 * b * a * b * a^(-3 : int) * b^3 * a^(-2 : int)
--   * b^(-4 : int) * a^3 * (a * b)⁻¹ = 1 :=
-- by group1r using h

-- example (h : a * b * a⁻¹ * b^(-2 : int) = 1)
--   (h1 : b * a * b⁻¹ * a ^ (-2 : int) = 1) :
--   a = 1 :=
-- by group_rel [h, h1]

example (h1 : a * c * a⁻¹ * c⁻¹ = 1)
        (h2 : c⁻¹ * d * c * d * c⁻¹ * d⁻¹ * c * d⁻¹ = 1)
        (h3 : a * c⁻¹ * d * c * a⁻¹ * c⁻¹ * d⁻¹ * d⁻¹ * c = 1) :
   a * d * a⁻¹ * d⁻¹ * d⁻¹ = 1 :=
by group_rel [h1, h2, h3]
