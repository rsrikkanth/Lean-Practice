import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg b, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_zero b, ← add_right_neg a, ← add_assoc, add_comm b a, h, add_comm a c, add_assoc, add_right_neg, add_zero]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact add_left_cancel h


theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, zero_add, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← zero_add b]
  rw [← add_right_neg a]
  rw [add_comm a]
  rw [add_assoc]
  rw [h]
  rw [add_zero (-a)]


theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← zero_add a]
  rw [← add_right_neg b]
  rw [add_comm b]
  rw [add_assoc]
  rw [add_comm b a]
  rw [h]
  rw [add_zero (-b)]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have h : - -a + -a = 0 := by
    rw [neg_add_cancel]
  rw [← add_right_neg a] at h
  rw [add_right_cancel h]
end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg]
  rw [add_right_neg a]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]
end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  nth_rw 1 [← one_mul a]
  nth_rw 1 [← one_mul (a⁻¹)]
  nth_rw 1 [← inv_mul_cancel (a⁻¹)]
  nth_rw 1 [← inv_mul_cancel a]
  nth_rw 1 [mul_assoc]
  nth_rw 1 [mul_assoc]
  nth_rw 2 [← mul_assoc]
  rw [← mul_assoc (a⁻¹ * a) (a⁻¹ * a) a⁻¹]
  rw [← mul_assoc (a⁻¹ * a) a⁻¹ a]
  rw [inv_mul_cancel]
  rw [one_mul]
  rw [inv_mul_cancel]
  rw [one_mul]
  rw [inv_mul_cancel (a⁻¹)]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a]
  rw [← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul ((a * b)⁻¹)]
  rw [← inv_mul_cancel b]
  nth_rw 2 [← one_mul b]
  rw [← inv_mul_cancel a]
  rw [mul_assoc (a⁻¹) a b]
  rw [← mul_assoc b⁻¹ a⁻¹ (a * b)]
  rw [mul_assoc (b⁻¹ * a⁻¹) (a * b) (a * b)⁻¹]
  rw [mul_inv_cancel (a * b)]
  rw [mul_one]
end MyGroup

end
