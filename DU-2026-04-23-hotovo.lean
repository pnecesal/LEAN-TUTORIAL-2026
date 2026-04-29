import LeanZCU.Hodina2

example (a : ℚ) : a ^ 2 = a * a := by
  -- Dokažte nalezením správného termu.
  ring

example (a b c d : ℕ) (ha : a = b + d) (hb : b = a * a) (hc : c = b + d) (hd : d = c * c) :
    b ^ d = d ^ b := by
  -- Dokažte pouze pomocí `rw`.
  rw [hd, hb, ha, hc]

example (a b c d : ℤ) (ha : a = d ^ 4) (hb : b = 1 / c) (hc : c = a - b) (hd : d = 4 * a) :
    (a + b) ^ 2 - c ^ 2 = b * d := by
  -- Dokažte pouze pomocí `rw` a `ring`.
  rw [hc, hd]
  ring

example (x : ℝ) : 50*x^2 - 126*x + 96 ≥ 0 := by
  · convert_to x^2 + (7*x - 9)^2 + 15 ≥ 0
    · ring
    nlinarith

example (x y : ℝ) : x^4 * y^2 - 2 * x^3 * y^3 + x^2 * y^4 ≥ 0 := by
  · convert_to (x * y * (x - y))^2 ≥ 0
    · ring
    nlinarith

example (x y : ℝ) : 2 * x^3 * y^3 ≤ x^4 * y^2 + x^2 * y^4 := by
  have pom : 0 ≤ x^4 * y^2 - 2 * x^3 * y^3 + x^2 * y^4
  · convert_to 0 ≤ (x * y * (x - y))^2
    · ring
    nlinarith
  linarith

example (x y z : ℝ) : 4*x^2 + 12*x*y - 4*x*z + 9*y^2 - 6*y*z + z^2 ≥ 0 := by
  · convert_to (z - 2*x - 3*y)^2 ≥ 0
    · ring
    nlinarith

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 1 / b ≤ a / b^2 + b / a^2 := by
  have pom : 0 ≤ (a + b)*(a - b)^2
  · sorry
  sorry
