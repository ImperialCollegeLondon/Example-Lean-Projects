import data.real.basic
import algebra.pi_instances -- to make "a + b" work

/-- is_limit a t means that t is the limit of the sequence a(0), a(1),...-/
def is_limit (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε, (0 : ℝ) < ε → ∃ N, ∀ n, N ≤ n → abs (a n - t) ≤ ε

-- Things you might find useful:
-- #check abs_le

-- A sequence has at most one limit

theorem limit_unique (a : ℕ → ℝ) (s t : ℝ) :
  is_limit a s → is_limit a t → s = t :=
begin
  sorry,
end

/-
Hints: 
1) This might be trickier than you think.
2) Prove by contradiction. WLOG s < t
3) Use linarith liberally 
4) `abs_le` is helpful
-/

-- sum of the limits is the limit of the sums

theorem limit_add (a b : ℕ → ℝ) (s t : ℝ) :
  is_limit a s → is_limit b t → is_limit (a + b) (s + t) :=
begin
  sorry,
end