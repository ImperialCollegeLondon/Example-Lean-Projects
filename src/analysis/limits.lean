import data.real.basic
import algebra.pi_instances -- to make "a + b" work

/-- is_limit a t means that t is the limit of the sequence a(0), a(1),...-/
def is_limit (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε, (0 : ℝ) < ε → ∃ N, ∀ n, N ≤ n → abs (a n - t) ≤ ε

/-
A note on lambda notation.

λ n, n^2 is the squaring function. A mathematician might write it
  n ↦ n^2 . Note that the advantage of these notations is that you 
  can talk about the function without ever giving it a name; if you
  say "f(x)=x^2" then you just used up f. 

(λ n, c) is the function that takes n as input, and then always returns c.
So it's a constant function.
-/

-- abs_zero is the lemma that abs 0 = 0

theorem limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  sorry
end

-- For this one you might find `abs_le` useful.

-- sum of the limits is the limit of the sums

theorem limit_add (a b : ℕ → ℝ) (s t : ℝ) :
  is_limit a s → is_limit b t → is_limit (a + b) (s + t) :=
begin
  sorry,
end


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

