import ring_theory.coprime
import data.real.basic

open nat
noncomputable theory

namespace fermat

def is_sum_of_relprime_squares (n:ℕ) :=
∃ a b, n = a^2 + b^2 ∧ gcd a b = 1.

theorem lem_1_4 (N q: ℕ) :
  is_sum_of_relprime_squares N →
  nat.prime q → is_sum_of_relprime_squares q → q ∣ N →
  is_sum_of_relprime_squares (N/q) :=
begin
intros Hrel Hqprime Hqsq Hqdiv,
unfold is_sum_of_relprime_squares at Hrel,
cases Hrel with a Hrel,
cases Hrel with b Hrel,
cases Hrel with H1 H2,
sorry
end

theorem strong_induction {p : ℕ → Prop} (n : ℕ) (h : ∀ (k : ℕ), (∀ (m : ℕ), m < k → p m) → p k) :
p n := sorry.

-- induction on N, then induction on p
--
theorem descent_wolog (p N : ℕ) :
  nat.prime p → p ∣ N → is_sum_of_relprime_squares N → is_sum_of_relprime_squares p:=
begin
  revert N,
  apply strong_induction p,
  intros p Hih1 N,

  apply strong_induction N,
  clear N,
  intros Ntemp Hih2,

  intros Hprime Hdiv Hsum,
  have HN : ∃ N, is_sum_of_relprime_squares N ∧ p ∣ N ∧ N < p^2/2,
  {
  sorry,
  },
  clear Hdiv Hsum,
  cases HN with N HN,
  cases HN with Hsum HN,
  cases HN with Hdiv HNlt,

  have Hcases : (N = p ∨ p < N),
  {
  cases Hdiv with x H,
  sorry,
  },
  cases Hcases with Heasy HpltN,
  { -- case N = p; easy!
  rw ←Heasy,
  assumption,
  },
  { -- case p < N
    -- show that there's a smaller prime factor q
    have Hq : ∃ q, prime q ∧ q ∣ N ∧ q < p,
    {
    sorry,
    -- FIXME: this will be impossible without the WOLOG
    },
    -- use lemma 1.4 to show that p | (N/q) and N/q is also a sum of squares of rel prime integers
    cases Hq with q Hq,
    specialize Hih1 q Hq.2.2 N Hq.1 Hq.2.1 Hsum,
    -- by our strong induction on N (Hih2), we'll be done
    apply Hih2 (N/q),
    {
    sorry,
    },
    { assumption },
    { sorry },
    { apply lem_1_4 N q Hsum Hq.1 Hih1 Hq.2.1, }
  }
end

theorem descent (p x y : ℕ) :
  p ∣ x^2 + y^2 → gcd x y = 1 → ∃ z w, p = z^2 + w^2 :=
begin
  intros Hp Hrel,
  sorry
end

end fermat
