import ring_theory.coprime
import data.real.basic
import data.nat.modeq

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
  N > 0 → prime p → p ∣ N → is_sum_of_relprime_squares N → is_sum_of_relprime_squares p:=
begin
  revert N,
  apply strong_induction p,
  intros p Hih1 N,

  apply strong_induction N,
  clear N,
  intros Ntemp Hih2,

  intros HNpos Hprime Hdiv Hsum,
  have HN : ∃ N, 0 < N ∧ is_sum_of_relprime_squares N ∧ p ∣ N ∧ N < p^2/2,
  {
  sorry,
  },
  clear Hdiv Hsum,
  rcases HN with ⟨N, HNpos, Hsum, Hdiv, Hle⟩,

  have Hcases : (N = p ∨ p < N),
  {
    let  H : _ := nat.le_of_dvd HNpos Hdiv,
    -- This shouldn't be so complicated.
    by_contra,
    push_neg at h,
    have h2 : (p = N),
    { exact le_antisymm H h.2, },
    rw h2 at h,
    let H :=  h.1,
    contradiction,
  },
  cases Hcases with Heasy HpltN,
  { -- case N = p; easy!
  rw ←Heasy,
  assumption,
  },
  { -- case p < N
    -- show that there's a smaller prime factor q
    have Hq : ∃ q, prime q ∧ q ∣ N ∧ q < p,
    { -- split into cases using dite
    exact dite (N.factors = [p])
    (begin -- case p is the only prime factor; contradiction
    intros Hps2,
    let h2 := prod_factors HNpos,
    rewrite Hps2 at h2,
    simp at h2,
    exfalso,
    linarith
    end
    )
    (begin -- case that there are factors other than p
    let Hpfactor := (mem_factors HNpos).2 ⟨Hprime, Hdiv⟩,
    have Hp : [p] ⊆ N.factors,
    { sorry, },
    intros HNp,
    have Hothers : ∀ q ∈ (N/p).factors, q < p,
    { sorry, },
    have Hp : ¬((N/p).factors = list.nil),
    { sorry },
    set qs := (N/p).factors,
    destruct qs,
    { sorry }, -- contradiction
    { intros q _ Hqs,
      specialize Hothers q _,
      { rewrite Hqs, simp },
      existsi q,
      let Hy := (nat.mem_factors HNpos).1 _, swap,
      {
        exact q
      },
      swap,
      { -- q ∈ (N/p).factors → q ∈ N.factors
        sorry,
      },
      {
      have Hyy : prime q ∧ q ∣ N,
      { exact Hy },
      cases Hyy with Hqprime Hqdiv,
      split,
      { assumption },
      split,
      { assumption },
      { assumption },
      },
    }
    end
    )
    },
    -- use lemma 1.4 to show that p | (N/q) and N/q is also a sum of squares of rel prime integers
    cases Hq with q Hq,
    specialize Hih1 q Hq.2.2 N HNpos Hq.1 Hq.2.1 Hsum,
    -- by our strong induction on N (Hih2), we'll be done
    apply Hih2 (N/q),
    {
    sorry,
    },
    { -- Prove that N/q is non-negative
    sorry },
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

-- Reciprocity step

theorem reciprocity (p : ℕ) :
  prime p → 1 ≡ p [MOD 4] → ∃ N, N > 0 ∧ p ∣ N ∧ is_sum_of_relprime_squares N :=
begin
  intros Hprime Hpmod,
  rw modeq.modeq_iff_dvd' at Hpmod,
  swap,
  {
  sorry,
  },
  rcases Hpmod with ⟨k, Hpmod⟩,
  have Hp : p = 4 * k + 1, {
  unfold prime at Hprime,
  rcases Hprime with ⟨Hpineq, _⟩,
  sorry,
  },
  have h₁ : ∀ x, x ≠ 0 → (x^(2 * k) - 1) * (x^(2*k) + 1) ≡ 0 [MOD p],
  { sorry },
  sorry
end


theorem fermat (p : ℕ) :
  prime p → 1 ≡ p [MOD 4] → ∃ a b, p = a^2 + b^2 :=
begin
  intros Hprime Hpmod,
  rcases (reciprocity p Hprime Hpmod) with ⟨N, HNpos, Hdiv, Hsum⟩,
  rcases (descent_wolog p N HNpos Hprime Hdiv Hsum) with ⟨a, b, Hsum, _⟩,
  existsi a,
  existsi b,
  assumption
end

end fermat
