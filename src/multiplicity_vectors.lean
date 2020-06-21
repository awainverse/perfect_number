import data.finsupp
import data.pnat.factors
import order.conditionally_complete_lattice
import order.lattice
import tactic.pi_instances

set_option old_structure_cmd true

open_locale classical
open_locale big_operators


noncomputable theory

def pnat.coprime (m n : ℕ+) : Prop := m.gcd n = 1

def mult (n : ℕ+) (p : nat.primes) : ℕ := (pnat.factor_multiset n).count p

--def prime_vector : Type := finsupp nat.primes ℕ

def factorisation (n : ℕ+) : nat.primes →₀ ℕ := finsupp.of_multiset n.factor_multiset

@[simp]
lemma inf_zero_iff {m n : ℕ} : m ⊓ n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split, swap, intro h, cases h; rw h; simp,
  unfold has_inf.inf, unfold semilattice_inf.inf, unfold lattice.inf, unfold min,
  intro hmin, by_cases m = 0, left, apply h,
  rw if_neg _ at hmin, right, apply hmin, contrapose hmin,
  simp only [not_lt, not_le] at hmin, rw if_pos hmin, apply h
end

lemma nat.zero_eq_bot : (0 : ℕ) = ⊥ := rfl

variable {α : Type}

instance finsupp.has_inf :
  has_inf (α →₀ ℕ) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨v1.support ∩ v2.support, (λ (a : α), (v1 a ⊓ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_inter],
  symmetry, rw not_iff_comm, push_neg, rw inf_zero_iff,
end

@[simp]
lemma finsupp.inf_apply {a : α} {f g : α →₀ ℕ} : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp]
lemma finsupp.support_inf {f g : α →₀ ℕ} : (f ⊓ g).support = f.support ⊓ g.support := rfl

instance finsupp.has_sup :
  has_sup (α →₀ ℕ) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨v1.support ∪ v2.support, (λ (a : α), (v1 a ⊔ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_inter],
  symmetry, rw not_iff_comm, simp only [finsupp.mem_support_iff, ne.def, finset.mem_union],
  push_neg, repeat {rw nat.zero_eq_bot}, rw sup_eq_bot_iff,
end

@[simp]
lemma finsupp.sup_apply {a : α} {f g : α →₀ ℕ} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma finsupp.support_sup {f g : α →₀ ℕ} : (f ⊔ g).support = f.support ⊔ g.support := rfl

-- finsupp.to_multiset_strict_mono

lemma nat.bot_eq_zero : (⊥ : ℕ) = 0 := rfl

instance finsupp.lattice : lattice (α →₀ ℕ) :=
begin
  refine lattice.mk has_sup.sup has_le.le preorder.le _ _ _ _ _ _ _ has_inf.inf _ _ _,
  exact (finsupp.preorder).le_refl,
  exact (finsupp.preorder).le_trans,
  sorry, -- apply finsupp.preorder.lt_iff_le_not_le
  exact (finsupp.partial_order).le_antisymm,
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *,
    intros, rw finsupp.sup_apply, apply sup_le,
    { by_cases s ∈ a.support, apply a_1 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp },
    { by_cases s ∈ b.support, apply a_2 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp }
    },
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *, intros,
    rw finsupp.inf_apply, apply le_inf, apply a_1 s H, apply a_2 s H }
end

instance finsupp.semilattice_inf_bot : semilattice_inf_bot (α →₀ ℕ) :=
begin
  sorry
end

@[simp]
lemma finsupp.to_multiset_of_multiset {m : multiset α} :
  (finsupp.of_multiset m).to_multiset = m := by { ext, simp }

@[simp]
lemma finsupp.of_multiset_to_multiset {f : α →₀ ℕ} :
  finsupp.of_multiset (finsupp.to_multiset f) = f := by { ext, simp }

@[simp]
lemma factorisation_to_multiset_eq_factor_multiset {n : ℕ+} :
  (factorisation n).to_multiset = n.factor_multiset :=
by { unfold factorisation, simp }

lemma finsupp.of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at a_1, apply a_1.left },
  { have h := a_1.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

section basic_number_theory_definitions

lemma dvd_iff_le_factorisations {m n : ℕ+} :
  m ∣ n ↔ factorisation m ≤ factorisation n := sorry

lemma factorisation_gcd_eq_inf_factorisations {m n : ℕ+} :
  factorisation (m.gcd n) = has_inf.inf (factorisation m) (factorisation n) :=
begin
  sorry
end

lemma coprime_iff_disjoint_supports {m n : ℕ+} :
  m.coprime n ↔ disjoint (factorisation m).support (factorisation n).support :=
begin
  sorry
end

lemma coprime_iff_disjoint_factorisations {m n : ℕ+} :
  m.coprime n ↔ disjoint (factorisation m) (factorisation n) :=
begin
  sorry
end

end basic_number_theory_definitions

@[instance]
def prime_finsupp_coe_pnat : has_coe (nat.primes →₀ ℕ) (ℕ+ →₀ ℕ) :=
{ coe := finsupp.map_domain coe }

lemma prime_finsupp_coe_prod_pow {f : nat.primes →₀ ℕ} :
(↑f : ℕ+ →₀ ℕ).prod pow = f.prod (λ (p : nat.primes), pow ↑p) :=
begin
  apply finsupp.prod_map_domain_index, simp,
  intros, rw pow_add,
end

-- Just wraps to_multiset in the prime_multiset type for the next lemma to typecheck
def finsupp.to_prime_multiset (f : nat.primes →₀ ℕ) : prime_multiset := f.to_multiset

lemma coe_pnat_commute_to_multiset {f : nat.primes →₀ ℕ} :
(↑f : ℕ+ →₀ ℕ).to_multiset =  prime_multiset.to_pnat_multiset f.to_prime_multiset :=
begin
  unfold prime_multiset.to_pnat_multiset, unfold finsupp.to_prime_multiset,
  rw finsupp.to_multiset_map, refl
end

lemma prod_pow_factorisation (n : ℕ+) :
  (factorisation n).prod (λ (p : nat.primes), pow ↑p) = n :=
begin
  rw ← prime_finsupp_coe_prod_pow,
  rw ← finsupp.prod_to_multiset,
  conv_rhs {rw ← pnat.prod_factor_multiset n},
  rw ← factorisation_to_multiset_eq_factor_multiset,
  rw coe_pnat_commute_to_multiset, refl
end

@[simp]
lemma factorisation_mul {m n : ℕ+} :
  factorisation (m * n) = factorisation m + factorisation n :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factorisation (m * n)) =
    finsupp.to_multiset (factorisation m + factorisation n),
  simp [finsupp.to_multiset_add, factorisation,
    finsupp.to_multiset_of_multiset, pnat.factor_multiset_mul]
end

section coprime_part

variables (p : nat.primes) (n : ℕ+)

/--
The greatest divisor n coprime to prime p
-/
def coprime_part : ℕ+ :=
((factorisation n).erase p).prod (λ (p : nat.primes), pow ↑p)

variables {p} {n}

lemma factorisation_prod_pow {f : nat.primes →₀ ℕ} :
factorisation (f.prod (λ (p : nat.primes), pow ↑p)) = f :=
begin
  sorry
end

lemma factorisation_coprime_part_eq_erase_factorisation :
  factorisation (coprime_part p n) = (factorisation n).erase p :=
by { rw coprime_part, apply factorisation_prod_pow }

variable (n)
lemma pow_mult_coprime_part_eq_self :
  (coprime_part p n) * p ^ (factorisation n p) = n :=
begin
  rw coprime_part,
  conv_rhs {rw ← prod_pow_factorisation n},
  sorry,
end
variable {n}

@[simp]
lemma factorisation_one : factorisation 1 = 0 :=
begin 
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factorisation 1) = finsupp.to_multiset 0,
  rw [finsupp.to_multiset_zero, factorisation_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_one]
 end

@[simp]
lemma factorisation_prime : factorisation ↑p = finsupp.single p 1 :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factorisation ↑p) = finsupp.to_multiset (finsupp.single p 1),
  rw [finsupp.to_multiset_single, factorisation_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_of_prime, prime_multiset.of_prime],
  simp
end

@[simp]
lemma factorisation_pow {k : ℕ} : factorisation (n ^ k) = k • factorisation n :=
begin
  induction k, simp,
  rw [pow_succ, nat.succ_eq_add_one, add_smul, ← k_ih, mul_comm], simp
end

lemma not_dvd_coprime_part : ¬ (↑p ∣ (coprime_part p n)) :=
begin
  rw [dvd_iff_le_factorisations, finsupp.le_iff], push_neg, existsi p, 
  rw [factorisation_prime, factorisation_coprime_part_eq_erase_factorisation],
  simp,
end

lemma coprime_pow_coprime_part {k : ℕ} (pos : 0 < k): ((p : ℕ+) ^ k).coprime (coprime_part p n) :=
begin
  rw coprime_iff_disjoint_supports,
  rw [factorisation_pow, factorisation_prime, factorisation_coprime_part_eq_erase_factorisation],
  simp only [finsupp.support_erase, finsupp.smul_single], rw finsupp.support_single_ne_zero, simp,
  rw [nat.smul_def, nat.nsmul_eq_mul, mul_one], omega,
end

lemma prime_dvd_iff_factorisation_pos :
↑p ∣ n ↔ 0 < factorisation n p :=
begin
  sorry
end

lemma coprime_of_prime_not_dvd (h : ¬ ↑p ∣ n) : n.coprime p :=
begin
  rw coprime_iff_disjoint_supports,
  rw prime_dvd_iff_factorisation_pos at h,
  rw factorisation_prime, rw finsupp.support_single_ne_zero, swap, omega,
  rw finset.disjoint_singleton, simp only [finsupp.mem_support_iff, classical.not_not], omega,
end

lemma dvd_coprime_part_of_coprime_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ ↑p ∣ m) :
  m ∣ (coprime_part p n) := sorry

def two_prime : nat.primes := ⟨2, nat.prime_two⟩

variable (n)
def odd_part : ℕ+ := coprime_part two_prime n
variable {n}

lemma dvd_odd_part_of_odd_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ 2 ∣ m) :
  m ∣ (odd_part n) :=
begin
  unfold odd_part, apply dvd_coprime_part_of_coprime_dvd hmn, apply hmp
end

lemma coprime_pow_odd_part {k : ℕ} (pos : 0 < k) : ((2 : ℕ+) ^ k).coprime (odd_part n) :=
begin
  rw odd_part, 
  have h : pnat.coprime (↑two_prime ^ k) (coprime_part two_prime n) := coprime_pow_coprime_part pos,
  apply h
end

variable (n)
lemma pow_mult_odd_part_eq_self : (odd_part n) * 2 ^ (factorisation n two_prime) = n :=
begin
  rw odd_part,
  --conv_rhs {rw ← prod_pow_factorisation n},
  change coprime_part two_prime n * ↑two_prime ^ (factorisation n) two_prime = n,
  rw pow_mult_coprime_part_eq_self n,
end
variable {n}

end coprime_part

section multiplicative

def is_multiplicative {α : Type} [comm_monoid α] (f : ℕ+ → α): Prop :=
f(1) = 1 ∧ ∀ m n : ℕ+, nat.coprime m n → f(m * n) = f(m) * f(n)

lemma multiplicative_from_prime_pow {α : Type} [comm_monoid α] {f : ℕ+ → α} (h : is_multiplicative f) :
∀ n : ℕ+, f(n) = (factorisation n).prod (λ p : nat.primes, λ k : ℕ, f (p ^ k)) :=
begin
  sorry
end

end multiplicative

