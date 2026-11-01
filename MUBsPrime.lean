import Mathlib

set_option linter.style.longLine false
/-!
# Mutually unbiased bases in odd prime dimension: N(p) = p + 1

We have already proved the upper bound N(d) <= d + 1 ∀ d ≥ 2, in the `MUBsFormalization.lean` file. Now, we want to prove a stronger result,
which holds for all prime numbers 'p' except 2, which is the number of mutually unbiased bases is exactly equal to one more than number of dimensions, for number of dimensions being prime.
We would formalize the proof of `∀ p ∈ Prime, p ≠ 2, we have N(p) = p + 1`.
-/

noncomputable section

namespace MUBPrime

/-! ## Here we again write the basic definitions as was done in MUBsFormalization.lean -/

/-- A basis of `ℂ^d`, stored as a `d × d` unitary matrix (`U† U = I`) whose columns are the basis vectors.
-/
abbrev UMat (d : ℕ) := ↥(Matrix.unitaryGroup (Fin d) ℂ)

/--
relativeUnitary (U,V) = U†V
-/
def relativeUnitary {d : ℕ} (U V : UMat d) : Matrix (Fin d) (Fin d) ℂ :=
  star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)

/-- Two bases are mutually unbiased when ∀ i,j we have ∣(U†V)_{i,j}∣² = 1/d
-/
def IsUnbiased {d : ℕ} (U V : UMat d) : Prop :=
  ∀ i j : Fin d, ‖relativeUnitary U V i j‖ ^ (2 : ℕ) = (d : ℝ)⁻¹

/--
V†U = (U†V)†. Thus, ∣(V†U)_i,j∣² = ∣(U†v)_i,j∣² = 1/d
-/
lemma IsUnbiased.symm {d : ℕ} {U V : UMat d} (hUV : IsUnbiased U V) : IsUnbiased V U := by
  intro i j
  -- V† U = (U† V)†, using (AB)† = B† A† and (U†)† = U, which `simp` knows.
  have hstar : relativeUnitary V U = star (relativeUnitary U V) := by simp [relativeUnitary]
  calc
    ‖relativeUnitary V U i j‖ ^ (2 : ℕ)
        = ‖star (relativeUnitary U V) i j‖ ^ (2 : ℕ) := by simp [hstar]
    _ = ‖relativeUnitary U V j i‖ ^ (2 : ℕ) := by simp
    _ = (d : ℝ)⁻¹ := hUV j i

/--
IsMUBFamily(B0, B1, ... B_{k - 1}) ⇔ B_m and B_n are unbiased whenever m ≠ n
-/
def IsMUBFamily {d k : ℕ} (B : Fin k → UMat d) : Prop :=
  Pairwise fun m n => IsUnbiased (B m) (B n)

/--
HasMUBs d k: there exist `k` pairwise mutually unbiased bases of `ℂ^d`.
-/
def HasMUBs (d k : ℕ) : Prop :=
  ∃ B : Fin k → UMat d, IsMUBFamily B

/--
`IsMaxMUBCount d k` says `N(d) = k` that k unbiased bases exist, and any number m of unbiased bases satisfies `m ≤ k`.
-/
def IsMaxMUBCount (d k : ℕ) : Prop :=
  HasMUBs d k ∧ ∀ m : ℕ, HasMUBs d m → m ≤ k

-- From here to `end Prime`, a prime number `p` is fixed.


section Prime

/-!
`section` defines a region of the file where all variables are scoped within the section
-/

/-!
We indicate p is a prime natural number and package it with a proof. This allows ZMod p to be a field.
-/
variable {p : ℕ} [Fact p.Prime]

/--
We explicitly define p ≠ 0 as some Mathlib tools need this.
`Fact.out : p.Prime` unwraps the automatic fact to get the proof p is prime.
-/
instance neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/--
If p is prime and p ≠ 2, then 2 ≠ 0 (mod p).
`ZMod p` is contained in Mathlib, and it performs the modulo p operation, so it is used to define clock numbers.
-/
lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  -- Restate h with 2 written as the cast of the natural number 2 (same number).
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  -- Two primes with p ∣ 2 must be equal, so p = 2, contradicting hp2.
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

/-! ## The function e(x) = ω^x and the geometric sum -/

/--
We define e(x) = exp(2πix/p) = ωˣ, e(0) = 1, e(x + y) = e(x)·e(y)
This is Mathlib's "standard additive character" of `ZMod p`. It sends x to a complex number
-/
def e (x : ZMod p) : ℂ := ZMod.stdAddChar x

/-- `e(0) = 1` is true for every additive character. -/
lemma e_zero : e (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _

/-- `e(x + y) = e(x)·e(y)` is true for every additive character. -/
lemma e_add (x y : ZMod p) : e (x + y) = e x * e y := AddChar.map_add_eq_mul _ x y

/--
Every value of complex number `e` lies on the unit circle as it is unimodular, `∣e(x)∣ = 1.`
-/
lemma norm_e (x : ZMod p) : ‖e x‖ = 1 := by
  rw [e, ZMod.stdAddChar_apply]
  -- Mathlib describes stdAddChar x as a point of `Circle` viewed in ℂ.
  exact Circle.norm_coe _

/--
`e(x) = 1 ⇔ x = 0`. e is one-to-one and e(0) = 1, so e(x) = 1 = e(0) forces x = 0. We prove both directions.
`constructor` splits the goal into 2 directions, each handled by one bullet
-/
lemma e_eq_one_iff (x : ZMod p) : e x = 1 ↔ x = 0 := by
  constructor
  · intro h
    -- Injectivity: to show x = 0 it suffices to show stdAddChar x = stdAddChar 0.
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_zero_eq_one]
    exact h
  · intro h
    rw [h, e_zero]




/-!
`e*(x) = e(-x)` is proved here, where * represents complex conjugate.
e(x)·e(-x) = e(0) = 1, and e*(x)·e(x) = ∣e(x)∣² = 1. So, e*(x) = e*(x)·(e(x)·e(-x)) = (e*(x)·e(x))·e(-x) = e(-x)
-/
lemma star_e (x : ZMod p) : star (e x) = e (-x) := by
  -- e(x)·e(-x) = e(x + (-x)) = e(0) = 1. (`← e_add` merges the product into one e.)
  have h1 : e x * e (-x) = 1 := by
    rw [← e_add, add_neg_cancel, e_zero]
  have h2 : star (e x) * e x = 1 := by
    simpa [norm_e] using Complex.conj_mul' (e x)
  calc star (e x) = star (e x) * (e x * e (-x)) := by rw [h1, mul_one]
    _ = (star (e x) * e x) * e (-x) := by ring
    _ = e (-x) := by rw [h2, one_mul]




/--
`If c ≠ 0 then S := ∑_x e(c·x) = 0`
Reindexing `x` by `x + 1` gives ∑ e(c(x + 1)) = S; factoring gives ∑ e(c(x + 1)) = e(c)·S. Thus,
(e(c) - 1)·S = 0 and e(c) ≠ 1, hence S = 0.
-/
lemma sum_e_mul_eq_zero {c : ZMod p} (hc : c ≠ 0) : ∑ x : ZMod p, e (c * x) = 0 := by
  -- Re-indexing along the bijection x ↦ x + 1 (`Equiv.addRight 1`) does not change the sum.
  -- `Fintype.sum_equiv σ f g h` : if f x = g (σ x) for all x, then ∑ f = ∑ g.
  have hshift : ∑ x : ZMod p, e (c * (x + 1)) = ∑ x : ZMod p, e (c * x) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x => by simp)
  -- Factor: e(c(x + 1)) = e(cx + c) = e(c)·e(cx), term by term.
  have hfactor : ∑ x : ZMod p, e (c * (x + 1)) = e c * ∑ x : ZMod p, e (c * x) := by
    -- Move e(c) inside the sum on the right.
    rw [Finset.mul_sum]
    -- Compare the two sums term by term; `?_` is the remaining term-wise goal.
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_add, mul_one, e_add]
    ring
  -- e(c) ≠ 1, since e(c) = 1 would force c = 0. (A proof of "≠" is a function to False.)
  have hne : e c ≠ 1 := fun h => hc ((e_eq_one_iff c).mp h)
  -- (e(c) - 1)·S = e(c)·S - S = (shifted sum) - S = S - S = 0.
  have key : (e c - 1) * ∑ x : ZMod p, e (c * x) = 0 := by
    rw [sub_mul, one_mul, ← hfactor, hshift, sub_self]
  -- A product is 0 only if a factor is 0; the first factor e(c) - 1 is not 0, so S = 0.
  exact (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hne)




/--
The geometric sum for both cases: `∑ₓ e(c·x) = p` if `c = 0`, and `0` otherwise.
-/
lemma sum_e_mul (c : ZMod p) : ∑ x : ZMod p, e (c * x) = if c = 0 then (p : ℂ) else 0 := by
  -- Split into the cases c = 0 and c ≠ 0 (the case hypothesis is named hc).
  split_ifs with hc
  -- Case c = 0: every term is e(0) = 1, and there are p terms (`ZMod.card`).
  · subst hc
    simp [e_zero, ZMod.card]
  -- Case c ≠ 0: the previous lemma.
  · exact sum_e_mul_eq_zero hc





/-! ## The Quadratic Gauss sum -/

/--
Completing the square proof. If `2as = b`, then `for every x, ax² + bx = a(x + s)² - as²`
-/
lemma complete_square {a b s : ZMod p} (hs : 2 * a * s = b) (x : ZMod p) :
    a * x ^ 2 + b * x = a * (x + s) ^ 2 - a * s ^ 2 := by
  -- Replace b by 2as, then both sides expand to the same polynomial.
  rw [← hs]
  ring




/-- The pure Gauss sum `G(a) = ∑_y e(a·y²) = ∑_y ω^(a·y²) where y ∈ ℤ_p`. -/
def G (a : ZMod p) : ℂ := ∑ y : ZMod p, e (a * y ^ 2)



/--
`If 2 ≠ 0 in ℤ_p and a ≠ 0, then G*(a)·G(a) = p.`
G*·G = ∑_z ∑_y e(a(y² - z²)) = ∑_z ∑_t e(at²)·e(2atz) = ∑_t e(at²)·∑_z e(2at·z) = ∑_t e(at²)·(p if 2at = 0, else 0) = p
Only t = 0 survives because 2a ≠ 0 and t ≠ 0, giving 2at ≠ 0.
-/
lemma star_G_mul_G (hp2 : (2 : ZMod p) ≠ 0) {a : ZMod p} (ha : a ≠ 0) : star (G a) * G a = p := by
  -- 2a ≠ 0: no zero divisors in ZMod p (this is where primality is used), and p is odd.
  have h2a : (2 : ZMod p) * a ≠ 0 := mul_ne_zero hp2 ha
  -- expand G*·G into the double sum ∑_z ∑_y e(a(y² - z²)).
  have step1 : star (G a) * G a
      = ∑ z : ZMod p, ∑ y : ZMod p, e (a * (y ^ 2 - z ^ 2)) := by
    -- Unfold G, conjugate the sum term by term, multiply the two sums out.
    rw [G, star_sum, Finset.sum_mul_sum]
    -- Compare the double sums term by term.
    refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun y _ => ?_))
    -- conj(e(az²))·e(ay²) = e(-az²)·e(ay²) = e(-az² + ay²).
    rw [star_e, ← e_add]
    -- compare the exponents.
    congr 1
    ring
  -- for each z, substitute y = z + t, using (z + t)² - z² = t² + 2zt.
  have step2 : ∀ z : ZMod p, ∑ y : ZMod p, e (a * (y ^ 2 - z ^ 2))
      = ∑ t : ZMod p, e (a * t ^ 2) * e (2 * a * t * z) := by
    intro z
    -- Put the t-sum on the left so that re-indexing goes from t to y = z + t.
    symm
    -- Re-index along t ↦ z + t; it remains to match the terms.
    apply Fintype.sum_equiv (Equiv.addLeft z)
    intro t
    simp only [Equiv.coe_addLeft]
    rw [← e_add]
    congr 1
    ring
  -- Now: ∑_z ∑_t e(at²)·e(2atz) = p.
  rw [step1]
  -- `simp_rw` can rewrite inside the outer sum, where `rw` cannot.
  simp_rw [step2]
  -- Swap the order of summation: ∑_t ∑_z.
  rw [Finset.sum_comm]
  -- Pull e(at²) out of the inner sum, then evaluate the inner geometric sum with c = 2at.
  simp_rw [← Finset.mul_sum, sum_e_mul]
  -- Only the term t = 0 survives; this leaves three goals.
  rw [Finset.sum_eq_single (0 : ZMod p)]
  -- Goal 1, the t = 0 term: e(0)·p = p.
  · simp [e_zero]
  -- Goal 2, every t ≠ 0 term vanishes, because 2a·t ≠ 0.
  · intro t _ ht
    rw [if_neg (mul_ne_zero h2a ht), mul_zero]
  -- Goal 3, "0 is not an index" is impossible: the sum runs over all of ZMod p.
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `|G(a)|² = p` as a real number ∈ ℝ, from the complex identity `G*·G = |G|² = p`. -/
lemma norm_G_sq (hp2 : (2 : ZMod p) ≠ 0) {a : ZMod p} (ha : a ≠ 0) : ‖G a‖ ^ 2 = (p : ℝ) := by
  -- First as complex numbers: |G|² = conj(G)·G = p
  have h : ((‖G a‖ : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.conj_mul']
    exact star_G_mul_G hp2 ha
  -- Viewing reals inside ℂ does not identify different reals, so the equality holds in ℝ
  exact_mod_cast h

/--
Completing the square inside the sum  with `s = b·(2a)⁻¹`, gives `∑ₓ e(a x² + b x) = e(-a s²) · G(a)`.
We write the constant as `b²(4a)⁻¹ = a s²`, as they represent the same thing -/
lemma quad_sum_eq (hp2 : (2 : ZMod p) ≠ 0) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ∑ x : ZMod p, e (a * x ^ 2 + b * x) = e (-(a * (b * (2 * a)⁻¹) ^ 2)) * G a := by
  -- s = b(2a)⁻¹ satisfies 2a·s = b. This needs 2a ≠ 0: here oddness of p is used
  have hs : 2 * a * (b * (2 * a)⁻¹) = b := by
    have h : (2 * a) * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hp2 ha)
    -- Goal minus (b times h) is a polynomial identity, checked by `ring`
    linear_combination b * h
  -- Each term factors e(ax² + bx) = e(-as²)·e(a(x + s)²)
  have hterm : ∀ x : ZMod p, e (a * x ^ 2 + b * x)
      = e (-(a * (b * (2 * a)⁻¹) ^ 2)) * e (a * (x + b * (2 * a)⁻¹) ^ 2) := by
    intro x
    rw [← e_add, complete_square hs x]
    congr 1
    ring
  -- Rewrite every term and pull the constant e(-as²) out of the sum
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  -- It remains to show ∑ₓ e(a(x + s)²) = G(a)
  congr 1
  rw [G]
  -- Re-index along the shift x ↦ x + s
  exact Fintype.sum_equiv (Equiv.addRight (b * (2 * a)⁻¹)) _ _ (fun x => by simp)

/--
The Gauss sum estimate. that is for `a ≠ 0` and `p` odd, `|∑ₓ e(a x² + b x)|² = p`
The prefactor `e(-as²)` has size 1, and `|G(a)|² = p`
-/
lemma norm_sq_quadratic_sum (hp2 : (2 : ZMod p) ≠ 0) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ‖∑ x : ZMod p, e (a * x ^ 2 + b * x)‖ ^ 2 = (p : ℝ) := by
  -- |e(-as²)·G| = |e(-as²)|·|G| = 1·|G| = |G|
  rw [quad_sum_eq hp2 ha b, norm_mul, norm_e, one_mul]
  exact norm_G_sq hp2 ha

/-!
Mathlib labels the rows and columns of a `p × p` matrix by `Fin p = {0, …, p-1}`, while the arithmetic of the construction happens in `ZMod p`.
The map `toZ` translates between the two, and the next lemmas show it is a perfect matching, so sums over rows equal sums over `ZMod p`.
`toZ(i) = i mod p, for a label i ∈ {0...p-1}`
-/
def toZ (i : Fin p) : ZMod p := (i : ℕ)

/--
`If toZ(i) = toZ(j) then i = j` because for a number below p, "reduce mod p" changes nothing. So i = (i mod p) = (j mod p) = j
-/
lemma toZ_injective : Function.Injective (toZ : Fin p → ZMod p) := by
  intro i j h
  apply Fin.ext
  -- Take representatives (`.val`, a natural number below p) of both sides of h
  have h' : (toZ i).val = (toZ j).val := by rw [h]
  -- For n < p the representative of (n mod p) is n itself; `rwa` = rewrite, then use h'
  rwa [toZ, toZ, ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at h'

/-!
toZ is a bijection (one-to-one mapping), so for any function f, `∑_{i=0}^{p-1} f(toZ(i)) = ∑_{x ∈ ℤ_p} f(x)`
-/
lemma toZ_bijective : Function.Bijective (toZ : Fin p → ZMod p) := by
  rw [Fintype.bijective_iff_injective_and_card]
  -- ⟨injective, equal sizes⟩; `ZMod.card` says ZMod p has p elements
  exact ⟨toZ_injective, by simp [ZMod.card]⟩

/--
Summing over row labels is the same as summing over `ZMod p`:
`∑_{i < p} f(toZ i) = ∑_{x ∈ ℤ_p} f(x)`. This bridges matrix products and the sums above.
-/
lemma sum_fin_toZ (f : ZMod p → ℂ) : ∑ i : Fin p, f (toZ i) = ∑ x : ZMod p, f x :=
  toZ_bijective.sum_comp f



/--
The normalising factor `1/√p`, computed as a real number and viewed in `ℂ`.
-/
def nrm (p : ℕ) : ℂ := ((Real.sqrt p)⁻¹ : ℝ)

/-- `|1/√p|² = 1/p`. -/
lemma norm_nrm_sq : ‖nrm p‖ ^ 2 = (p : ℝ)⁻¹ := by
  -- |(√p)⁻¹|² = ((√p)⁻¹)² = ((√p)²)⁻¹ = p⁻¹, using p ≥ 0 for (√p)² = p.
  rw [nrm, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]


/-- `conj(1/√p) · (1/√p) = 1/p` in `ℂ`. -/
lemma star_nrm_mul_nrm : star (nrm p) * nrm p = (p : ℂ)⁻¹ := by
  -- conj(z)·z = |z|², viewed as a complex number.
  have h : star (nrm p) * nrm p = ((‖nrm p‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' (nrm p)
  rw [h, norm_nrm_sq]
  -- Viewing the real number p⁻¹ in ℂ gives the complex number p⁻¹
  exact Complex.ofReal_inv (p : ℝ)

/-! ## Ivanović matrices and the three cases -/

/--
The matrix `U_a`: `(U_a)_{i,j} = (1/√p)·ω^(a i² + j i)`.
Row `i` is the position `x`, column `j` is the label `b` of the basis vector, so column `j`
of `U_a` is the vector `v_{a,j}`. A matrix is a function of (row, column), hence `fun i j`.
-/
def ivMat (a : ZMod p) : Matrix (Fin p) (Fin p) ℂ :=
  fun i j => nrm p * e (a * toZ i ^ 2 + toZ j * toZ i)



/--
We restate the formula as a named fact (true by definition, rfl) so later proofs can rewrite it
-/
lemma ivMat_apply (a : ZMod p) (i j : Fin p) :
    ivMat a i j = nrm p * e (a * toZ i ^ 2 + toZ j * toZ i) := rfl



/--
`The overlap formula : (U_a† U_c)_jk = (1/p)·∑_(x ∈ ℤ_p) e((c-a)x² + (k - j)x)`
We find the overlap between any two vectors in this fashion
-/
lemma relEntry (a c : ZMod p) (j k : Fin p) : (star (ivMat a) * ivMat c) j k = (p : ℂ)⁻¹ * ∑ x : ZMod p, e ((c - a) * x ^ 2 + (toZ k - toZ j) * x) := by
  -- One term of the matrix product: conj((U_a)_{ij})·(U_c)_{ik} = (1/p)·e((c-a)i² + (k-j)i).
  have hterm : ∀ i : Fin p, star (ivMat a) j i * ivMat c i k
      = (p : ℂ)⁻¹ * e ((c - a) * toZ i ^ 2 + (toZ k - toZ j) * toZ i) := by
    intro i
    -- Entry (j, i) of U_a† is the conjugate of entry (i, j) of U_a.
    rw [Matrix.star_apply]
    -- Write out the entries; conjugate a product factor by factor; e*(A) = e(-A).
    simp only [ivMat_apply, star_mul', star_e]
    -- Regroup (u·v)·(w·z) = (u·w)·(v·z) so (nrm)*·nrm = 1/p, then merge the two e's.
    rw [mul_mul_mul_comm, star_nrm_mul_nrm, ← e_add]
    -- Peel off "p⁻¹ * _" and "e _", and compare the exponents.
    congr 2
    ring
  -- The full entry is the sum of these terms over the row label i.
  rw [Matrix.mul_apply]
  simp_rw [hterm]
  -- Pull 1/p out of the sum.
  rw [← Finset.mul_sum]
  congr 1
  -- Turn the sum over row labels into a sum over ZMod p.
  exact sum_fin_toZ (fun x => e ((c - a) * x ^ 2 + (toZ k - toZ j) * x))



/-- Case 1 :
each `U_a` is unitary, so its columns form a basis.
With `c = a` the `x²` term cancels: `(U_a† U_a)_{jk} = (1/p)·∑ₓ e((k-j)x) = δ_{jk}`.
-/
lemma ivMat_mem_unitary (a : ZMod p) : ivMat a ∈ Matrix.unitaryGroup (Fin p) ℂ := by
  -- p ≠ 0 as a complex number, to cancel p⁻¹·p = 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- Being unitary means U† U = I
  rw [Matrix.mem_unitaryGroup_iff']
  -- Two matrices are equal when every entry (j, k) agrees
  ext j k
  -- Overlap formula with c = a: a - a = 0 kills the x² term
  rw [relEntry, sub_self]
  simp only [zero_mul, zero_add]
  -- Geometric sum on the left; identity entry `if j = k then 1 else 0` on the right.
  rw [sum_e_mul, Matrix.one_apply]
  by_cases hjk : j = k
  -- Diagonal entry: k - j = 0, so (1/p)·p = 1.
  · subst hjk
    simp [hp0]
  -- Off-diagonal entry: k - j ≠ 0 because toZ is injective, so (1/p)·0 = 0.
  · have hne : toZ k - toZ j ≠ 0 :=
      sub_ne_zero.mpr (fun h => hjk (toZ_injective h).symm)
    rw [if_neg hne, if_neg hjk, mul_zero]


/-- `U_a` is written as a basis: the matrix together with its unitarity certificate. -/
def ivU (a : ZMod p) : UMat p := ⟨ivMat a, ivMat_mem_unitary a⟩



/-- Case 2 :
for `a ≠ c`, every overlap has squared size `1/p`:
`|(U_a† U_c)_{jk}|² = (1/p)²·|Gauss sum|² = (1/p)²·p = 1/p`, since `c - a ≠ 0`.
-/
lemma ivMat_unbiased (hp2 : (2 : ZMod p) ≠ 0) {a c : ZMod p} (hac : a ≠ c) (j k : Fin p) :
    ‖(star (ivMat a) * ivMat c) j k‖ ^ 2 = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- |p⁻¹·S|² = |p⁻¹|²·|S|² = |p⁻¹|²·p (Gauss sum with leading coefficient c - a ≠ 0)
  -- = (p⁻¹)²·p = p⁻¹·(p⁻¹·p) = p⁻¹.
  rw [relEntry, norm_mul, mul_pow,
    norm_sq_quadratic_sum hp2 (sub_ne_zero.mpr hac.symm), norm_inv,
    Complex.norm_natCast, sq, mul_assoc, inv_mul_cancel₀ hp0, mul_one]



/--
`U_a` and `U_c` are unbiased when `a ≠ c`.
`relativeUnitary (ivU a) (ivU c)` is by definition `U_a† U_c`, so Lean accepts the previous lemma after unfolding definitions. -/
lemma isUnbiased_ivU (hp2 : (2 : ZMod p) ≠ 0) {a c : ZMod p} (hac : a ≠ c) : IsUnbiased (ivU a) (ivU c) := by
  intro j k
  exact ivMat_unbiased hp2 hac j k



/-- Case 3 :
the standard basis `I` is unbiased to every `U_c`.
`I† U_c = U_c`, and every entry has squared size `|1/√p|²·|e(…)|² = 1/p`.
-/
lemma isUnbiased_one_ivU (c : ZMod p) : IsUnbiased (1 : UMat p) (ivU c) := by
  intro j k
  -- The overlap matrix of the identity with U_c is U_c itself.
  have h1 : relativeUnitary (1 : UMat p) (ivU c) = ivMat c := by
    simp [relativeUnitary, ivU]
  -- |nrm·e(…)|² = |nrm|²·|e(…)|² = |nrm|²·1 = 1/p.
  rw [h1, ivMat_apply, norm_mul, mul_pow, norm_e, one_pow, mul_one, norm_nrm_sq]

/-! ## Counting the p + 1 bases and the final theorems -/



/--
If Bases B_ι are labelled by the elements of a finite set ι and are pairwise unbiased, then there are ∣ι∣ pairwise unbiased bases
`HasMUBs` wants the bases numbered `0, …, k-1`; here we renumber the labels
-/
lemma hasMUBs_of_fintype {d : ℕ} {ι : Type*} [Fintype ι] (B : ι → UMat d) (hB : Pairwise fun i j => IsUnbiased (B i) (B j)) :
    HasMUBs d (Fintype.card ι) := by
  -- σ sends the number n to the n-th label (a bijection Fin |ι| ≃ ι from Mathlib's numbering).
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  -- Witness for "there exists": basis number n is B(σ n). The hole: it is pairwise unbiased.
  refine ⟨fun n => B (σ n), ?_⟩
  intro m n hmn
  -- σ is injective, so m ≠ n gives σ m ≠ σ n, and hB applies.
  exact hB (fun h => hmn (σ.injective h))



/--
The `p + 1` bases with their natural labels. `Option (ZMod p)` is `ZMod p` plus one extra
label `none`, playing the role of the notes' `B_∞` (the standard computational basis).
-/
def family : Option (ZMod p) → UMat p
  | none => 1
  | some a => ivU a



/--
All `p + 1` bases are pairwise unbiased. For labels `i ≠ j` there are four shapes:
(∞, ∞) is impossible, (∞, c) is Case 3, (a, ∞) is Case 3 by symmetry, (a, c) with `a ≠ c` is Case 2.
-/
lemma family_pairwise (hp2 : (2 : ZMod p) ≠ 0) :
    Pairwise fun i j : Option (ZMod p) => IsUnbiased (family i) (family j) := by
  intro i j hij
  -- Split on the shape of i, then of j.
  cases i with
  | none =>
    cases j with
    -- none ≠ none contradicts rfl : none = none.
    | none => exact absurd rfl hij
    | some c => exact isUnbiased_one_ivU c
  | some a =>
    cases j with
    -- Symmetry of unbiasedness (dot notation for `IsUnbiased.symm`).
    | none => exact (isUnbiased_one_ivU a).symm
    -- From some a ≠ some c get a ≠ c: if a = c then `congrArg some` gives some a = some c.
    | some c => exact isUnbiased_ivU hp2 (fun h => hij (congrArg some h))



/--
`If p is prime and p ≠ 2, then ℂᵖ has p + 1 pairwise unbiased bases`
The family defined above has |Option(ℤ_p)| = p + 1 members, pairwise unbiased.
-/
theorem hasMUBs_odd_prime (hp2 : p ≠ 2) : HasMUBs p (p + 1) := by
  -- Renumber the family. `(p := p)` names the implicit argument, which Lean cannot guess here.
  have h := hasMUBs_of_fintype (family (p := p)) (family_pairwise (two_ne_zero_of_ne_two hp2))
  -- |Option (ZMod p)| = |ZMod p| + 1 = p + 1.
  rwa [Fintype.card_option, ZMod.card] at h

/-- **The Main Theorem : N(p) = p + 1**
For every prime `p ≠ 2`. `IsMaxMUBCount p (p + 1)` has two halves: `p + 1` unbiased bases exist (`hasMUBs_odd_prime`, proved above),
and no family has more than `p + 1` members. The second half is the universal ceiling `N(d) ≤ d + 1` from `MUBsFormalization.lean`; it is passed in as `ub` (supply `MUBUpperBound.mub_upper_bound` for it).
Thus, we conclude that N(p) = p + 1
-/
theorem isMaxMUBCount_odd_prime (hp2 : p ≠ 2)
    (ub : ∀ m : ℕ, HasMUBs p m → m ≤ p + 1) : IsMaxMUBCount p (p + 1) := ⟨hasMUBs_odd_prime hp2, ub⟩


end Prime

end MUBPrime
