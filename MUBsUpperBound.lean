import Mathlib

/-
# The upper bound N(d) ≤ d + 1, via shifted projectors
-/

noncomputable section
/-
`noncomputable section` means we are not interested in computational outputs,
but only in mathematical statements and proofs. Lean will not try to compute anything.
-/

set_option linter.style.longLine false
/-
disabled warning for long lines, just annoying
-/
namespace MUBUpperBound

/--
A `d ⨯ d unitary matrix U`, and every such matrix represents any 1 complete
orthonormal basis of ℂ^d. Each column represents one of the basis vectors.
It is bundled with proof of its unitarity, i.e. `U†U = I`.
`Matrix.unitaryGroup (Fin d) ℂ` is the type of all unitary matrices of size d ⨯ d.
-/
abbrev UMat (d : ℕ) := ↑(Matrix.unitaryGroup (Fin d) ℂ)

/-
The ↑ symbol turns a set into a type. It means any element of that type
is a unitary matrix and certificate that it is unitary.
-/


/--
the relative unitary U V = U† V is another matrix, whose `(j,k)-th entry`
is the inner product, `<u_j | v_k>`. So, overlap of all basis vectors of one
basis with all basis vectors of another basis is acccomplished here.
-/
def relativeUnitary {d : ℕ} (U V : UMat d) : Matrix (Fin d) (Fin d) ℂ :=
    star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)

/-
`(star U) i k = conj (U k i)` and so it works
-/

/--
Two bases `U and V are mutually unbiased` if every overlap, that is every entry
of the `relative unitary` matrix defined above, has `modulus squared equal to '1/d'`
-/
def IsUnbiased {d : ℕ} (U V : UMat d) : Prop :=
  ∀ i j : Fin d, ‖relativeUnitary U V i j‖ ^ (2 : ℕ) = (d : ℝ)⁻¹

/-
`Prop` is Lean's type of mathematical statements, things that
can be true or false and can be proved.
-/



/--
A family of `k` bases in which every two distinct members are mutually unbiased
-/
def IsMUBFamily {d k : ℕ} (B : Fin k → UMat d) : Prop :=
    Pairwise fun a b => IsUnbiased (B a) (B b)

/-
`B` is function from k to unitary matrices, like indexing the MUBs
`Pairwise R` means for all a and b, a ≠ b, R a b holds.
So, every two distinct bases are mutually unbiased.
-/


/--
There exists `k mutually unbiased bases in ℂ^d`
-/
def HasMUBs (d k : ℕ) : Prop :=
    ∃ B : Fin k → UMat d, IsMUBFamily B



/--
Defining the projector `|u_j><u_j|`, which comes from j-th column of unitary
matrix U, and is a d ⨯ d matrix. `(|u_j><u_j|)_{i,l} = U_{i,j} * conj(U_{l,j}`
-/
def proj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
        Matrix.of fun i l => U i j * star (U l j)

/-
`Matrix.of` supplies a recipe to fill the elements of the matrix by a function,
in our case that is, U_{i,j} * conj(U_{l,j})
-/


/--
Simp tactic is for simplification, to replace complicated expressions with easy ones.
Whenever simp sees `proj U j i l` in a goal, it automatically
replaces it with `U i j * star (U l j)`
-/
@[simp] lemma proj_apply {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (j i l : Fin d) :
    proj U j i l = U i j * star (U l j) := rfl

/-
`rfl` means reflexivity, or LHS = RHS, proof of equality.
-/

/-! # The trace identities -/



/--
`Tr |u_j><u_j| = <u_j|u_j>` is written as diagonal `entry (j,j) of U†U`
-/
lemma trace_proj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    (proj U j).trace = (star U * U) j j := by
    simp only [Matrix.trace, Matrix.diag, proj_apply, Matrix.mul_apply, Matrix.star_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-
`Finset.sum_congr` means two sums are equal if they run over
the same set and their terms are equal one by one.
`exact` means the proof is complete, no further steps needed.
`simp only[...]`  rewrites the goal only using the facts given in the list.
Use `simp?` [with only ones you can think of] to get suggestion from Lean itself
-/


/--
Proof of the identity Tr(P_i P_j) = |<u_i|u_j>|^2,
where P_i = |u_i><u_i| and P_j = |u_j><u_j|
-/
lemma trace_proj_mul_proj {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    (proj U j * proj V k).trace = star ((star U * V) j k) * ((star U * V) j k) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, proj_apply, Matrix.star_apply, star_sum, star_mul, star_star]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring

/-
`rw` means rewrite, here (∑ a_i)*b = ∑ (a_i * b)
`simprw` just means the converse of the last rewrite.
To show two double sums are equal, it's enough to show their terms match for every i and l.
The outer `sum_congr` handles the i-sum and the inner one handles the l-sum;
rfl says both sides sum over the same indices.
`?_` leaves the single remaining job, proving "term (i, l) on the left = term (i, l) on the right",
as a new goal for ring to finish.
`ring` means these terms follow ordinary commutative algebra rules
so we can rearrange them to match the goal.
-/


/--
For a complex number, |z|^2 = z * conj (z)
-/
lemma star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw[Complex.ofReal_pow]
    simpa using Complex.conj_mul' z

/-
`rw` means rewrite, to say that x^n is complex, same as (x^n : ℂ) = (x : ℝ)^n
`simpa` means simplify and then apply a lemma, in this case `Complex.conj_mul' z`
which says conj(z) * z = |z|^2
-/

/-! # The Shifted Projectors -/

/--
Shifted projectors are defined as P' = P - I/d,
where P is the projector |u_j><u_j| and I is the identity matrix.
-/
def shiftedProj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
        proj U j - (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)

/-
The identity matrix is written as `(1 : Matrix (Fin d) (Fin d) ℂ)`)
-/





/-- Proving shifted projectors are traceless, `Tr P' = 0` -/
lemma trace_shiftedProj {d : ℕ} (hd : (d : ℂ) ≠ 0) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : star U * U = 1) (j : Fin d) : (shiftedProj U j).trace = 0 := by
  rw [shiftedProj, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    trace_proj, hU, Matrix.one_apply_eq, smul_eq_mul, inv_mul_cancel₀ hd, sub_self]

/-
hd is hypothesis (any prefix h is like hypothesis) that d ≠ 0
Since we don't want to deal with fractions because in ℕ 1/d would be 0, we typecast to ℂ
Similarly, hU represents hypothesis that U is unitary, i.e. U†U = I
-/
/-
rw again is rewrite (like steps of any calculation). `Matrix.trace_sub` means Tr(A - B) = TrA - TrB
`Matrix.trace_smul` means Tr(c • A) = c * Tr(A), `Matrix.trace_one` means Tr(I) = d,
`Fintype.card_fin` means the number of elements in Fin d is d, `Matrix.one_apply_eq` means
diagonal entry of I is 1, `smul_eq_mul` means for numbers, c • A = c * A,
`inv_mul_cancel₀ hd` means 1/d * d = 1, and `sub_self` means x - x = 0
-/

/-- Proving `Tr(P' Q') = Tr(P Q) − 1/d`. -/
lemma trace_shiftedProj_mul {d : ℕ} (hd : (d : ℂ) ≠ 0) {U V : Matrix (Fin d) (Fin d) ℂ}
    (hU : star U * U = 1) (hV : star V * V = 1) (j k : Fin d) :
    (shiftedProj U j * shiftedProj V k).trace = (proj U j * proj V k).trace - (d : ℂ)⁻¹ := by
  have hPU : (proj U j).trace = 1 := by rw [trace_proj, hU, Matrix.one_apply_eq]
  have hPV : (proj V k).trace = 1 := by rw [trace_proj, hV, Matrix.one_apply_eq]
  simp only [shiftedProj, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
             Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, hPU, hPV, smul_eq_mul]
  linear_combination (d : ℂ)⁻¹ * inv_mul_cancel₀ hd

/-
hU and hV are hypotheses that U and V are unitary, i.e. U†U = I and V†V = I
The goal is  `(shiftedProj U j * shiftedProj V k).trace = (proj U j * proj V k).trace - (d : ℂ)⁻¹`
which translates to Tr(P'_U(j) P'_V(k)) = Tr(P_U(j) P_V(k)) - 1/d
`have hPU` and `have hPV` are smaller helper facts that prove Tr(P_U(j)) = 1 and Tr(P_V(k)) = 1
-/

/-!
# Detailed explanation of how the simp only works, to understand Lean version of an analytical proof
Say, P_U(j) = P, P_V(k) = Q, and c = 1/d.
(P - cI)(Q - cI) is unfolded by shiftedProj definition
= PQ - P(cI) - (cI)Q + (cI)(cI) is unfolded by sub_mul (a-b)c = ac - bc & mul_sub a(b-c) = ab - ac
= PQ - cP - cQ + c^2 I : smul_mul_assoc (c • A)B = c • (AB), mul_smul_comm A(c • B) = c • (AB), one_mul I = I, mul_one A = A
Tr(PQ - cP - cQ + c^2 I) = Tr(PQ) - cTr(P) - cTr(Q) + c^2 Tr(I)
given by Matrix.trace_sub Tr(A-B) = Tr(A) - Tr(B), Matrix.trace_smul Tr(cA) = cTr(A), Matrix.trace_one Tr(I) = d
Tr(P) = Tr(Q) = 1, given by hPU and hPV
Ultimately, We have Tr(PQ) - c - c + c^2 d,
To prove c.d = 1, we use linear_combination (d : ℂ)⁻¹ * inv_mul_cancel₀ hd, which means 1/d * d = 1
-/







/-! ## The Gram matrix of shifted projectors -/

/-- For two shifted projectors from the same basis, `Tr(P'_x(j) P'_x(k)) = δ_{jk} − 1/d`.
where P'_x(j) is the shifted projector of j-th basis vector of x-th basis.
-/
lemma gram_same {d : ℕ} (hd : (d : ℂ) ≠ 0) {U : Matrix (Fin d) (Fin d) ℂ} (hU : star U * U = 1) (j k : Fin d) :
    (shiftedProj U j * shiftedProj U k).trace = (if j = k then 1 else 0) - (d : ℂ)⁻¹ := by
  rw [trace_shiftedProj_mul hd hU hU, trace_proj_mul_proj, hU, Matrix.one_apply]
  split_ifs <;> simp

/-
We already proved `Tr(P'_x(j) P'_x(k)) = Tr(P_x(j) P_x(k)) − 1/d` in lemma trace_shiftedProj_mul
Now, we also know `Tr (P_i P_j) = |<u_j|u_k>|^2 = δ_{jk}` for same basis, which is proved in lemma trace_proj_mul_proj
`split_ifs splits the goal into two cases, one for j = k and one for j ≠ k, and then simp simplifies both cases
`<;>` means apply the tactic on the left to all goals generated by the tactic on the right
-/

/-
`simp` tries to simplify the goal using facts in the list, and works mostly on pattern matching
It tries to apply all facts everywhere until it cannot simplify anymore.
`simp only` means use only the facts that is provided by me in the list, otherwise it can use other facts from lean
`rw` is more sequential. It applies facts in the order they are given. Each rule used exactly once.
We can use `simp [*]` but it is slow, based on pure guesswork, with no guarantee that it follows what is there in your analytical proof.
-/




/-- Two different (unbiased) bases: `Tr(P'_a(j) P'_b(k)) = 0`.
where P'_a and P'_b are shifted projectors of a-th and b-th bases.
-/
lemma gram_unbiased {d : ℕ} (hd : (d : ℂ) ≠ 0) {U V : UMat d} (hUV : IsUnbiased U V) (j k : Fin d) :
    (shiftedProj (U : Matrix (Fin d) (Fin d) ℂ) j * shiftedProj (V : Matrix (Fin d) (Fin d) ℂ) k).trace = 0 := by
  rw [trace_shiftedProj_mul hd (Matrix.UnitaryGroup.star_mul_self U) (Matrix.UnitaryGroup.star_mul_self V),
      trace_proj_mul_proj, star_mul_self_eq_norm_sq]
  have h : ‖(star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)) j k‖ ^ 2
      = (d : ℝ)⁻¹ := hUV j k
  rw [h]
  simp

/-
`hUV` is a hypothesis that U and V are mutually unbiased. Unitarity is a property of the bases but not the projectors.
So far, we did not use the IsUnbiased property, which requires unitarity of matrices U, V and thus UMat d
The projector algebra is kept general for all matrices, to use the readymade Mathlib Matrix properties conveniently.
Here, we use the IsUnbiased property. And we typecast using `Matrix.UnitaryGroup.star_mul_self U` to get the unitarity of U and V,
which is required for trace_shiftedProj_mul in the rw tactic.
-/
/-
`have h : ...` line means we have a helper fact that the modulus squared of the (j,k)-th entry of the relative unitary is 1/d,
which is exactly the definition of IsUnbiased property.
`rw[h]` replaces |r|^2 with 1/d for the goal and simplifies by simp tactic to zero.
-/



/-! ## The trace pairing as a linear map -/

/--
For a fixed matrix X, we define a function pairWith_X (A) = Tr (A · X)
It measures the overlap of any matrix A with a fixed matrix X
`pairWith X` is the ℂ-linear map `A ↦ Tr(A X)`.
-/
def pairWith {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ where
      toFun A := (A * X).trace
      map_add' A B := by simp [add_mul, Matrix.trace_add]
      map_smul' c A := by simp [Matrix.trace_smul]

/-
Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ is the type of all ℂ-linear maps from d ⨯ d matrices to complex numbers.
`where` means "a linear map is a package; here are its parts :
1. function definition : `tofun A := (A * X).trace` means A ↦ Tr (A X)
2. proof of additivity that Tr ((A + B) X) = Tr (A X) + Tr (B X)
3. proof of scaling that Tr ((c • A) X) = c Tr (A X)
-/

/--
Like proj_apply, we define the simplification rule for pairWith, so that Lean knows how exactly to unpack pairWith if it sees it
-/
@[simp] lemma pairWith_apply {d : ℕ} (X A : Matrix (Fin d) (Fin d) ℂ) :
    pairWith X A = (A * X).trace := rfl




/-! ## The family we will prove linearly independent (here d = n + 2) -/


/-
All d × d complex matrices form a vector space of dimension d^2 over ℂ. So, atmost d^2 linearly independent vectors can exist.
Now, if we take the subspace of traceless matrices, then the dimension is d^2 - 1, because trace = 0 supplies a linear condition
Any projector is basically, P = P' + I/d, where P' is traceless shifted projector and I is identity matrix.
Let's say we have 'm' bases, B_0, B_1,... B_{m-1}. And, all projectors are defined as d × d matrices over ℂ
Thus, the total dimensionality of (identity + shifted projectors) is m(d-1) + 1.
Why (d - 1), because ∑_i P'_x(i) = 0, so only (d - 1) shifted projectors are linearly independent for each basis.
Now, very clearly, this total dimensionality of identity + shifted projectors is less or equals to dimensionality of all d × d complex matrices.
So, 1 + m·(d - 1) ≤ d^2, or, m·(d - 1) ≤ d^2 - 1, or, m ≤ (d^2 - 1)/(d - 1) = d + 1
Thus, upper bound on the number of mutually unbiased bases is m ≤ d + 1.
-/

/-
In our code, we have defined d as a natural number, d : ℕ. In Lean, 0 - 1 = 0 for natural numbers, so (d - 1) must be 1 or more.
Moreover, we are concerned only for d = 2 (qubit) and beyond, that is we can fix, d ≥ 2. So, any d ≥ 2 can be written as d = n + 2, where n : ℕ
In Lean, the set of natural numbers ℕ runs from 0, 1, 2, 3,... and so on.
-/

/-- Index `none` gives the identity. Index `some (a, j)` gives `P'_a(j)` for `j = 0, …, d − 2`.
The last shifted projector of each basis is left out, because it equals minus the sum of the others.
`B` is the family of all 'm' MUBs and gives a dxd complex matrix.
`family` is a function from labels to matrices. Fin m represents basis index, Fin (n + 1) represents projector number
Now, `Option` keyword looks at all basis-projector combinations and gives corresponding matrix as output.
The `none` label gives identity matrix as output.
-/
def family {n m : ℕ} (B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    Option (Fin m × Fin (n + 1)) → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ
  | none => 1
  | some p => shiftedProj (B p.1) (Fin.castSucc p.2)



/--
Let g be any choice of coeffecients, g_{none} for identity and g_{a,j} for each shifted projector. Let F be the family of matrices.
`Tr ((∑_x g_x F_x)· P'_{b,k}) = g_{b,k} - (1/d)∑_j g_{b,j}`, because by applying linearity of trace on the LHS, we get,
`g_{none}· Tr(I·P'_{b,k}) + ∑_a ∑_j g_{a,j} · Tr(P'_{a,j}·P'_{b,k})`
First term goes to zero as shifted projectors are traceless, and for every basis a ≠ b, the second term is zero by lemma gram_unbiased
So, only for a = b, our sum survives. `Tr(P'_{a,j}·P'_{a,k}) = δ_{j,k} - 1/d`. Thus, our sum becomes,
`Tr(M·P'_{b,k}) = g_{b,k} - (1/d)∑_j g_{b,j}, where M = g_{none} I + ∑_a ∑_j g_{a,j} P'_{a,j}`
-/
lemma pairWith_shifted_family {n m : ℕ}
    (B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hB : ∀ a, star (B a) * B a = 1)
    (hOrth : ∀ a b, a ≠ b → ∀ j k, (shiftedProj (B a) j * shiftedProj (B b) k).trace = 0)
    (g : Option (Fin m × Fin (n + 1)) → ℂ) (b : Fin m) (k : Fin (n + 1)) :
    pairWith (shiftedProj (B b) (Fin.castSucc k)) (∑ x, g x • family B x)
      = g (some (b, k)) - (∑ j, g (some (b, j))) * ((n + 2 : ℕ) : ℂ)⁻¹ := by
  have hd : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [map_sum, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [map_smul, smul_eq_mul, pairWith_apply, family, one_mul,
    trace_shiftedProj hd (hB b), mul_zero, zero_add]
  rw [Finset.sum_eq_single b]
  · -- the surviving term, a = b
    simp only [gram_same hd (hB b), Fin.castSucc_inj]
    simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  · -- every other basis contributes zero
    intro a _ hab
    simp only [hOrth a b hab, mul_zero, Finset.sum_const_zero]
  · -- b is in Finset.univ, so this case cannot happen
    intro hb
    exact absurd (Finset.mem_univ b) hb


/-
For us d = n + 2. m is the number of bases. B : m matrices of size (n + 2)⨯(n + 2). hB is hypothesis that every B_a is unitary (orthonormal columns).
hOrth is hypothesis that for separate MUBs (a≠B), the gram_unbiased lemma is satisfied. Trace of product of the shifted projectors = 0 for a ≠ b
g again represents the family of coeffecients, one complex number for each label {b,k}
`have hd...` line converts d from ℕ to ℂ and says if in ℕ something is non-zero, it remains in ℂ non-zero as well. `omega` is automatic solver for ℕ, `.mpr` means go right to left
`map_sum` makes f(∑ x) = ∑ f(x), `Fintype.sum_option` makes sum over all labels- a none term + some p, `Fintype.sum_prod_type` means ∑_{a,j} = ∑_a ∑_j
The simp only reduces goal to `∑ a ∑ j g (some (a, j)) * (P' a j * P' b k).trace  = RHS = g (some b, k) - (1/d)∑_j some(b, j)
bullets - each bullet represents one goal, in this case when same bases a = b, different a ≠ b and 3rd case for completeness.
`absurd` means if h1 proves a statement P and h2 proves 'not P', then absurd h1 h2 proves any goal.
-/





/-- Pair a linear combination of the family with the identity (take the trace).
Every shifted projector is traceless, so only the identity's coefficient survives.
`Tr((∑_x g_x F_x)·I) = g_none · Tr(I) + ∑_{a,j} g_{a,j} · Tr(P'_{a,j}) = g_{none}·d + 0`
-/
lemma pairWith_one_family {n m : ℕ}
    (B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hB : ∀ a, star (B a) * B a = 1) (g : Option (Fin m × Fin (n + 1)) → ℂ) :
    pairWith 1 (∑ x, g x • family B x) = g none * ((n + 2 : ℕ) : ℂ) := by
  have hd : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsp : ∀ (a : Fin m) (j : Fin (n + 2)), (shiftedProj (B a) j).trace = 0 :=
    fun a j => trace_shiftedProj hd (hB a) j
  rw [map_sum, Fintype.sum_option]
  simp only [map_smul, smul_eq_mul, pairWith_apply, family, mul_one, hsp, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.trace_one, Fintype.card_fin]

/-
`hsp` is the hypothesis that every shifted projector is traceless.
`fun a j => trace_shiftedProj hd (hB a) j` prepares a map with proof of the tracelessness with indices a & j for every projector
`map_sum` again splits into sum of 'none' term + 'some' terms
the simp only simplifies into the final state g_{none}·(n + 2) on both sides
-/



/--
If each of n + 1 complex numbers is equal to their total divided by n + 2, then the total is (n + 1)/(n + 2) of itself.
The only number equal to a fraction of itself is zero.
Let x_0,...,x_n be n + 1 complex numbers and S = ∑_k x_k, and d = n + 2. If x_k = S/d, for every k, then every x_k = 0.
Proof- If all x_k = S/d, then S = (n + 1).S/d, or, dS = (n + 2)S = (n + 1)S. Thus, S = 0. So, x_k = 0.
-/
lemma eq_zero_of_eq_sum_mul_inv {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : ∀ k, x k = (∑ j, x j) * ((n + 2 : ℕ) : ℂ)⁻¹) : ∀ k, x k = 0 := by
  have hd : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hS : ∑ j, x j = 0 := by
    have h1 : ∑ k, x k = ∑ _k : Fin (n + 1), (∑ j, x j) * ((n + 2 : ℕ) : ℂ)⁻¹ :=
      Finset.sum_congr rfl (fun k _ => hx k)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hc : ((n + 2 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
    push_cast at h1 hc
    linear_combination ((n : ℂ) + 2) * h1 + ((n : ℂ) + 1) * (∑ j, x j) * hc
  intro k
  rw [hx k, hS, zero_mul]

/-
`x : Fin (n + 1) → ℂ` is a list of n + 1 complex numbers and d ≠ 0
Finset.sum_congr means the termwise equal ⇒ sums equal
`_ k`: on the right says the summand S/d doesn't depend on k. The underscore just says 'this variable isn't used'.
`push_cast` moves the casts from ℕ to ℂ inward: ↑(n + 1) becomes ↑n + 1, and ↑(n + 2) becomes ↑n + 2.
`intro k` is used to introduce temporary dummy variables, indices.
`linear_combination` step is the multiply by (n + 2)S and subtract (n + 1)S step.
-/




/-! ## Linear independence -/


/-! # If d ≥ 2 and there are 'm' mutually unbiased bases of ℂ^d, then m ≤ d + 1 (MAIN THEOREM) -/


/--
The Family F is identity I + Q_aj where a = 0,...,m - 1 and j = 0,...,d - 2. Q_aj = P_aj - I/d (shifted projector)
`The Claim is these 1 + m(d - 1) matrices are linearly independent, that is if g_{none} I + ∑_a ∑_j g_aj Q_aj = 0, then every g_aj = 0`
How to read off every coefficient? By taking trace of the Hilbert-Schmidt inner product of the corresponding shifted projector with a reference matrix X, as in `pairWith lemma`
If we pair members of the same family (that is X composed of elements of Family F), we get the Gram matrix
`<I,I> = d, <I, Q_aj> = 0, <Q_aj, Q_bk> = 0, <Q_aj, Q_ak> = δ_jk - 1/d`
Let gI + ∑_a ∑_j c_aj Q_aj = 0. Take an inner product of this equation with Q_bk. We get,
c_bk (1 - 1/d) + ∑_{j≠k} c_bj (-1/d) = 0. Thus, c_bk = S/d where S = ∑_i c_bi. Therefore, S = [(d - 1)/d]·S, or S = 0.
-/
theorem family_linearIndependent {n m : ℕ}
    (B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hB : ∀ a, star (B a) * B a = 1)
    (hOrth : ∀ a b, a ≠ b → ∀ j k, (shiftedProj (B a) j * shiftedProj (B b) k).trace = 0) :
    LinearIndependent ℂ (family B) := by
  have hd : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Step 1: the coefficients of the shifted projectors vanish.
  have hsome : ∀ (b : Fin m) (k : Fin (n + 1)), g (some (b, k)) = 0 := by
    intro b
    refine eq_zero_of_eq_sum_mul_inv (fun j => g (some (b, j))) (fun k => ?_)
    change g (some (b, k)) = (∑ j, g (some (b, j))) * ((n + 2 : ℕ) : ℂ)⁻¹
    have h := pairWith_shifted_family B hB hOrth g b k
    rw [hg, map_zero] at h
    exact sub_eq_zero.mp h.symm
  -- Step 2: the coefficient of the identity vanishes.
  have hnone : g none = 0 := by
    have h := pairWith_one_family B hB g
    rw [hg, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hd
  -- Step 3: so every coefficient vanishes.
  rintro (_ | ⟨b, k⟩)
  · exact hnone
  · exact hsome b k

/-
`LinearIndependent ℂ (family B)` is the claim that the family I, Q_aj is linearly independent.
The `omega tactic`, for resolving integer and natural linear arithmetic problems.
For a finite list, `linearly independent` if and only if for every choice of coefficients g, if ∑ gx · Fx = 0 then every gx = 0.
`intro g hg` means let g be any coefficients, and assume hg: ∑_x g_x F_x = 0. Now we must show every g_x = 0.
`intro b` is fix a basis b.
-/

/-! ## Counting dimensions -/

/--
`m (d − 1) + 1` independent matrices fit in the `d^2`-dimensional space of `d × d` complex matrices.
This tries to prove m(n + 1) + 1 ≤ (n + 2)(n + 2) or 1 + m(d - 1) ≤ d²
The family has 1 + m(n + 1) members, they are linearly independent
-/
theorem card_bound {n m : ℕ} (B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hB : ∀ a, star (B a) * B a = 1)
    (hOrth : ∀ a b, a ≠ b → ∀ j k, (shiftedProj (B a) j * shiftedProj (B b) k).trace = 0) :
    m * (n + 1) + 1 ≤ (n + 2) * (n + 2) := by
  have h := (family_linearIndependent B hB hOrth).fintype_card_le_finrank
  simpa [Module.finrank_matrix] using h

/-
`family_linearIndependent B hB hOrth` is the proof the family is independent.
`LinearIndependent.fintype_card_le_finrank` says number of members of an independent family is at most the dimensions of the space
`simpa... using h` means simplify h until it matches the goal. `Module.finrank_matrix` says dimension of the space of a × b matrices is a·b
-/

/-! ## The theorem -/

/-- **The Main Theorem N(d) ≤ d + 1**
For `d ≥ 2`, at most `d + 1` mutually unbiased bases exist in `ℂ^d`.
As d = n + 2, take the m bases B_a, their columns are orthonormal, and by `gram_unbiased` the shifted projectors pair to 0 across different bases.
`card_bound` applies, m(n + 1) + 1 ≤ (n + 2)² = n² + 4n + 4, so m(n + 1) ≤ n² + 4n + 3 = (n + 3)(n + 1). Divide by n + 1 > 0,
m ≤ n + 3 which is same as m ≤ d + 1
-/
theorem mub_upper_bound {d m : ℕ} (hd : 2 ≤ d) (hMUB : HasMUBs d m) : m ≤ d + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  obtain ⟨B, hB⟩ := hMUB
  have hdC : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcount : m * (n + 1) + 1 ≤ (n + 2) * (n + 2) :=
    card_bound (fun a => (B a : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ))
      (fun a => Matrix.UnitaryGroup.star_mul_self (B a))
      (fun a b hab j k => gram_unbiased hdC (hB hab) j k)
  have h3 : m * (n + 1) ≤ (n + 3) * (n + 1) := by nlinarith [hcount]
  have h4 : m ≤ n + 3 := le_of_mul_le_mul_right h3 (by omega)
  omega

/-
`obtain ⟨n, rfl⟩...` line switches from d to n + 2, as natural number subtraction stops at 0
`obtain ⟨B, hB⟩...` there exists a family B with isMUBFamily B
`linarith` is an automatic solver for inequalities that may involve products.
Mathlib fact `le_of_mul_le_mul_right` says if a·c ≤ b·c, and c > 0, then a ≤ b
`omega` just makes sure n + 1 + 2 becomes n + 3
-/

/-- The upper-bound of specifically the d = 6 case. -/
theorem dim6_upper_bound : ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 := by
  intro m h
  have := mub_upper_bound (by norm_num) h
  omega

end MUBUpperBound

#print axioms MUBUpperBound.mub_upper_bound
