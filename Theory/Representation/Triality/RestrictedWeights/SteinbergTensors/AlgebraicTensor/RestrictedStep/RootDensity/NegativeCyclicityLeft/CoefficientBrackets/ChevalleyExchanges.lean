module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.Relations

/-!
# D4 root exchanges from the Chevalley relations

All D4 roots have squared Euclidean length two. The symmetric integral pairing
of independent roots has square less than four. Comparing lengths therefore
forces every positive mixed root term to have coefficients `(1, 1)`. The
Chevalley commutator list is consequently empty or the singleton sum root.

For a root sum, the canonical root-form lengths agree as well. This excludes
the exceptional coefficients, and characteristic two identifies both remaining
signs with one. Cancelling in the raw commutator gives the stated exchange
order. Equal roots are handled by the additive root-group law.

Sources: GLS3 §1.12, Theorem 1.12.1(a,b),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg, *Representations of Algebraic Groups*
(1963), §§2 and 4. The proof applies to the given arbitrary `D4Geometry`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft

private abbrev P := typeDRootPairing 2
private abbrev rv (r : TypeDRootIndex 4) : Vec 4 := typeDRootEmbedding 4 r

private lemma pairing_symm (α β : TypeDRootIndex 4) :
    P.pairing α β = P.pairing β α := by
  simp only [P, typeDRootPairing_pairing]
  exact dot_comm _ _

private lemma pairing_lower (α β : TypeDRootIndex 4)
    (hli : LinearIndependent ℝ ![P.root α, P.root β]) :
    (-1 : ℝ) ≤ P.pairing α β := by
  have hsym : P.pairingIn ℤ α β = P.pairingIn ℤ β α := by
    apply Int.cast_injective (α := ℝ)
    change (algebraMap ℤ ℝ) (P.pairingIn ℤ α β) = (algebraMap ℤ ℝ) (P.pairingIn ℤ β α)
    simpa only [P.algebraMap_pairingIn] using pairing_symm α β
  have hle := P.coxeterWeightIn_le_four ℤ α β
  have hne := (P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ).mp hli
  rw [RootPairing.coxeterWeightIn, ← hsym] at hle hne
  have hlt := lt_of_le_of_ne hle hne
  have h : (-1 : ℤ) ≤ P.pairingIn ℤ α β := by nlinarith
  rw [← P.algebraMap_pairingIn ℤ]
  change (-1 : ℝ) ≤ (P.pairingIn ℤ α β : ℝ)
  exact_mod_cast h

private lemma norm_root (α : TypeDRootIndex 4) : dot (rv α) (rv α) = 2 :=
  typeDRootInSpan_coroot_eval 4 α

private lemma norm_mixed (x y : Vec 4) (a b : ℝ) :
    dot (a • x + b • y) (a • x + b • y) =
      a ^ 2 * dot x x + b ^ 2 * dot y y + 2 * a * b * dot x y := by
  unfold dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma mixed_coefficients (α β γ : TypeDRootIndex 4) (i j : ℕ)
    (hi : 0 < i) (hj : 0 < j)
    (hli : LinearIndependent ℝ ![P.root α, P.root β])
    (hr : P.root γ = (i : ℝ) • P.root α + (j : ℝ) • P.root β) :
    i = 1 ∧ j = 1 := by
  have hv : rv γ = (i : ℝ) • rv α + (j : ℝ) • rv β :=
    congrArg (fun x : typeDRootSpan 4 => (x : Vec 4)) hr
  have hn := norm_root γ
  rw [hv, norm_mixed, norm_root, norm_root] at hn
  have hl : (-1 : ℝ) ≤ dot (rv α) (rv β) := by
    simpa only [P, typeDRootPairing_pairing, rv, dot_comm] using pairing_lower α β hli
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hprod : (0 : ℝ) ≤ i * j * (dot (rv α) (rv β) + 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hij : (i : ℝ) * j ≤ 1 := by nlinarith [sq_nonneg ((i : ℝ) - j)]
  have hi1 : (i : ℝ) = 1 := by nlinarith
  have hj1 : (j : ℝ) = 1 := by nlinarith
  exact ⟨by exact_mod_cast hi1, by exact_mod_cast hj1⟩

private lemma sum_length (α β γ : TypeDRootIndex 4)
    (hr : P.root γ = P.root α + P.root β) :
    RootSquaredLength P γ = RootSquaredLength P α := by
  classical
  let := Fintype.ofFinite (TypeDRootIndex 4)
  have hv : rv γ = rv α + rv β :=
    congrArg (fun x : typeDRootSpan 4 => (x : Vec 4)) hr
  have hv' : rv γ = (1 : ℝ) • rv α + (1 : ℝ) • rv β := by simpa using hv
  have hn := norm_root γ
  rw [hv', norm_mixed, norm_root, norm_root] at hn
  have hab : dot (rv α) (rv β) = -1 := by nlinarith
  have hγα : P.pairing γ α = 1 := by
    change dot (rv α) (rv γ) = 1
    rw [hv]
    change rv α ⬝ᵥ (rv α + rv β) = 1
    rw [dotProduct_add]
    change dot (rv α) (rv α) + dot (rv α) (rv β) = 1
    rw [norm_root, hab]
    norm_num
  have h := P.toInvariantForm.pairing_mul_eq_pairing_mul_swap α γ
  rw [hγα, pairing_symm α γ, hγα] at h
  simpa only [one_mul, RootPairing.toInvariantForm_form, RootSquaredLength] using h.symm

universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

private lemma independent_roots (S : D4Geometry K) (α β : S.roots.Root)
    (hne : β ≠ α) (hop : β ≠ S.roots.neg α) :
    LinearIndependent ℝ ![P.root (S.rootEquiv α), P.root (S.rootEquiv β)] := by
  apply RootPairing.IsReduced.linearIndependent
  · exact fun h => hne (S.rootEquiv.injective h).symm
  · intro h
    apply hop
    apply S.rootEquiv.injective
    apply P.root.injective
    rw [S.based.2.2.1 α]
    rw [P.root_reflectionPerm, P.reflection_apply_self]
    exact (neg_eq_iff_eq_neg.mpr h).symm

private lemma valid_term_iff (S : D4Geometry K) (α β : S.roots.Root)
    (hli : LinearIndependent ℝ ![P.root (S.rootEquiv α), P.root (S.rootEquiv β)])
    (q : ChevalleyCommutatorTerm S.roots.Root) :
    IsValidChevalleyCommutatorTerm S.roots P S.rootEquiv α β q ↔
      q.i = 1 ∧ q.j = 1 ∧ S.roots.add α β = some q.root := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := mixed_coefficients _ _ _ _ _ h.1 h.2.1 hli h.2.2
    refine ⟨hi, hj, (S.addition α β q.root).mpr ?_⟩
    simpa only [hi, hj, Nat.cast_one, one_smul] using h.2.2
  · rintro ⟨hi, hj, hadd⟩
    refine ⟨by omega, by omega, ?_⟩
    simpa only [hi, hj, Nat.cast_one, one_smul] using (S.addition α β q.root).mp hadd

private lemma coefficient_one [CharP k 2] (S : D4Geometry K) (α β : S.roots.Root)
    (hli : LinearIndependent ℝ ![P.root (S.rootEquiv α), P.root (S.rootEquiv β)])
    (q : ChevalleyCommutatorTerm S.roots.Root) (c : k)
    (hc : HasExpectedChevalleyCoefficient S.roots P S.rootEquiv α β q c) : c = 1 := by
  have htwo : ¬ IsChevalleyCoefficientExceptionalTwo S.roots P S.rootEquiv α β q := by
    rintro ⟨hq, hfirst | hsecond | hthird⟩
    · obtain ⟨hi, hj, hadd⟩ := (valid_term_iff S α β hli q).mp hq
      have hlen := sum_length _ _ _ ((S.addition α β q.root).mp hadd)
      have hne : RootSquaredLength P (S.rootEquiv α) ≠ 0 := by
        classical
        exact RootPairing.IsAnisotropic.rootForm_root_ne_zero _
      exact hne (by linarith [hfirst.2.2.2])
    · obtain ⟨r, hr, he⟩ := hsecond.2.2.2.2
      obtain ⟨hi, hj, -⟩ := (valid_term_iff S α β hli r).mp hr
      rcases he with he | he <;> omega
    · have hi := ((valid_term_iff S α β hli q).mp hq).1
      omega
  have hthree : ¬ IsChevalleyCoefficientExceptionalThree S.roots P S.rootEquiv α β q := by
    rintro ⟨hq, hfirst | hsecond⟩
    · obtain ⟨hi, hj, hadd⟩ := (valid_term_iff S α β hli q).mp hq
      have hlen := sum_length _ _ _ ((S.addition α β q.root).mp hadd)
      have hne : RootSquaredLength P (S.rootEquiv α) ≠ 0 := by
        classical
        exact RootPairing.IsAnisotropic.rootForm_root_ne_zero _
      exact hne (by linarith [hfirst.2.2.2])
    · obtain ⟨hi, hj, -⟩ := (valid_term_iff S α β hli q).mp hq
      rcases hsecond.1 with he | he <;> omega
  rcases hc.2.2 htwo hthree with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

/-- The characteristic-two, simply laced exchanges of the actual pinned root
subgroups, including two parameters in the same root subgroup. -/
public theorem nonopposite_root_exchanges [IsAlgClosed k] [CharP k 2] (S : D4Geometry K) :
    HasNonoppositeRootExchanges S := by
  intro α β hop
  by_cases heq : β = α
  · subst β
    have hadd : S.roots.add α α = none := by
      cases ha : S.roots.add α α with
      | none => rfl
      | some γ =>
        exfalso
        have hli := P.linearIndependent_of_add_mem_range_root'
          ⟨S.rootEquiv γ, (S.addition α α γ).mp ha⟩
        exact one_ne_zero (LinearIndependent.pair_iff.mp hli 1 (-1) (by simp)).1
    rw [hadd]
    intro a b
    change S.chevalley.x α a * S.chevalley.x α b =
      S.chevalley.x α b * S.chevalley.x α a
    rw [S.chevalley_spec.2.2.2.1, S.chevalley_spec.2.2.2.1, add_comm a b]
  · have hli := independent_roots S α β heq hop
    obtain ⟨order, c, hnd, _, hmem, hc, hcomm⟩ :=
      S.chevalley_spec.2.2.2.2.1 α β (LinearIndependent.pair_iff.mp hli)
    have hex (a b : k) : S.chevalley.x α a * S.chevalley.x β b =
        S.chevalley.x β b * S.chevalley.x α a *
          (order.map fun q => S.chevalley.x q.root (c q * a ^ q.i * b ^ q.j)).prod := by
      rw [← hcomm a b]
      group
    cases hadd : S.roots.add α β with
    | none =>
      have hn : order = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro q hq
        have he := ((valid_term_iff S α β hli q).mp ((hmem q).mp hq)).2.2
        rw [hadd] at he
        cases he
      intro a b
      change S.chevalley.x α a * S.chevalley.x β b =
        S.chevalley.x β b * S.chevalley.x α a
      simpa only [hn, List.map_nil, List.prod_nil, mul_one] using hex a b
    | some γ =>
      let q₀ : ChevalleyCommutatorTerm S.roots.Root := ⟨1, 1, γ⟩
      have hq₀ : q₀ ∈ order :=
        (hmem q₀).mpr ((valid_term_iff S α β hli q₀).mpr ⟨rfl, rfl, hadd⟩)
      have hunique : ∀ q ∈ order, q = q₀ := by
        intro q hq
        obtain ⟨hi, hj, hroot⟩ := (valid_term_iff S α β hli q).mp ((hmem q).mp hq)
        have hr : q.root = γ := Option.some.inj (hroot.symm.trans hadd)
        cases q
        simp_all only [q₀]
      have hn : order = [q₀] := by
        cases order with
        | nil => simp at hq₀
        | cons r rs =>
          have hr := hunique r List.mem_cons_self
          subst r
          have hrs : rs = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro q hq
            have he := hunique q (List.mem_cons_of_mem _ hq)
            subst q
            exact (List.nodup_cons.mp hnd).1 hq
          rw [hrs]
      have hc₀ : c q₀ = 1 := coefficient_one S α β hli q₀ (c q₀) (hc q₀ hq₀)
      intro a b
      simpa only [hn, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, hc₀, q₀, pow_one, one_mul] using hex a b

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft

end
