module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.WeightNilpotence
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm.Dual
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm.Opposition

/-!
# The basic highest weight of the rational dual

The negative cyclic span bounds the heights of the integral coroot weights
occurring in a factor.  The actual opposition word gives the corresponding
lower bound and produces a nonzero vector in the opposite weight space.  A
covector supported on that weight space is fixed by every positive root group
in the contragredient action.  The torus equations then identify its weight
with the original basic coefficient. All polynomial coefficients are used, so
fixation holds for the entire root groups in characteristic two.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J. 22
(1963), §§2 and 4, especially the height argument in 2.8–2.9 and 4.5,
DOI 10.1017/S0027763000011016. This realizes the rational-dual highest weight
`-w₀λ = λ` using the actual opposition element acting by negation.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem algebraicRootElement_inv_local (r : F4Chevalley.Root) (t : F) :
    (algebraicRootElement r t)⁻¹ = algebraicRootElement r t := by
  have ht : (kPlusPoint t)⁻¹ = kPlusPoint (-t) := by
    apply (additiveGroupPointEquiv F).injective
    rfl
  rw [algebraicRootElement, ← map_inv, ht, CharTwo.neg_eq]

omit [CharP F 2] in
private theorem coeff_zero_local {B : AlgebraicFactor F} (p : RootExpansion B.action)
    (r : F4Chevalley.Root) : p.coeff r 0 = 1 := by
  have h := p.eval_eq r 0
  have hz : (p.coeff r).sum (fun n A => (0 : F) ^ n • A) = p.coeff r 0 := by
    rw [Finsupp.sum_eq_single 0]
    · simp
    · intro n _ hn
      simp [zero_pow hn]
    · simp
  rw [hz] at h
  have h0 : kPlusPoint (0 : F) = (1 : Variety.Point (KPlus F)) := by
    apply (additiveGroupPointEquiv F).injective
    rfl
  simpa [algebraicRootElement, h0] using h

omit [CharP F 2] in
/-- Every coefficient of a root action has the expected integral weight shift. -/
theorem RootExpansion.coeff_mem_corootWeightSpace_of_mem
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (r : F4Chevalley.Root)
    (n : ℕ) {μ : EndNode.Weight} {v : B.Space}
    (hv : v ∈ EndNode.corootWeightSpace B μ) :
    p.coeff r n v ∈ EndNode.corootWeightSpace B
      (μ + n • PositivePrimitives.rootWeight r) := by
  classical
  apply (EndNode.mem_corootWeightSpace B _ _).mpr
  intro j t
  let A : Module.End F B.Space :=
    B.action.action (algebraicCorootElement (typeF4SimpleRootIndex j) t)
  have hpoly (a : F) :
      A * (p.coeff r).sum (fun m C => a ^ m • C) =
        (p.coeff r).sum (fun m C =>
          (a * (t : F) ^ (PositivePrimitives.rootWeight r j)) ^ m • C) * A := by
    have h := congrArg (fun g => (B.action.action g : Module.End F B.Space))
      (EndNode.Multiplicity.coroot_root_commute
        (typeF4RootPairing_baseEquiv j) r t a)
    have h' :
        A * (B.action.action (algebraicRootElement r a) : Module.End F B.Space) =
          (B.action.action
            (algebraicRootElement r ((t : F) ^ PositivePrimitives.rootWeight r j * a)) :
              Module.End F B.Space) * A := by
      simpa only [A, map_mul, Units.val_mul, Module.End.mul_apply, PositivePrimitives.rootWeight,
        typeF4RootPairing_baseEquiv_val] using h
    rw [← p.eval_eq r a, ← p.eval_eq r ((t : F) ^ PositivePrimitives.rootWeight r j * a)] at h'
    simpa only [Finsupp.smul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
      mul_pow] using h'
  have hcoeff (m : ℕ) (x : B.Space) :
      A (p.coeff r m x) =
        (((t : F) ^ PositivePrimitives.rootWeight r j) ^ m) •
          p.coeff r m (A x) := by
    apply (Module.finBasis F B.Space).repr.injective
    ext i
    let l := (Module.finBasis F B.Space).coord i
    let q₁ : Polynomial F :=
      (p.coeff r).sum (fun n C => Polynomial.monomial n (l (A (C x))))
    let q₂ : Polynomial F :=
      (p.coeff r).sum (fun n C => Polynomial.monomial n
        (((t : F) ^ (PositivePrimitives.rootWeight r j : ℤ)) ^ n * l (C (A x))))
    have hpq : q₁ = q₂ := by
      apply Polynomial.funext
      intro a
      have h := congrArg (fun L : Module.End F B.Space => l (L x)) (hpoly a)
      simp only [q₁, q₂, Finsupp.sum, Polynomial.eval_finsetSum,
        Polynomial.eval_monomial, Module.End.mul_apply, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h ⊢
      calc
        _ = ∑ n ∈ (p.coeff r).support, a ^ n * l (A (p.coeff r n x)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact mul_comm _ _
        _ = _ := h
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [mul_pow]
          ring
    change l (A (p.coeff r m x)) =
      l ((((t : F) ^ PositivePrimitives.rootWeight r j) ^ m) • p.coeff r m (A x))
    rw [map_smul, smul_eq_mul]
    have hc := congrArg (fun f : Polynomial F => f.coeff m) hpq
    by_cases hm : m ∈ (p.coeff r).support
    · simpa only [q₁, q₂, Finsupp.sum, Polynomial.finsetSum_coeff,
        Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hm] using hc
    · rw [Finsupp.notMem_support_iff.mp hm]
      simp only [LinearMap.zero_apply, map_zero, mul_zero]

  have he := hcoeff n v
  have ht := (EndNode.mem_corootWeightSpace B μ v).mp hv j t
  rw [ht] at he
  rw [map_smul, smul_smul] at he
  change A (p.coeff r n v) = _
  rw [he]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [zpow_add₀ t.ne_zero, nsmul_eq_mul,
    mul_comm (n : ℤ), zpow_mul, zpow_natCast]
  exact mul_comm _ _

omit [CharP F 2] in
private theorem coeff_functional_eq_zero_of_weight_ne
    {B : AlgebraicFactor F} {bμ μ : EndNode.Weight}
    (f : Module.Dual F B.Space) (hf : f ∈
      (⨆ ν : {ν : EndNode.Weight // ν ≠ bμ}, EndNode.corootWeightSpace B ν).dualAnnihilator)
    (hμ : μ ≠ bμ) {x : B.Space}
    (hx : x ∈ EndNode.corootWeightSpace B μ) : f x = 0 := by
  have hm : EndNode.corootWeightSpace B μ ≤
      (⨆ ν : {ν : EndNode.Weight // ν ≠ bμ}, EndNode.corootWeightSpace B ν) := by
    exact le_iSup (fun ν : {ν : EndNode.Weight // ν ≠ bμ} =>
      EndNode.corootWeightSpace B ν) ⟨μ, hμ⟩
  exact (Submodule.mem_dualAnnihilator f).mp hf _ (hm hx)

/-- The rational dual has the original basic coefficient as its actual highest weight. -/
theorem ContravariantForm.dualFactor_hasHighestWeight
    (B : AlgebraicFactor F) (b : BasicWeight) {v : B.Space}
    (p : RootExpansion B.action) (_hb : b ≠ (0, 0))
    (hv : B.IsBasicHighestWeightVector b v)
    (hspan : p.shortNegativeSpan v = ⊤) :
    HasHighestWeight (ContravariantForm.dualFactor B) (basicCoefficient b) := by
  classical
  let bμ : EndNode.Weight := fun i => (basicCoefficient b i : ℤ)
  let H := PositivePrimitives.weightHeight
  let Hb : ℤ := H bμ
  have htop : (⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ) = ⊤ :=
    p.corootWeightSpace_iSup_eq_top_of_negative_span hv hspan
  have hword_bound (l : List ShortNegativeRoot) :
      H (bμ + (l.map fun r => PositivePrimitives.rootWeight r.val).sum) ≤ Hb := by
    rw [map_add]
    have hroot (r : ShortNegativeRoot) :
        H (PositivePrimitives.rootWeight r.val) ≤ 0 := by
      rw [PositivePrimitives.weightHeight_root]
      have hn : typeF4RootPairing_base.height r.val ≠ 0 :=
        typeF4RootPairing_base.height_ne_zero r.val
      have hnp : ¬ 0 ≤ typeF4RootPairing_base.height r.val := by
        intro hp
        exact r.property.2 ((typeF4RootPairing_base.isPos_iff').mpr hp)
      omega
    induction l with
    | nil => simp [Hb]
    | cons r l ih =>
      simp only [List.map_cons, List.sum_cons, map_add]
      have hr := hroot r
      omega
  let U : Submodule F B.Space :=
    ⨆ μ : EndNode.Weight, ⨆ (_ : H μ ≤ Hb), EndNode.corootWeightSpace B μ
  have hU : U = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    have hw := p.word_mem_corootWeightSpace (l.map Subtype.val)
      (EndNode.basicHighestWeightVector_mem_corootWeightSpace hv)
    have hμ : H (bμ + (l.map fun r => PositivePrimitives.rootWeight r.val).sum) ≤ Hb :=
      hword_bound l
    exact Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem hμ (by simpa only [List.map_map,
        Function.comp_def, bμ] using hw))
  have hupper (μ : EndNode.Weight)
      (hμ : EndNode.corootWeightSpace B μ ≠ ⊥) : H μ ≤ Hb := by
    have hmemb : μ ∈ {ν : EndNode.Weight | H ν ≤ Hb} :=
      iSupIndep.mem_of_biSup_eq_top (EndNode.corootWeightSpace_iSupIndep B)
        (by simpa [U] using hU) hμ
    exact hmemb
  have hlow (μ : EndNode.Weight)
      (hμ : EndNode.corootWeightSpace B μ ≠ ⊥) : -Hb ≤ H μ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    let n := ContravariantForm.oppositionElement (F := F)
    let y : B.Space :=
      (B.action.action n : Module.End F B.Space) x
    have hy : y ∈ EndNode.corootWeightSpace B (-μ) :=
      ContravariantForm.opposition_mem_neg_weight B hx
    have hy0 : y ≠ 0 := by
      intro hz
      exact (EndNode.action_ne_zero B n hx0) (by simpa [y] using hz)
    have hbound := hupper (-μ) (by
      intro hbot
      exact hy0 (by simpa [hbot] using hy))
    have hbound' := neg_le_neg hbound
    simpa [map_neg] using hbound'
  let lambdaWeight : EndNode.Weight := -bμ
  have hlambdaWeight : EndNode.corootWeightSpace B lambdaWeight ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show EndNode.corootWeightSpace B bμ ≠ ⊥ from by
        intro hbot
        have hz : v ∈ (⊥ : Submodule F B.Space) := by
          have hvw := EndNode.basicHighestWeightVector_mem_corootWeightSpace hv
          rw [hbot] at hvw
          exact hvw
        exact hv.1 ((Submodule.mem_bot F).mp hz))
    let n := ContravariantForm.oppositionElement (F := F)
    let y : B.Space :=
      (B.action.action n : Module.End F B.Space) x
    have hy : y ∈ EndNode.corootWeightSpace B lambdaWeight :=
      ContravariantForm.opposition_mem_neg_weight B hx
    have hy0 : y ≠ 0 := by
      intro hz
      exact (EndNode.action_ne_zero B n hx0) (by simpa [y] using hz)
    intro hbot
    exact hy0 (by simpa [hbot] using hy)
  let W : Submodule F B.Space :=
    ⨆ μ : {μ : EndNode.Weight // μ ≠ lambdaWeight}, EndNode.corootWeightSpace B μ
  have hnot : ∀ x ∈ EndNode.corootWeightSpace B lambdaWeight, x ≠ 0 → x ∉ W := by
    intro x hx hx0 hxW
    have hd := (EndNode.corootWeightSpace_iSupIndep B).disjoint_biSup
      (x := lambdaWeight) (y := {μ : EndNode.Weight | μ ≠ lambdaWeight}) (by simp)
    have hxW' : x ∈ (⨆ i ∈ {μ : EndNode.Weight | μ ≠ lambdaWeight},
      EndNode.corootWeightSpace B i) := by
      simpa only [W, iSup_subtype, Set.mem_ofPred_eq] using hxW
    have : x ∈ (⊥ : Submodule F B.Space) :=
      hd.le_bot ⟨hx, hxW'⟩
    exact hx0 ((Submodule.mem_bot F).mp this)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hlambdaWeight
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (hnot x hx hx0) inferInstance
  have hfdual : f ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have hm : f y ∈ W.map f := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    rw [hfW] at hm
    exact (Submodule.mem_bot F).mp hm
  have hf0 : f ≠ 0 := by
    intro hzero
    exact hf (congrArg (fun q : Module.Dual F B.Space => q x) hzero)
  refine ⟨f, hf0, ?_, ?_⟩
  · intro r hr t
    apply LinearMap.ext
    intro z
    erw [ContravariantForm.dualFactor_spec B]
    rw [algebraicRootElement_inv_local]
    have hz : z ∈ ⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ := by
      rw [htop]
      trivial
    refine Submodule.iSup_induction (EndNode.corootWeightSpace B)
      (motive := fun y => f ((B.action.action (algebraicRootElement r t)).val y) = f y)
      hz ?_ ?_ ?_
    · intro μ y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      have hnonbot : EndNode.corootWeightSpace B μ ≠ ⊥ := by
        intro hbot
        exact hy0 (by simpa only [hbot, Submodule.mem_bot] using hy)
      have hμlow := hlow μ hnonbot
      have hvanish (n : ℕ) (hn : n ≠ 0) : f (p.coeff r n y) = 0 := by
        have hshift := p.coeff_mem_corootWeightSpace_of_mem r n hy
        have hneq : μ + n • PositivePrimitives.rootWeight r ≠ lambdaWeight := by
          intro heq
          have hh := congrArg H heq
          have hrpos : 0 < H (PositivePrimitives.rootWeight r) := by
            rw [PositivePrimitives.weightHeight_root]
            exact hr
          have hnpos : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hp := mul_pos hnpos hrpos
          change H (μ + n • PositivePrimitives.rootWeight r) = H (-bμ) at hh
          rw [map_add, map_nsmul, map_neg] at hh
          simp only [nsmul_eq_mul] at hh
          change _ = -Hb at hh
          omega
        exact coeff_functional_eq_zero_of_weight_ne f hfdual hneq hshift
      rw [← p.eval_eq]
      simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      rw [Finset.sum_eq_single 0]
      · rw [coeff_zero_local p r]
        simp
      · intro n _ hn
        rw [hvanish n hn, smul_zero]
      · intro hzero
        have hz := Finsupp.notMem_support_iff.mp hzero
        rw [hz]
        simp
    · simp
    · intro y z hy hz
      simp only [map_add, hy, hz]
  · intro i t
    apply LinearMap.ext
    intro z
    erw [ContravariantForm.dualFactor_spec B]
    change f ((B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t)⁻¹).val z) =
      ((t : F) ^ basicCoefficient b i) • f z
    have hz : z ∈ ⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ := by
      rw [htop]
      trivial
    refine Submodule.iSup_induction (EndNode.corootWeightSpace B)
      (motive := fun y =>
        f ((B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t)⁻¹).val y) =
          ((t : F) ^ basicCoefficient b i) • f y) hz ?_ ?_ ?_
    · intro μ y hy
      have htμ := (EndNode.mem_corootWeightSpace B μ y).mp hy i t
      have he := congrArg (fun y =>
        (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t)⁻¹).val y) htμ
      simp only [← Module.End.mul_apply, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Module.End.one_apply, map_smul] at he
      have htinv := congrArg (fun z : B.Space => ((t : F) ^ μ i)⁻¹ • z) he
      have hi : (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t)⁻¹).val y =
          ((t : F) ^ μ i)⁻¹ • y := by
        simpa only [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ t.ne_zero), one_smul]
          using htinv.symm
      rw [hi, map_smul]
      by_cases heq : μ = lambdaWeight
      · subst μ
        simp [lambdaWeight, bμ]
      · have hfz := coeff_functional_eq_zero_of_weight_ne f hfdual heq hy
        simp only [hfz, smul_zero]
    · simp
    · intro y z hy hz
      simp only [map_add, hy, hz, smul_add]

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
