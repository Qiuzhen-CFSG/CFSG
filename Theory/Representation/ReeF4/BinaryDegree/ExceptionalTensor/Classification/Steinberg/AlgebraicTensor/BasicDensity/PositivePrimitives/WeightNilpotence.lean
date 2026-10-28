module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.TorusCovariance

/-!
# Uniform nilpotence from integral coroot weights

The degree-one coefficient of an actual root action shifts all four integral
coroot weights by that root's coroot pairings. The linear functional
`11 μ₀ + 21 μ₁ + 15 μ₂ + 8 μ₃` takes each simple root to one, hence takes every
root to its height in the fixed F₄ base. Every positive-root coefficient
therefore raises this integral height by at least one.

If negative short-root words span from a genuine highest vector, the integral
weight spaces span the factor. Their independence and finite dimensionality
leave a finite set of occurring weights. A word longer than the range of their
heights acts as zero. This proves uniform product nilpotence, without inferring
it from individual nilpotence or assuming differential irreducibility.

Source: the height argument in Steinberg, *Representations of Algebraic Groups*,
Nagoya Math. J. 22 (1963), §§2.8–2.9, 4.5, and 11.1(1),(3),
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]
namespace PositivePrimitives

/-- Integral simple-coroot coordinates. -/
abbrev IntegralWeight := EndNode.Weight

/-- The shift of coroot coordinates caused by the specified root. -/
@[expose] def rootWeight (r : F4Chevalley.Root) : IntegralWeight :=
  fun i => typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)

/-- The height functional in simple-coroot coordinates. -/
@[expose] def weightHeight : IntegralWeight →ₗ[ℤ] ℤ where
  toFun μ := 11 * μ 0 + 21 * μ 1 + 15 * μ 2 + 8 * μ 3
  map_add' μ ν := by simp only [Pi.add_apply]; ring
  map_smul' c μ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Each row of the F₄ Cartan matrix has height one. -/
lemma weightHeight_simple (i : Fin 4) : weightHeight (rootWeight (typeF4SimpleRootIndex i)) = 1 := by
  have hp (j : Fin 4) : rootWeight (typeF4SimpleRootIndex i) j = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [weightHeight, LinearMap.coe_mk, AddHom.coe_mk, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix] <;> decide

/-- The coordinate functional agrees with the fixed base's root height. -/
lemma weightHeight_root (r : F4Chevalley.Root) :
    weightHeight (rootWeight r) = typeF4RootPairing_base.height r := by
  let L : typeF4RootPairing.rootSpan ℤ →ₗ[ℤ] ℤ :=
    weightHeight.comp (LinearMap.pi fun i : Fin 4 =>
      typeF4RootPairing.coroot'In ℤ (typeF4SimpleRootIndex i))
  have hL (s : F4Chevalley.Root) :
      L (typeF4RootPairing.rootSpanMem ℤ s) = weightHeight (rootWeight s) := by
    change weightHeight _ = weightHeight _
    congr 1
  have hLs (s : typeF4RootPairing_base.support) :
      L (typeF4RootPairing.rootSpanMem ℤ s) = 1 := by
    rw [hL, ← typeF4RootPairing_baseEquiv.apply_symm_apply s]
    exact weightHeight_simple _
  obtain ⟨f, _, _, hf⟩ := typeF4RootPairing_base.exists_root_eq_sum_int r
  have hspan : typeF4RootPairing.rootSpanMem ℤ r =
      ∑ s ∈ typeF4RootPairing_base.support, f s • typeF4RootPairing.rootSpanMem ℤ s := by
    apply Subtype.ext
    simpa using hf
  rw [← hL, hspan, map_sum, typeF4RootPairing_base.height_eq_sum hf]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, hLs ⟨s, hs⟩]
  simp
end PositivePrimitives

/-- The actual first root coefficient shifts the full integral weight. -/
lemma RootExpansion.coeff_one_mem_corootWeightSpace {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (r : F4Chevalley.Root)
    {μ : EndNode.Weight} {v : B.Space} (hv : v ∈ EndNode.corootWeightSpace B μ) :
    p.coeff r 1 v ∈ EndNode.corootWeightSpace B (μ + PositivePrimitives.rootWeight r) := by
  apply (EndNode.mem_corootWeightSpace B _ _).mpr
  intro j t
  let A : Module.End F B.Space :=
    B.action.action (algebraicCorootElement (typeF4SimpleRootIndex j) t)
  have he := EndNode.Multiplicity.rootOperator_intertwine B r r A A
    ((t : F) ^ (PositivePrimitives.rootWeight r j)) (by
      intro a w
      have hh := congrArg (fun g => (B.action.action g : Module.End F B.Space) w)
        (EndNode.Multiplicity.coroot_root_commute (typeF4RootPairing_baseEquiv j) r t a)
      simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A,
        PositivePrimitives.rootWeight, typeF4RootPairing_baseEquiv_val] using hh)
  have he' := congrArg (fun L : Module.End F B.Space => L v) he
  have ht := (EndNode.mem_corootWeightSpace B μ v).mp hv j t
  rw [p.coeff_one_eq_rootOperator]
  change A (EndNode.Multiplicity.rootOperator B r v) = _
  change A (EndNode.Multiplicity.rootOperator B r v) =
    ((t : F) ^ (PositivePrimitives.rootWeight r j)) •
      EndNode.Multiplicity.rootOperator B r (A v) at he'
  change A v = _ at ht
  rw [ht, map_smul, smul_smul] at he'
  convert he' using 1
  simp only [Pi.add_apply, zpow_add₀ t.ne_zero, mul_comm]

/-- A word shifts weight by the sum of its root weights. -/
lemma RootExpansion.word_mem_corootWeightSpace {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (l : List F4Chevalley.Root)
    {μ : EndNode.Weight} {v : B.Space} (hv : v ∈ EndNode.corootWeightSpace B μ) :
    (l.map fun r => p.coeff r 1).prod v ∈
      EndNode.corootWeightSpace B (μ + (l.map PositivePrimitives.rootWeight).sum) := by
  induction l with
  | nil => simpa using hv
  | cons r l ih =>
    simpa [add_assoc, add_comm, add_left_comm] using p.coeff_one_mem_corootWeightSpace r ih

/-- Negative cyclicity from a highest vector supplies a spanning weight decomposition. -/
lemma RootExpansion.corootWeightSpace_iSup_eq_top_of_negative_span
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (hspan : p.shortNegativeSpan v = ⊤) :
    (⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  have h := p.word_mem_corootWeightSpace (l.map Subtype.val)
    (EndNode.basicHighestWeightVector_mem_corootWeightSpace hv)
  exact Submodule.mem_iSup_of_mem _ (by simpa only [List.map_map, Function.comp_def] using h)

/-- Positive short-root words act uniformly nilpotently on a negative-cyclic factor. -/
lemma RootExpansion.hasNilpotentShortPositiveAction_of_negative_span
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (hspan : p.shortNegativeSpan v = ⊤) :
    p.HasNilpotentShortPositiveAction := by
  classical
  let H := PositivePrimitives.weightHeight
  have hfinite := Submodule.finite_ne_bot_of_iSupIndep (EndNode.corootWeightSpace_iSupIndep B)
  obtain ⟨hi, hhi⟩ := (hfinite.image H).bddAbove
  obtain ⟨lo, hlo⟩ := (hfinite.image H).bddBelow
  refine ⟨(hi - lo).toNat + 1, ?_⟩
  intro l hl
  have hheight : (l.length : ℤ) ≤ H ((l.map fun r => PositivePrimitives.rootWeight r.val).sum) := by
    clear hl
    induction l with
    | nil => simp [H]
    | cons r l ih =>
      have hr : 0 < H (PositivePrimitives.rootWeight r.val) := by
        rw [PositivePrimitives.weightHeight_root]
        exact r.property.2
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
        List.sum_cons, map_add]
      omega
  ext x
  have hx : x ∈ ⨆ μ, EndNode.corootWeightSpace B μ := by
    rw [p.corootWeightSpace_iSup_eq_top_of_negative_span hv hspan]
    trivial
  change (l.map fun r => p.coeff r.val 1).prod x = 0
  refine Submodule.iSup_induction (EndNode.corootWeightSpace B)
    (motive := fun y => (l.map fun r => p.coeff r.val 1).prod y = 0) hx ?_ ?_ ?_
  · intro μ y hy
    by_contra hne
    have hy0 : y ≠ 0 := by intro hz; apply hne; simp [hz]
    have hμ : EndNode.corootWeightSpace B μ ≠ ⊥ := by
      intro hz
      exact hy0 (by simpa [hz] using hy)
    have hword := p.word_mem_corootWeightSpace (l.map Subtype.val) hy
    have hν : EndNode.corootWeightSpace B
        (μ + (l.map fun r => PositivePrimitives.rootWeight r.val).sum) ≠ ⊥ := by
      intro hz
      apply hne
      simpa only [List.map_map, Function.comp_def, hz, Submodule.mem_bot] using hword
    have hb := hhi ⟨_, hν, rfl⟩
    have ha := hlo ⟨μ, hμ, rfl⟩
    simp only [map_add] at hb
    rw [hl] at hheight
    have hn := Int.self_le_toNat (hi - lo)
    omega
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz, add_zero]
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
