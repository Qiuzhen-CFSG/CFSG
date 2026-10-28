module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RankOnePinning

/-!
# Whole source rank-one pinnings aligned with the specified reflections

Pull a specified nᵢ ∈ Rᵢ ∩ N back through the faithful whole SL₂ comparison.
Its lower-left entry is nonzero: otherwise nᵢ would normalize the simple
root and contradict its disjointness from the reflected Borel. Its square
lies in H and hence normalizes the simple root. The lower-left entry of
that square forces equal diagonal entries, and determinant one then gives
nᵢ² = 1, including over F₂ and F₄.

A Borel conjugation sends this matrix to the standard Weyl involution.
Precompose the ENTIRE source pinning with its inverse. This preserves the
simple-root subgroup, makes the Weyl image precisely the specified nᵢ,
and induces one scalar change on its additive parameters. Transport the
rank-one word and diagonal action along the same map. Every element of
H ∩ Rᵢ is diagonal in these coordinates. The reverse torus containment,
compatibility between the two rank-one labelings and the mixed module
relations remain source obligations.

Source: Fong--Seitz II §7, printed p.192, and the labelings used in
(9.9)--(9.15), printed pp.213--216. The elementary Borel conjugation
calculation is adapted from the existing private matrix proof in
Theory/SpecificGroups/PSL2/SemilinearCoverage/Normalization.lean.
AlignedPositive supplies the actual six-root consumer on the same quotient.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F))

theorem sourcePinningHom_unip_map :
    (Unip F).map (sourcePinningHom Q split i hV μ) = simpleRoot Q split i := by
  rw [← simpleParameter_range Q split i hV μ]
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨a,rfl⟩ := (mem_Unip_iff g).mp hg
    exact ⟨.ofAdd a, (sourcePinningHom_root Q split i hV μ a).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨uni a.toAdd, (mem_Unip_iff _).mpr ⟨a.toAdd,rfl⟩,
      sourcePinningHom_root Q split i hV μ a.toAdd⟩

theorem sourcePinningHom_unip_comap :
    (simpleRoot Q split i).comap (sourcePinningHom Q split i hV μ) = Unip F := by
  rw [← sourcePinningHom_unip_map Q split i hV μ,
    comap_map_eq_self_of_injective (sourcePinningHom_injective Q split i hV μ)]

theorem sourcePinningHom_borel_iff (g : SL2 F) :
    sourcePinningHom Q split i hV μ g ∈ normalizer (simpleRoot Q split i : Set _) ↔
      g ∈ Borel F := by
  change g ∈ (normalizer (simpleRoot Q split i : Set _)).comap
    (sourcePinningHom Q split i hV μ) ↔ _
  rw [comap_normalizer_eq_of_le_range (by
    rw [sourcePinningHom_range]
    exact le_sup_left), sourcePinningHom_unip_comap]

def reflectionMatrix (n : RootReflection Q split i) : SL2 F :=
  (sourcePinning Q split i hV μ).symm ⟨n.val,n.mem_rankOne⟩

@[simp] theorem reflectionMatrix_image (n : RootReflection Q split i) :
    sourcePinningHom Q split i hV μ (reflectionMatrix Q split i hV μ n) = n.val := by
  change ((sourcePinning Q split i hV μ)
    ((sourcePinning Q split i hV μ).symm _) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]

theorem reflectionMatrix_lower_ne_zero (n : RootReflection Q split i) :
    (reflectionMatrix Q split i hV μ n).val 1 0 ≠ 0 := by
  intro hz
  have hn : (n.val : X ⧸ Q.D) ∈ normalizer (simpleRoot Q split i : Set _) := by
    rw [← reflectionMatrix_image Q split i hV μ n, sourcePinningHom_borel_iff,
      mem_Borel_iff]
    exact hz
  have hsub : simpleRoot Q split i ≤ borelConjugate (Q.simple i) := by
    rw [borelConjugate_eq _ n.val n.class_eq]
    intro u hu
    exact split.U_le (simpleRoot_le Q split i ((mem_normalizer_iff.mp hn u).mp hu))
  exact simpleRoot_ne_bot Q split i
    (eq_bot_iff.mpr fun u hu => mem_bot.mpr
      ((disjoint_def.mp (simpleRoot_disjoint_conjugateBorel Q split i)) hu (hsub hu)))

theorem reflectionMatrix_square_borel (n : RootReflection Q split i) :
    reflectionMatrix Q split i hV μ n * reflectionMatrix Q split i hV μ n ∈ Borel F := by
  rw [← sourcePinningHom_borel_iff Q split i hV μ, map_mul, reflectionMatrix_image]
  apply torus_normalizes_simpleRoot Q split i
  have hq : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (n.val*n.val) = 1 := by
    rw [map_mul,n.class_eq]
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  exact (QuotientGroup.eq_one_iff (n.val*n.val)).mp hq

omit [Finite F] in
private theorem square_borel_involution (A : SL2 F)
    (hc : A.val 1 0 ≠ 0) (hA : A*A ∈ Borel F) : A*A = 1 := by
  have hd : A.val 1 1 = A.val 0 0 := by
    have he := (mem_Borel_iff _).mp hA
    have he0 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
    have he' : (A.val 1 1 + A.val 0 0) * A.val 1 0 = 0 := by
      linear_combination he0
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hc)
  have hdet : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two,hd,CharTwo.sub_eq_add] using A.property
  ext j k
  fin_cases j <;> fin_cases k
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,hd] using hdet
  · have hz : A.val 0 0 * A.val 0 1 + A.val 0 1 * A.val 0 0 = 0 := by
      rw [mul_comm (A.val 0 1), CharTwo.add_self_eq_zero]
    simpa [Matrix.mul_apply,Fin.sum_univ_two,hd] using hz
  · exact (mem_Borel_iff _).mp hA
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,hd,add_comm,mul_comm] using hdet

include hV μ in
theorem sourceReflection_sq (n : RootReflection Q split i) :
    (n.val : X ⧸ Q.D) * n.val = 1 := by
  rw [← reflectionMatrix_image Q split i hV μ n, ← map_mul,
    square_borel_involution _ (reflectionMatrix_lower_ne_zero Q split i hV μ n)
      (reflectionMatrix_square_borel Q split i hV μ n), map_one]

private theorem exists_borel_conj_reflection (A : SL2 F)
    (hAA : A * A = 1) (hc : A.val 1 0 ≠ 0) :
    ∃ b : SL2 F, b ∈ Borel F ∧ b * A * b⁻¹ = weyl F := by
  have hd : A.val 1 1 = A.val 0 0 := by
    have he := congrArg (fun g : SL2 F => g.val 1 0) hAA
    have he0 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
    have he' : (A.val 1 1 + A.val 0 0) * A.val 1 0 = 0 := by
      linear_combination he0
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hc)
  have hdet : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hd, CharTwo.sub_eq_add] using A.property
  obtain ⟨r, hr2⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := F))) (A.val 1 0)
  change r ^ 2 = A.val 1 0 at hr2
  have hr : r ≠ 0 := by intro hz; apply hc; rw [← hr2, hz]; simp
  let b : SL2 F := ⟨!![r, A.val 0 0 / r; 0, r⁻¹], by
    simp [Matrix.det_fin_two, hr]⟩
  have hcr : r⁻¹ * A.val 1 0 = r := by
    rw [← hr2, pow_two, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  have hrel : b * A = weyl F * b := by
    apply Subtype.ext
    change b.val * A.val = (weyl F).val * b.val
    ext j k
    fin_cases j <;> fin_cases k
    · simp [b, Matrix.mul_apply, Fin.sum_univ_two]
      rw [div_eq_mul_inv, mul_assoc, hcr, mul_comm r, CharTwo.add_self_eq_zero]
    · simp [b, Matrix.mul_apply, Fin.sum_univ_two, hd]
      field_simp
      linear_combination hdet + A.val 0 1 * hr2
    · simpa [b, Matrix.mul_apply, Fin.sum_univ_two] using hcr
    · simp [b, Matrix.mul_apply, Fin.sum_univ_two, hd, div_eq_mul_inv, mul_comm]
  refine ⟨b, ?_, ?_⟩
  · rw [mem_Borel_iff]; simp [b]
  · rw [hrel, mul_inv_cancel_right]

theorem exists_reflection_alignment (n : RootReflection Q split i) :
    ∃ b : SL2 F, b ∈ Borel F ∧
      sourcePinningHom Q split i hV μ (b⁻¹ * weyl F * b) = n.val := by
  let A := reflectionMatrix Q split i hV μ n
  obtain ⟨b,hb,he⟩ := exists_borel_conj_reflection A
    (square_borel_involution A (reflectionMatrix_lower_ne_zero Q split i hV μ n)
      (reflectionMatrix_square_borel Q split i hV μ n))
    (reflectionMatrix_lower_ne_zero Q split i hV μ n)
  refine ⟨b,hb,?_⟩
  rw [← he]
  have hh : b⁻¹ * (b*A*b⁻¹) * b = A := by group
  rw [hh]
  exact reflectionMatrix_image Q split i hV μ n

def alignmentMatrix (n : RootReflection Q split i) : SL2 F :=
  (exists_reflection_alignment Q split i hV μ n).choose

theorem alignmentMatrix_mem (n : RootReflection Q split i) :
    alignmentMatrix Q split i hV μ n ∈ Borel F :=
  (exists_reflection_alignment Q split i hV μ n).choose_spec.1

/-- Change the entire rank-one pinning to match the specified source reflection. -/
def alignedPinning (n : RootReflection Q split i) : SL2 F ≃* rankOne Q split i :=
  (MulAut.conj (alignmentMatrix Q split i hV μ n)⁻¹).trans (sourcePinning Q split i hV μ)

def alignedPinningHom (n : RootReflection Q split i) : SL2 F →* X ⧸ Q.D :=
  (sourcePinningHom Q split i hV μ).comp
    (MulAut.conj (alignmentMatrix Q split i hV μ n)⁻¹).toMonoidHom

@[simp] theorem alignedPinning_coe (n : RootReflection Q split i) (g : SL2 F) :
    (alignedPinning Q split i hV μ n g : X ⧸ Q.D) = alignedPinningHom Q split i hV μ n g := rfl

theorem alignedPinningHom_injective (n : RootReflection Q split i) :
    Function.Injective (alignedPinningHom Q split i hV μ n) :=
  (sourcePinningHom_injective Q split i hV μ).comp (MulAut.conj _).injective

theorem alignedPinningHom_range (n : RootReflection Q split i) :
    (alignedPinningHom Q split i hV μ n).range = rankOne Q split i := by
  rw [alignedPinningHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (MulAut.conj _).surjective,
    ← MonoidHom.range_eq_map, sourcePinningHom_range]

@[simp] theorem alignedPinningHom_weyl (n : RootReflection Q split i) :
    alignedPinningHom Q split i hV μ n (weyl F) = n.val := by
  simpa only [alignedPinningHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv, alignmentMatrix] using
      (exists_reflection_alignment Q split i hV μ n).choose_spec.2

def alignedSimpleParameter (n : RootReflection Q split i) : Multiplicative F →* X ⧸ Q.D :=
  (alignedPinningHom Q split i hV μ n).comp (Matrix.SpecialLinearGroup.upperUnipotentHom F)

@[simp] theorem alignedSimpleParameter_apply (n : RootReflection Q split i) (a : F) :
    alignedSimpleParameter Q split i hV μ n (.ofAdd a) =
      alignedPinningHom Q split i hV μ n (uni a) := rfl

theorem alignedSimpleParameter_injective (n : RootReflection Q split i) :
    Function.Injective (alignedSimpleParameter Q split i hV μ n) :=
  (alignedPinningHom_injective Q split i hV μ n).comp
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)

theorem alignedPinningHom_unip_map (n : RootReflection Q split i) :
    (Unip F).map (alignedPinningHom Q split i hV μ n) = simpleRoot Q split i := by
  have he : (Unip F).map (MulAut.conj (alignmentMatrix Q split i hV μ n)⁻¹).toMonoidHom =
      Unip F := mem_normalizer_iff_map_conj_eq.mp
        ((Borel F).inv_mem (alignmentMatrix_mem Q split i hV μ n))
  rw [alignedPinningHom, ← map_map,he,sourcePinningHom_unip_map]

@[simp] theorem alignedSimpleParameter_range (n : RootReflection Q split i) :
    (alignedSimpleParameter Q split i hV μ n).range = simpleRoot Q split i := by
  rw [alignedSimpleParameter, MonoidHom.range_comp]
  exact alignedPinningHom_unip_map Q split i hV μ n

/-- The normalization is a single scalar change, induced by the whole Borel conjugacy. -/
theorem alignedSimpleParameter_scaling (n : RootReflection Q split i) (a : F) :
    alignedSimpleParameter Q split i hV μ n (.ofAdd a) =
      simpleParameter Q split i hV μ
        (.ofAdd (((alignmentMatrix Q split i hV μ n)⁻¹).val 0 0 ^ 2 * a)) := by
  rw [alignedSimpleParameter_apply]
  change sourcePinningHom Q split i hV μ
    ((alignmentMatrix Q split i hV μ n)⁻¹ * uni a * ((alignmentMatrix Q split i hV μ n)⁻¹)⁻¹) = _
  rw [Borel_conj_uni ((Borel F).inv_mem (alignmentMatrix_mem Q split i hV μ n)),
    sourcePinningHom_root]

theorem alignedPinningHom_borel_iff (n : RootReflection Q split i) (g : SL2 F) :
    alignedPinningHom Q split i hV μ n g ∈ normalizer (simpleRoot Q split i : Set _) ↔
      g ∈ Borel F := by
  have hc : (simpleRoot Q split i).comap (alignedPinningHom Q split i hV μ n) = Unip F := by
    rw [← alignedPinningHom_unip_map Q split i hV μ n,
      comap_map_eq_self_of_injective (alignedPinningHom_injective Q split i hV μ n)]
  change g ∈ (normalizer (simpleRoot Q split i : Set _)).comap
    (alignedPinningHom Q split i hV μ n) ↔ _
  rw [comap_normalizer_eq_of_le_range (by
    rw [alignedPinningHom_range]
    exact le_sup_left),hc]

def alignedTorus (n : RootReflection Q split i) (a : Fˣ) : X ⧸ Q.D :=
  alignedPinningHom Q split i hV μ n (tor a)

theorem aligned_rankOne_word (n : RootReflection Q split i) (a : Fˣ) :
    alignedSimpleParameter Q split i hV μ n (.ofAdd (a : F)) *
      ((n.val : X ⧸ Q.D) * alignedSimpleParameter Q split i hV μ n (.ofAdd (↑a⁻¹ : F)) *
        (n.val : X ⧸ Q.D)⁻¹) * alignedSimpleParameter Q split i hV μ n (.ofAdd (a : F)) =
      alignedTorus Q split i hV μ n a * n.val := by
  have hw : uni (a : F) * (weyl F * uni (↑a⁻¹ : F) * (weyl F)⁻¹) * uni (a : F) =
      tor a * weyl F := by
    apply sourcePinningHom_injective Q split i hV μ
    simpa only [map_mul,map_inv,sourcePinningHom_root,pinnedReflection,pinnedTorus]
      using pinned_rankOne_word Q split i hV μ a
  simpa only [map_mul,map_inv,alignedPinningHom_weyl,← alignedSimpleParameter_apply,alignedTorus]
    using congrArg (alignedPinningHom Q split i hV μ n) hw

theorem alignedTorus_root (n : RootReflection Q split i) (a : Fˣ) (b : F) :
    alignedTorus Q split i hV μ n a * alignedSimpleParameter Q split i hV μ n (.ofAdd b) *
      (alignedTorus Q split i hV μ n a)⁻¹ =
        alignedSimpleParameter Q split i hV μ n (.ofAdd ((a : F)^2*b)) := by
  simp only [alignedSimpleParameter_apply, alignedTorus, ← map_inv, ← map_mul]
  apply congrArg (alignedPinningHom Q split i hV μ n)
  exact Borel_conj_uni (by rw [mem_Borel_iff]; rfl) b

/-- The entire source Cartan intersection is diagonal in the aligned pinning. -/
theorem aligned_cartan_diagonal (n : RootReflection Q split i) (g : SL2 F)
    (hg : alignedPinningHom Q split i hV μ n g ∈ Q.tits.B ⊓ Q.tits.N) :
    ∃ a : Fˣ, g = tor a := by
  have h10 : g.val 1 0 = 0 := (mem_Borel_iff _).mp
    ((alignedPinningHom_borel_iff Q split i hV μ n g).mp
      (torus_normalizes_simpleRoot Q split i hg))
  have hinv : (n.val : X ⧸ Q.D)⁻¹ = n.val :=
    inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i hV μ n)
  have hg' : alignedPinningHom Q split i hV μ n (weyl F*g*weyl F) ∈
      Q.tits.B ⊓ Q.tits.N := by
    rw [map_mul,map_mul,alignedPinningHom_weyl]
    simpa only [hinv] using (mem_normalizer_iff.mp (torus_normalizes n.val)
      (alignedPinningHom Q split i hV μ n g)).mp hg
  have h01 : g.val 0 1 = 0 := by
    have he := (mem_Borel_iff _).mp
      ((alignedPinningHom_borel_iff Q split i hV μ n _).mp
        (torus_normalizes_simpleRoot Q split i hg'))
    simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using he
  have hdet : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two,h10,h01,mul_zero,zero_mul,sub_zero] using g.property
  let a : Fˣ := ⟨g.val 0 0,g.val 1 1,hdet,(mul_comm _ _).trans hdet⟩
  refine ⟨a,?_⟩
  ext j k
  fin_cases j <;> fin_cases k <;> simp [a,h10,h01]

/-- Every element of H ∩ Rᵢ uses this SAME pinning's diagonal torus.
The reverse containment, needed for Hᵢ equality, is a separate source step. -/
theorem exists_alignedTorus_of_mem (n : RootReflection Q split i) {x : X ⧸ Q.D}
    (hxH : x ∈ Q.tits.B ⊓ Q.tits.N) (hxR : x ∈ rankOne Q split i) :
    ∃ a : Fˣ, alignedTorus Q split i hV μ n a = x := by
  obtain ⟨g,hg⟩ := (alignedPinningHom_range Q split i hV μ n).symm ▸ hxR
  obtain ⟨a,rfl⟩ := aligned_cartan_diagonal Q split i hV μ n g (hg.symm ▸ hxH)
  exact ⟨a,hg⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
