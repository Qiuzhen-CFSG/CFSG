module
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Automorphisms.Support
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Parameters
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Transport
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Surjectivity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightFaithful

/-!
# Signed octad stabilizers and their actual alternating quotient

An even standard automorphism fixes the octad block pointwise precisely when
it fixes the chosen Parker-loop lift `(c, 0)` and every support position.
The signed-vector equality criterion retains the loop sign and identifies
even subsets only with their complements; faithfulness of the deleted
eight-point action therefore detects the pointwise support condition.

The even subgroup fixing `(c, 0)` maps onto the full Golay support stabilizer:
cocode evaluations at a point inside the octad and one outside independently
correct the octad sign and the all-ones sign. The compatible native M24
comparison in `Automorphisms.Support` then identifies the actual support image
with A8. The literal `psiAut1N` inclusion is faithful on this subgroup, and its
restriction of `blockRepresentation` has precisely the support-action kernel.
Every even support stabilizer element factors into an even cocode actor and
this signed subgroup; `evenBlockInclusion_factor` retains the literal N1 actors.

There is a source-convention obstruction. Section 27, printed p. 144, expressly
makes E the kernel of Gamma's coordinate action. Thus the coordinate pointwise
fixer contains even cocode automorphisms with epsilon_J(c) = 1; these negate the
octad lift and do not belong to the block kernel. The printed shorthand in
29.13(3) cannot literally identify these two kernels under that convention.
`coordinate_fixer_not_block_kernel` proves the obstruction; `blockQuotientEquiv`
provides the adequate signed-stabilizer quotient for the local assembly.

The only additional premise is `EvenStandardFormula`, the explicit signed
conjugation identity of 29.12(1). Its producer is the separate octad conjugation
development, and the source-theorem assembly must discharge it. Support
surjectivity, sign correction, kernel detection, and the alternating quotient
are proved here, without any quotient or group-family hypothesis.

Source: Aschbacher, *Sporadic Groups*, 19.1(3), Section 27 and 29.12–29.13,
printed pp. 85–86, 144 and 160. The imported deleted-module faithfulness is
the licensed ATLAS proof; attribution is retained in its owning module.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Automorphisms
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem eight_even_faithful (σ : Equiv.Perm (Fin 8))
    (h : ∀ v : Atlas.Order20160A8.DeletedEight.evenCode,
      (fun i => v.val (σ.symm i)) = v.val ∨
      (fun i => v.val (σ.symm i)) = v.val + (fun _ => 1)) : σ = 1 := by
  apply Atlas.Order20160A8.DeletedEight.permutationHom_injective
  rw [map_one]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change (Submodule.Quotient.mk (Atlas.Order20160A8.DeletedEight.evenPerm σ v) :
      Atlas.Order20160A8.DeletedEight.W) = Submodule.Quotient.mk v
    apply (Submodule.Quotient.eq _).mpr
    rcases h v with hv | hv
    · have he : Atlas.Order20160A8.DeletedEight.evenPerm σ v = v := Subtype.ext hv
      rw [he, sub_self]
      exact Submodule.zero_mem _
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨1, ?_⟩
      apply Subtype.ext
      change (fun _ : Fin 8 => (1 : Bit)) = (fun i => v.val (σ.symm i)) - v.val
      rw [hv, add_sub_cancel_left]

/-- A permutation of eight positions acting trivially on even subsets modulo
complementation fixes every position. -/
theorem even_subsets_faithful (c : NOctad.Octad) (σ : Equiv.Perm (Support c))
    (h : ∀ J : EvenSubset c, (fun i => J.val (σ.symm i)) = J.val ∨
      (fun i => J.val (σ.symm i)) = J.val + (fun _ => 1)) : σ = 1 := by
  let e : Support c ≃ Fin 8 := Fintype.equivFinOfCardEq (support_card c)
  apply e.permCongr.injective
  rw [show e.permCongr 1 = 1 from e.permCongrHom.map_one]
  apply eight_even_faithful
  intro v
  let J : EvenSubset c := ⟨fun i => v.val (e i), by
    change (∑ i, v.val (e i)) = 0
    rw [Equiv.sum_comp]
    exact v.prop⟩
  rcases h J with hj | hj
  · left
    funext i
    simpa [J, Equiv.permCongr_def] using congrFun hj (e.symm i)
  · right
    funext i
    simpa [J, Equiv.permCongr_def] using congrFun hj (e.symm i)

/-- The literal first standard-automorphism inclusion into `N1`. -/
def standardInclusion : ParkerStandardGroup →* N1 where
  toFun α := ⟨psiAut1N α, psiAut1N_mem_N1 α⟩
  map_one' := Subtype.ext TrialityGeneratorCalculation.aut_one
  map_mul' α β := Subtype.ext (TrialityGeneratorCalculation.aut_mul α β)

@[simp] theorem coordinateRepresentation_standard (α : ParkerStandardGroup) :
    coordinateRepresentation (standardInclusion α) = parkerStandardProjection α := by
  have h : monomialRepresentation (standardInclusion α) =
      SemidirectProduct.inr (parkerStandardProjection α) := by
    apply monomialEmbedding_injective
    rw [monomialRepresentation_embedding]
    change n1LeechRepresentation (standardInclusion α) =
      permutationEmbedding (parkerStandardProjection α)
    exact natural_lift_unique _ _ _ (n1LeechRepresentation_natural _)
      (fun v => (naturalLeechComparison_psiAut1 α v).symm)
  exact congrArg SemidirectProduct.right h

theorem standard_mem_blockStabilizer (c : NOctad.Octad) (α : ParkerStandardGroup) :
    standardInclusion α ∈ blockStabilizer c ↔
      parkerStandardProjection α ∈ supportStabilizer c := by
  rw [mem_supportStabilizer_iff]
  change octadTransport (standardInclusion α) c = c ↔ _
  rw [Subtype.ext_iff]
  change golayPermutationEquiv (coordinateRepresentation (standardInclusion α)) c.val = c.val ↔ _
  rw [coordinateRepresentation_standard]
  rfl

/-- The even support stabilizer still permits sign changes of the loop lift. -/
def evenStabilizer (c : NOctad.Octad) : Subgroup ParkerStandardGroup :=
  parkerStandardPlus ⊓ (supportStabilizer c).comap parkerStandardProjection

/-- Fix the chosen signed lift as well as the distinguished all-ones lift. -/
def signedStabilizer (c : NOctad.Octad) : Subgroup ParkerStandardGroup :=
  parkerStandardPlus ⊓
    (MulAction.stabilizer (Equiv.Perm ParkerLoop) (c.val, (0 : ParkerBit))).comap
      parkerStandardAutomorphisms.subtype

theorem mem_signedStabilizer (c : NOctad.Octad) (α : ParkerStandardGroup) :
    α ∈ signedStabilizer c ↔ α ∈ parkerStandardPlus ∧ α.val (c.val, 0) = (c.val, 0) := Iff.rfl

theorem signedStabilizer_le_even (c : NOctad.Octad) : signedStabilizer c ≤ evenStabilizer c := by
  intro α hα
  refine ⟨hα.1, (mem_supportStabilizer_iff c _).mpr ?_⟩
  exact (parkerStandardProjection_spec α (c.val, 0)).symm.trans
    (congrArg Prod.fst hα.2)

/-- Projection of the signed stabilizer retains the literal support permutation. -/
def signedProjection (c : NOctad.Octad) : signedStabilizer c →* supportStabilizer c :=
  (parkerStandardProjection.comp (signedStabilizer c).subtype).codRestrict _
    (fun α => (signedStabilizer_le_even c α.prop).2)

private theorem exists_outside (c : NOctad.Octad) : ∃ i, c.val.val i = 0 := by
  by_contra hn
  push Not at hn
  have he : c.val.val = allOnes := by
    funext i
    exact (bit_cases (c.val.val i)).resolve_left (hn i)
  have hc := c.prop
  rw [he] at hc
  have hall : hammingNorm allOnes = 24 := by decide +kernel
  omega

/-- Independent sign corrections on the octad lift and the all-ones lift. -/
theorem sign_correction (c : NOctad.Octad) (s t : ParkerBit) :
    ∃ d : Cocode, cocodePairing c.val d = s ∧ cocodePairing golayOne d = t := by
  let i : Support c := Classical.choice inferInstance
  obtain ⟨j, hj⟩ := exists_outside c
  have hi : c.val.val i.val = 1 := (bit_cases _).resolve_left i.prop
  let w : BinaryWord := Pi.single i.val s + Pi.single j (t + s)
  refine ⟨Submodule.Quotient.mk w, ?_, ?_⟩
  · change cocodeDualEquiv (Submodule.Quotient.mk w) c.val = s
    rw [cocodeDualEquiv_mk]
    simp [w, binaryDot, mul_add, hi, hj]
  · change cocodeDualEquiv (Submodule.Quotient.mk w) golayOne = t
    rw [cocodeDualEquiv_mk]
    have he : s + t + s = t := by
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    simpa [w, binaryDot, mul_add, golayOne, allOnes, ← add_assoc] using he

/-- Every support stabilizer lifts while independently fixing both loop signs. -/
theorem signedProjection_surjective (c : NOctad.Octad) : Function.Surjective (signedProjection c) := by
  intro g
  obtain ⟨α, hα⟩ := parkerStandardProjection_surjective g.val
  have hc : (α.val (c.val, 0)).1 = c.val := by
    rw [parkerStandardProjection_spec, hα]
    exact (mem_supportStabilizer_iff c g.val).mp g.prop
  obtain ⟨d, hd, ht⟩ := sign_correction c (α.val (c.val, 0)).2 (α.val parkerOmega).2
  let β := parkerCocodeStandard d * α
  have hb : β ∈ signedStabilizer c := by
    apply (mem_signedStabilizer c β).mpr
    constructor
    · apply (parkerStandardPlus_iff β).mpr
      change (parkerCocodeStandard d).val (α.val parkerOmega) = parkerOmega
      rw [parkerCocodeStandard_apply, parkerStandard_omega_first, ht,
        CharTwo.add_self_eq_zero]
      rfl
    · change (parkerCocodeStandard d).val (α.val (c.val, 0)) = (c.val, 0)
      rw [parkerCocodeStandard_apply, hc, hd, CharTwo.add_self_eq_zero]
  refine ⟨⟨β, hb⟩, Subtype.ext ?_⟩
  change parkerStandardProjection (parkerCocodeStandard d * α) = g.val
  rw [map_mul, parkerCocodeStandard_projection, one_mul, hα]

/-- The support action of the genuine even signed-lift stabilizer. -/
def signedSupportAction (c : NOctad.Octad) : signedStabilizer c →* Equiv.Perm (Support c) :=
  (supportAction c).comp (signedProjection c)

theorem signedSupportAction_range (c : NOctad.Octad) :
    (signedSupportAction c).range = alternatingGroup (Support c) := by
  rw [← supportAction_range c]
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    exact ⟨signedProjection c α, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨α, rfl⟩ := signedProjection_surjective c g
    exact ⟨α, rfl⟩

def alternatingAction (c : NOctad.Octad) : signedStabilizer c →* alternatingGroup (Support c) :=
  (signedSupportAction c).codRestrict _ (fun α => signedSupportAction_range c ▸ ⟨α, rfl⟩)

theorem alternatingAction_surjective (c : NOctad.Octad) : Function.Surjective (alternatingAction c) := by
  intro p
  have hp : p.val ∈ (signedSupportAction c).range := by
    rw [signedSupportAction_range]
    exact p.prop
  obtain ⟨α, hα⟩ := hp
  exact ⟨α, Subtype.ext hα⟩

theorem alternatingAction_kernel (c : NOctad.Octad) :
    (alternatingAction c).ker = (signedSupportAction c).ker := by
  ext α
  change (alternatingAction c α = 1) ↔ _
  exact Subtype.ext_iff

/-- The signed stabilizer modulo its pointwise support kernel is genuinely A8. -/
def supportQuotientEquiv (c : NOctad.Octad) :
    signedStabilizer c ⧸ (signedSupportAction c).ker ≃* alternatingGroup (Support c) :=
  (QuotientGroup.quotientMulEquivOfEq (alternatingAction_kernel c).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (alternatingAction c)
      (alternatingAction_surjective c))

/-- The same quotient written on eight numbered positions. -/
def supportQuotientEquivA8 (c : NOctad.Octad) :
    signedStabilizer c ⧸ (signedSupportAction c).ker ≃* alternatingGroup (Fin 8) :=
  (supportQuotientEquiv c).trans
    (Fintype.equivFinOfCardEq (support_card c)).altCongrHom


/-- Signed octad vectors detect both the loop sign and every support position. -/
theorem standardParameters_fixed_iff (c : NOctad.Octad) (α : ParkerStandardGroup) :
    (∀ p : OctadParameters, p.c.1 = c.val → vector (standardParameters α p) = vector p) ↔
      α.val (c.val, 0) = (c.val, 0) ∧
      ∀ i : Support c, (parkerStandardProjection α).val i.val = i.val := by
  constructor
  · intro h
    have hc := ((vector_eq_iff _ _).mp (h (parameters c 0 0) rfl)).1
    change α.val (c.val, 0) = (c.val, 0) at hc
    refine ⟨hc, ?_⟩
    have hg : parkerStandardProjection α ∈ supportStabilizer c := by
      apply (mem_supportStabilizer_iff c _).mpr
      exact (parkerStandardProjection_spec α (c.val, 0)).symm.trans (congrArg Prod.fst hc)
    let g : supportStabilizer c := ⟨parkerStandardProjection α, hg⟩
    have hs : supportAction c g = 1 := by
      apply even_subsets_faithful
      intro J
      have hj := ((vector_eq_iff _ _).mp (h (parameters c J 0) rfl)).2
      rcases hj with hj | hj
      · left
        funext i
        have he := congrFun hj i.val
        change subsetWord c J ((supportAction c g).symm i).val = subsetWord c J i.val at he
        simpa only [subsetWord_support] using he
      · right
        funext i
        have he := congrFun hj i.val
        change subsetWord c J ((supportAction c g).symm i).val =
          subsetWord c J i.val + c.val.val i.val at he
        have hi : c.val.val i.val = 1 := (bit_cases _).resolve_left i.prop
        change J.val ((supportAction c g).symm i) = J.val i + 1
        simpa only [subsetWord_support, hi] using he
    exact fun i => congrArg Subtype.val (Equiv.congr_fun hs i)
  · rintro ⟨hc, hi⟩ p hp
    apply (vector_eq_iff _ _).mpr
    constructor
    · have he : p.c = parkerSign p.c.2 (c.val, 0) := by
        apply Prod.ext hp
        simp [parkerSign]
      change α.val p.c = p.c
      rw [he, parkerStandard_preserves_sign, hc]
    · left
      change coordinatePermutation (parkerStandardProjection α).val p.J = p.J
      funext i
      change p.J ((parkerStandardProjection α).val.symm i) = p.J i
      by_cases hci : c.val.val i ≠ 0
      · have he := hi ⟨i, hci⟩
        have he' : (parkerStandardProjection α).val.symm i = i :=
          (Equiv.symm_apply_eq _).mpr he.symm
        rw [he']
      · have hz : p.J i = 0 := by
          by_contra hn
          exact hci (hp ▸ p.supported i hn)
        rw [hz]
        by_contra hn
        have hj : c.val.val ((parkerStandardProjection α).val.symm i) ≠ 0 :=
          hp ▸ p.supported _ hn
        have he := hi ⟨_, hj⟩
        rw [Equiv.apply_symm_apply] at he
        exact hci (he.symm ▸ hj)

/-- The exact signed formula from 29.12(1), the sole conjugation premise here.
Its producer is the octad conjugation development. -/
def EvenStandardFormula : Prop :=
  ∀ α : ParkerStandardGroup, α ∈ parkerStandardPlus → ∀ p : OctadParameters,
    q1ImageConjugation (standardInclusion α) (rOctad p).val =
      (rOctad (standardParameters α p)).val

theorem representation_standard_of_formula (h : EvenStandardFormula)
    (α : ParkerStandardGroup) (hα : α ∈ parkerStandardPlus) (p : OctadParameters) :
    representation (standardInclusion α) (vector p) = vector (standardParameters α p) :=
  (representation_vector_eq_iff _ _ _).mpr (h α hα p)

/-- Restriction of the literal standard inclusion to the even block stabilizer. -/
def evenBlockInclusion (c : NOctad.Octad) : evenStabilizer c →* blockStabilizer c :=
  (standardInclusion.comp (evenStabilizer c).subtype).codRestrict _
    (fun α => (standard_mem_blockStabilizer c α.val).mpr α.prop.2)

/-- The relative kernel retains the signed-lift condition lost by the coordinate action. -/
theorem even_block_kernel_iff (h : EvenStandardFormula) (c : NOctad.Octad)
    (α : evenStabilizer c) :
    evenBlockInclusion c α ∈ (blockRepresentation c).ker ↔
      α.val.val (c.val, 0) = (c.val, 0) ∧
      ∀ i : Support c, (parkerStandardProjection α.val).val i.val = i.val := by
  rw [blockRepresentation_kernel_iff, ← standardParameters_fixed_iff]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  rw [← representation_vector_eq_iff]
  exact (congrArg (· = vector p) (representation_standard_of_formula h α.val α.prop.1 p)).to_iff

/-- The literal signed stabilizer acting on the actual block submodule. -/
def signedBlockInclusion (c : NOctad.Octad) : signedStabilizer c →* blockStabilizer c :=
  (evenBlockInclusion c).comp (Subgroup.inclusion (signedStabilizer_le_even c))

def signedBlockRepresentation (c : NOctad.Octad) :
    Representation ℝ (signedStabilizer c) (block c) :=
  (blockRepresentation c).comp (signedBlockInclusion c)

/-- Application to the inherited Griess action, with the actual `psiAut1N` actor. -/
theorem signedBlockRepresentation_inclusion (c : NOctad.Octad)
    (α : signedStabilizer c) (v : block c) :
    blockInclusion c (signedBlockRepresentation c α v) =
      cRepresentation (n1ToC (standardInclusion α.val)) (blockInclusion c v) :=
  blockRepresentation_inclusion c (signedBlockInclusion c α) v

/-- On the signed-lift stabilizer the block and pointwise support kernels coincide. -/
theorem signedBlockRepresentation_kernel (h : EvenStandardFormula) (c : NOctad.Octad) :
    (signedBlockRepresentation c).ker = (signedSupportAction c).ker := by
  ext α
  change evenBlockInclusion c (Subgroup.inclusion (signedStabilizer_le_even c) α) ∈
    (blockRepresentation c).ker ↔ signedProjection c α ∈ (supportAction c).ker
  rw [even_block_kernel_iff h, supportAction_kernel_iff]
  exact and_iff_right α.prop.2

/-- The quotient by the literal block kernel is the actual alternating support group. -/
def blockQuotientEquiv (h : EvenStandardFormula) (c : NOctad.Octad) :
    signedStabilizer c ⧸ (signedBlockRepresentation c).ker ≃* alternatingGroup (Support c) :=
  (QuotientGroup.quotientMulEquivOfEq (signedBlockRepresentation_kernel h c)).trans
    (supportQuotientEquiv c)

/-- Explicit obstruction to identifying the coordinate pointwise fixer with the
block kernel: an even cocode automorphism fixes all coordinates and negates the octad lift. -/
theorem coordinate_fixer_not_block_kernel (h : EvenStandardFormula) (c : NOctad.Octad) :
    ∃ α : evenStabilizer c, parkerStandardProjection α.val = 1 ∧
      evenBlockInclusion c α ∉ (blockRepresentation c).ker := by
  obtain ⟨d, hd, ht⟩ := sign_correction c 1 0
  let α := parkerCocodeStandard d
  have hp : α ∈ parkerStandardPlus := by
    apply (parkerStandardPlus_iff α).mpr
    change (golayOne, 0 + cocodePairing golayOne d) = parkerOmega
    rw [ht, add_zero]
    rfl
  have hc : α ∈ evenStabilizer c :=
    ⟨hp, by change parkerStandardProjection α ∈ supportStabilizer c
            rw [parkerCocodeStandard_projection]
            exact (supportStabilizer c).one_mem⟩
  refine ⟨⟨α, hc⟩, parkerCocodeStandard_projection d, ?_⟩
  rw [even_block_kernel_iff h]
  intro he
  have hs := congrArg Prod.snd he.1
  change 0 + cocodePairing c.val d = 0 at hs
  rw [hd, zero_add] at hs
  exact one_ne_zero hs


/-- The quotient equivalence is induced by restriction of the actual support permutation. -/
@[simp] theorem supportQuotientEquiv_mk (c : NOctad.Octad) (α : signedStabilizer c) :
    supportQuotientEquiv c (QuotientGroup.mk α) = alternatingAction c α := rfl

/-- The block quotient map likewise retains the literal support action. -/
@[simp] theorem blockQuotientEquiv_mk (h : EvenStandardFormula) (c : NOctad.Octad)
    (α : signedStabilizer c) :
    blockQuotientEquiv h c (QuotientGroup.mk α) = alternatingAction c α := rfl

/-- For the sign subgroup E, the additional block-kernel condition is exactly
its cocode pairing with the octad. -/
theorem cocode_block_kernel_iff (h : EvenStandardFormula) (c : NOctad.Octad)
    (α : evenStabilizer c) (d : Cocode) (hα : α.val = parkerCocodeStandard d) :
    evenBlockInclusion c α ∈ (blockRepresentation c).ker ↔ cocodePairing c.val d = 0 := by
  rw [even_block_kernel_iff h, hα]
  simp [parkerCocodeStandard_apply, parkerCocodeStandard_projection]

/-- In the book's subset notation, the missing condition is epsilon_J(c) = 0. -/
theorem cocodeWord_block_kernel_iff (h : EvenStandardFormula) (c : NOctad.Octad)
    (α : evenStabilizer c) (J : BinaryWord)
    (hα : α.val = parkerCocodeStandard (Submodule.Quotient.mk J)) :
    evenBlockInclusion c α ∈ (blockRepresentation c).ker ↔ binaryDot J c.val.val = 0 := by
  rw [cocode_block_kernel_iff h c α _ hα, cocodePairing, cocodeDualEquiv_mk,
    binaryDot_symmetric]

/-- Faithfulness of the literal inclusion on even standard automorphisms. -/
theorem standardInclusion_injective_on_even (α β : ParkerStandardGroup)
    (hα : α ∈ parkerStandardPlus) (hβ : β ∈ parkerStandardPlus)
    (he : standardInclusion α = standardInclusion β) : α = β := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he' := congrArg (fun g : N1 => g.val.val) he
  change psiAut1 α.val = psiAut1 β.val at he'
  rw [psiAut1, if_pos ((parkerStandardPlus_iff α).mp hα),
    psiAut1, if_pos ((parkerStandardPlus_iff β).mp hβ)] at he'
  have hx := congrArg Prod.fst (Equiv.congr_fun he' (some x, none, none))
  exact Option.some.inj hx

/-- Thus the signed actor really is a subgroup of the literal block stabilizer. -/
theorem signedBlockInclusion_injective (c : NOctad.Octad) :
    Function.Injective (signedBlockInclusion c) := by
  intro α β he
  apply Subtype.ext
  exact standardInclusion_injective_on_even α.val β.val α.prop.1 β.prop.1
    (congrArg Subtype.val he)


/-- The quotient by the literal block kernel, on eight numbered support positions. -/
def blockQuotientEquivA8 (h : EvenStandardFormula) (c : NOctad.Octad) :
    signedStabilizer c ⧸ (signedBlockRepresentation c).ker ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq (signedBlockRepresentation_kernel h c)).trans
    (supportQuotientEquivA8 c)

/-- Replacing the even support stabilizer by its signed-lift subgroup loses only
an even element of E, already among the local cocode actors. -/
theorem evenStabilizer_factor (c : NOctad.Octad) (α : evenStabilizer c) :
    ∃ d : Cocode, cocodePairing golayOne d = 0 ∧
      ∃ β : signedStabilizer c, α.val = parkerCocodeStandard d * β.val := by
  obtain ⟨β, hβ⟩ := signedProjection_surjective c ⟨parkerStandardProjection α.val, α.prop.2⟩
  have hp : parkerStandardProjection β.val = parkerStandardProjection α.val :=
    congrArg Subtype.val hβ
  let γ : ParkerStandardGroup := α.val * β.val⁻¹
  have hg : γ ∈ parkerStandardProjection.ker := by
    change parkerStandardProjection (α.val * β.val⁻¹) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  have heven : γ ∈ parkerStandardPlus :=
    parkerStandardPlus.mul_mem α.prop.1 (parkerStandardPlus.inv_mem β.prop.1)
  obtain ⟨d, hd⟩ := parkerCocodeKernelHom_surjective ⟨γ, hg⟩
  have he : parkerCocodeStandard d.toAdd = γ := congrArg Subtype.val hd
  refine ⟨d.toAdd, ?_, β, ?_⟩
  · have ho := (parkerStandardPlus_iff γ).mp heven
    rw [← he, parkerCocodeStandard_apply] at ho
    have hh := congrArg Prod.snd ho
    exact (zero_add _).symm.trans hh
  · rw [he]
    simp [γ, mul_assoc]

/-- The factorization applied to the literal local actors in `N1`. -/
theorem evenBlockInclusion_factor (c : NOctad.Octad) (α : evenStabilizer c) :
    ∃ d : Cocode, cocodePairing golayOne d = 0 ∧
      ∃ β : signedStabilizer c, (evenBlockInclusion c α).val =
        standardInclusion (parkerCocodeStandard d) * (signedBlockInclusion c β).val := by
  obtain ⟨d, hd, β, hβ⟩ := evenStabilizer_factor c α
  refine ⟨d, hd, β, ?_⟩
  change standardInclusion α.val =
    standardInclusion (parkerCocodeStandard d) * standardInclusion β.val
  rw [hβ, map_mul]

end Sporadic.Monster.Construction.NOctad.LocalStructure.Automorphisms
