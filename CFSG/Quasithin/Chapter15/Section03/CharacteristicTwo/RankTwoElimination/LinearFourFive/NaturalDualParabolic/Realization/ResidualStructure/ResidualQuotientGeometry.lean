module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.ResidualGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.RadicalFactor
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Opposing marked factors in the residual central quotient

Let P be the point parabolic in the actual natural-plus-dual model, D its
two-residual, and K = [O₂(D),D]. Chiefness of the original radical interval
shows that K has the full point-radical image. The embedded natural four-space
lies in K, its intersection with Z(K) is the fixed line, and Z(K) acts trivially
on it. Thus V/⟨x⟩ injects into K/Z(K), while K/Z(K) surjects onto its dual.

Both maps intertwine literal conjugation by P with the same original
quotientActor. Restriction to D retains the full quotient action. No equality
between K and [O₂(P),P] is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public noncomputable section
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
open ChiefLayers
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

/-- The literal intrinsic residual commutator in the original ambient group. -/
abbrev residualCore (h : NaturalDual d L) (x : Space 4) : Subgroup G :=
  ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
    Stellmacher.twoResidualAmbient (point h x)⁆

theorem residualCore_le_pointCore (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    residualCore h x ≤ (point h x).pCoreIn 2 :=
  (residualCore_le_coreCommutator h hx).trans (coreCommutator_le _)

theorem residualCore_le_point (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    residualCore h x ≤ point h x := (residualCore_le_pointCore h hx).trans (pCoreIn_le _ _)

theorem residualCore_normalized (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    point h x ≤ normalizer (residualCore h x : Set G) := by
  have he : residualCore h x =
      ⁅(point h x).pCoreIn 2,Stellmacher.twoResidualAmbient (point h x)⁆ :=
    residual_core_commutator_eq h hx
  rw [he]
  exact (point_eq_residual_sup_componentCore h hx).le.trans
    (sup_le (normalizer_commutator_ge_right _ _)
      ((componentCore_le_pointCore h x).trans (normalizer_commutator_ge_left _ _)))

/-- Chiefness of the marked radical forces it to be covered by the old core
and the literal residual commutator. -/
theorem pointCore_eq_componentCore_sup_residualCore (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (point h x).pCoreIn 2 = L.pCoreIn 2 ⊔ residualCore h x := by
  let J := L.pCoreIn 2 ⊔ residualCore h x
  have hJn : (J.subgroupOf (point h x)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact (le_inf ((point_le h x).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))) (residualCore_normalized h hx)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJE : J ≤ (point h x).pCoreIn 2 :=
    sup_le (componentCore_le_pointCore h x) (residualCore_le_pointCore h hx)
  have hc := radical_interval_chief h hx
  rcases hc.chief J le_sup_left hJE hJn with he | he
  · exfalso
    apply hc.noncentral
    rw [commutator_comm]
    change coreCommutator (point h x) ≤ L.pCoreIn 2
    rw [coreCommutator_eq_residualCore_sup_componentDerived h hx]
    exact sup_le (by change residualCore h x ≤ _; rw [←he]; exact le_sup_right)
      (commutator_le_self _)
  · exact he.symm

/-- The actual point-core marking is onto the geometric radical. -/
theorem pointCore_pointActor_image (h : NaturalDual d L) (x : Space 4) :
    (((point h x).pCoreIn 2).subgroupOf (point h x)).map (pointActor h x) = pointKernel x := by
  change (((pCore 2 (point h x)).map (point h x).subtype).comap (point h x).subtype).map _ = _
  rw [comap_map_eq_self_of_injective (point h x).subtype_injective]
  ext g
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact point_core_actor h x p hp
  · intro hg
    obtain ⟨q,hq⟩ := coreActor_surjective h x ⟨g,hg⟩
    exact ⟨q.val,q.property,congrArg Subtype.val hq⟩

/-- The intrinsic residual core has the full radical image under the original
pointActor; its source is not replaced by the larger parabolic commutator. -/
theorem residualCore_pointActor_image (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    ((residualCore h x).subgroupOf (point h x)).map (pointActor h x) = pointKernel x := by
  have he := congrArg (fun A : Subgroup G => (A.subgroupOf (point h x)).map (pointActor h x))
    (pointCore_eq_componentCore_sup_residualCore h hx)
  rw [pointCore_pointActor_image,subgroupOf_sup (componentCore_le_point h x)
    (residualCore_le_point h hx),Subgroup.map_sup,←pointActor_ker,Subgroup.map_ker_self] at he
  simpa using he.symm

/-- Restrict the original quotient action to the actual residual core. -/
def residualCoreActor (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    residualCore h x →* pointKernel x :=
  ((pointActor h x).comp (inclusion (residualCore_le_point h hx))).codRestrict _ (by
    intro k
    rw [←residualCore_pointActor_image h hx]
    exact mem_map.mpr ⟨⟨k,residualCore_le_point h hx k.property⟩,k.property,rfl⟩)

theorem residualCoreActor_surjective (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Function.Surjective (residualCoreActor h hx) := by
  rintro ⟨g,hg⟩
  rw [←residualCore_pointActor_image h hx] at hg
  obtain ⟨p,hp,he⟩ := hg
  exact ⟨⟨p,hp⟩,Subtype.ext he⟩

/-- The embedded natural summand is already in the intrinsic residual core. -/
theorem naturalSubgroup_le_residualCore (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    naturalSubgroup h ≤ residualCore h x := by
  rintro _ ⟨v,hv,rfl⟩
  apply movedSpace_mem_residualCore h hx hU v.toAdd
  rw [show v.toAdd.2 = 0 from hv.2]
  exact Submodule.zero_mem _

omit [Finite G] in
private theorem mem_line_of_kernel_fixed {x v : Space 4} (hx : x ≠ 0)
    (hv : ∀g : pointKernel x, g.val.val v = v) : v ∈ line x := by
  by_contra hn
  have hq : (line x).mkQ v ≠ 0 := fun he => hn ((Submodule.Quotient.mk_eq_zero _).mp he)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let w : line x := ⟨x,Submodule.mem_span_singleton_self x⟩
  have he := hv (kernelShear x (f.smulRight w))
  rw [kernelShear_apply] at he
  change v + f ((line x).mkQ v) • x = v at he
  rw [hf,one_smul] at he
  exact hx (add_left_cancel (he.trans (add_zero v).symm))

/-- The center meets the original natural four-space in exactly its marked
fixed line. Both sides are subgroups of the original ambient group. -/
theorem residualCore_center_inf_natural (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    (center (residualCore h x)).map (residualCore h x).subtype ⊓ naturalSubgroup h =
      lineSubgroup h x := by
  apply le_antisymm
  · rintro a ⟨haz,han⟩
    obtain ⟨v,hv,rfl⟩ := han
    have hvzero : v.toAdd.2=0 := hv.2
    apply (embed_mem_coordinateSubgroup h (lineSpace x) v.toAdd).mpr
    refine ⟨mem_line_of_kernel_fixed hx ?_,hvzero⟩
    intro g
    obtain ⟨k,hk⟩ := residualCoreActor_surjective h hx g
    obtain ⟨z,hz,hez⟩ := haz
    have hcomm := congrArg (fun b : residualCore h x => (b:G)) ((mem_center_iff.mp hz) k)
    change (k:G)*(z:G)=(z:G)*(k:G) at hcomm
    change (z:G)=embed h v at hez
    rw [hez] at hcomm
    have hconj : (k:G)*embed h v*(k:G)⁻¹=embed h v := by rw [hcomm,mul_inv_cancel_right]
    have hc := embed_conj h (⟨k,(residualCore_le_point h hx).trans (point_le h x) k.property⟩:L) v.toAdd
    change (k:G)*embed h v*(k:G)⁻¹ = embed h (Multiplicative.ofAdd
      (BinaryLinear.NaturalDualFlag.action
        (linearAction (by decide) h.model ⟨k,(residualCore_le_point h hx).trans (point_le h x) k.property⟩)
        v.toAdd)) at hc
    rw [hconj] at hc
    have he := congrArg (fun w : Multiplicative (Space 4 × Module.Dual (ZMod 2) (Space 4)) => w.toAdd.1)
      (embed_injective h hc)
    simp only [toAdd_ofAdd,BinaryLinear.NaturalDualFlag.action_fst] at he
    have hg := congrArg (fun q : pointKernel x => q.val.val v.toAdd.1) hk
    exact hg.symm.trans he.symm
  · apply le_inf _ (lineSubgroup_le_natural h x)
    apply (le_trans ?_ (centralSubgroup_le_residualCore_center h hx hU))
    apply map_mono
    intro v hv
    exact ⟨hv.1,by rw [show v.toAdd.2=0 from hv.2];exact Submodule.zero_mem _⟩

/-- Every central element acts trivially on the original natural space, so the
point radical projection kills the full center. -/
theorem residualCore_center_le_actor_ker (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    center (residualCore h x) ≤ (residualCoreActor h hx).ker := by
  intro z hz
  change residualCoreActor h hx z = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  let b := (naturalCoordinates h).symm (Multiplicative.ofAdd v)
  let k : residualCore h x := inclusion (naturalSubgroup_le_residualCore h hx hU) b
  have hc := congrArg (fun a : residualCore h x => (a:G)) ((mem_center_iff.mp hz) k)
  have hb : conjugate _ _ (naturalSubgroup_normalized h x)
      (inclusion (residualCore_le_point h hx) z) b = b := by
    apply Subtype.ext
    change (z:G)*(b:G)*(z:G)⁻¹=(b:G)
    change (b:G)*(z:G)=(z:G)*(b:G) at hc
    rw [←hc,mul_inv_cancel_right]
  rw [naturalCoordinates_conj] at hb
  exact congrArg Multiplicative.toAdd ((naturalCoordinates h).symm.injective hb)

/-- Covectors obtained from the original residual core by the marked displacement. -/
def residualCoreDualProjection (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    residualCore h x →* Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  ((radicalDisplacementDual hx).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (kernelDisplacementEquiv x).toMonoidHom).comp (residualCoreActor h hx)

theorem residualCoreDualProjection_surjective (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) : Function.Surjective (residualCoreDualProjection h hx) :=
  (radicalDisplacementDual hx).toAddEquiv.toMultiplicative.surjective.comp
    ((kernelDisplacementEquiv x).surjective.comp (residualCoreActor_surjective h hx))

theorem residualCoreDualProjection_eq_ambient (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (k : residualCore h x) :
    residualCoreDualProjection h hx k = ambientRadicalProjection h hx
      (inclusion (residualCore_le_pointCore h hx) k) := by
  let q := inclusion (residualCore_le_pointCore h hx) k
  have he := congrArg (fun a : (point h x).pCoreIn 2 => (a:G))
    ((radicalCoreEquiv h x).apply_symm_apply q)
  have ha : coreActor h x ((radicalCoreEquiv h x).symm q) = residualCoreActor h hx k := by
    apply Subtype.ext
    apply congrArg (pointActor h x)
    exact Subtype.ext he
  change _ = (radicalDisplacementDual hx).toAddEquiv.toMultiplicative
    (kernelDisplacementEquiv x (coreActor h x ((radicalCoreEquiv h x).symm q)))
  rw [ha]
  rfl

/-- The residual covector projection intertwines literal ambient conjugation. -/
theorem residualCoreDualProjection_conj (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (p : point h x) (k : residualCore h x) :
    (residualCoreDualProjection h hx (conjugate _ _ (residualCore_normalized h hx) p k)).toAdd =
      (quotientActor h x p).symm.dualMap (residualCoreDualProjection h hx k).toAdd := by
  rw [residualCoreDualProjection_eq_ambient,residualCoreDualProjection_eq_ambient]
  exact ambientRadicalProjection_conj h hx p (inclusion (residualCore_le_pointCore h hx) k)

theorem residualCore_center_le_dual_ker (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    center (residualCore h x) ≤ (residualCoreDualProjection h hx).ker := by
  intro z hz
  have he := residualCore_center_le_actor_ker h hx hU hz
  change residualCoreActor h hx z = 1 at he
  change (radicalDisplacementDual hx).toAddEquiv.toMultiplicative
    (kernelDisplacementEquiv x (residualCoreActor h hx z)) = 1
  rw [he,map_one,map_one]

/-- The actual central quotient surjects onto the marked dual three-space. -/
def residualCentralDualProjection (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    (residualCore h x ⧸ center (residualCore h x)) →*
      Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  QuotientGroup.lift _ (residualCoreDualProjection h hx) (residualCore_center_le_dual_ker h hx hU)

theorem residualCentralDualProjection_surjective (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    Function.Surjective (residualCentralDualProjection h hx hU) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (residualCoreDualProjection_surjective h hx) _

@[simp] theorem residualCentralDualProjection_mk (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (k : residualCore h x) :
    residualCentralDualProjection h hx hU (QuotientGroup.mk' _ k) =
      residualCoreDualProjection h hx k := rfl

/-- The natural four-space maps to the actual residual central quotient. -/
def naturalCentralProjection (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    naturalSubgroup h →* (residualCore h x ⧸ center (residualCore h x)) :=
  (QuotientGroup.mk' _).comp (inclusion (naturalSubgroup_le_residualCore h hx hU))

theorem naturalCentralProjection_ker (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    (naturalCentralProjection h hx hU).ker = (lineSubgroup h x).subgroupOf (naturalSubgroup h) := by
  ext b
  change QuotientGroup.mk' _ (inclusion (naturalSubgroup_le_residualCore h hx hU) b) = 1 ↔ _
  change (↑(inclusion (naturalSubgroup_le_residualCore h hx hU) b) :
    residualCore h x ⧸ center (residualCore h x)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change inclusion (naturalSubgroup_le_residualCore h hx hU) b ∈ center (residualCore h x) ↔
    (b:G) ∈ lineSubgroup h x
  rw [←residualCore_center_inf_natural h hx hU]
  constructor
  · intro hb
    exact ⟨mem_map.mpr ⟨_,hb,rfl⟩,b.property⟩
  · rintro ⟨⟨z,hz,he⟩,_⟩
    have hz' : z = inclusion (naturalSubgroup_le_residualCore h hx hU) b := Subtype.ext he
    exact hz' ▸ hz

/-- The natural three-space embeds in the same actual central quotient. -/
def naturalIntoResidualCentral (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    Multiplicative (pointQuotient x) →* (residualCore h x ⧸ center (residualCore h x)) :=
  (QuotientGroup.lift _ (naturalCentralProjection h hx hU)
    (naturalCentralProjection_ker h hx hU).ge).comp (naturalQuotientEquiv h x).symm.toMonoidHom

theorem naturalIntoResidualCentral_injective (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    Function.Injective (naturalIntoResidualCentral h hx hU) :=
  ((QuotientGroup.injective_lift_iff _ (naturalCentralProjection h hx hU)
    (naturalCentralProjection_ker h hx hU).ge).mpr (naturalCentralProjection_ker h hx hU).symm).comp
    (naturalQuotientEquiv h x).symm.injective

@[simp] theorem naturalIntoResidualCentral_projection (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (b : naturalSubgroup h) :
    naturalIntoResidualCentral h hx hU (naturalProjection h x b) =
      naturalCentralProjection h hx hU b := by
  change QuotientGroup.lift _ (naturalCentralProjection h hx hU)
    (naturalCentralProjection_ker h hx hU).ge ((naturalQuotientEquiv h x).symm
    (naturalQuotientEquiv h x (QuotientGroup.mk' _ b))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The original point parabolic acts on the literal central quotient. -/
def residualCentralActor (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    point h x →* MulAut (residualCore h x ⧸ center (residualCore h x)) :=
  (quotientAut (center (residualCore h x))).comp
    ((residualCore h x).normalizerMonoidHom.comp (inclusion (residualCore_normalized h hx)))

@[simp] theorem residualCentralActor_mk (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (p : point h x) (k : residualCore h x) :
    residualCentralActor h hx p (QuotientGroup.mk' _ k) =
      QuotientGroup.mk' _ (conjugate _ _ (residualCore_normalized h hx) p k) := by
  exact quotientAut_apply_mk _ _ _

/-- The injection is natural for the original quotientActor marking. -/
theorem naturalIntoResidualCentral_equivariant (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (p : point h x) (v : Multiplicative (pointQuotient x)) :
    residualCentralActor h hx p (naturalIntoResidualCentral h hx hU v) =
      naturalIntoResidualCentral h hx hU (Multiplicative.ofAdd (quotientActor h x p v.toAdd)) := by
  obtain ⟨b,rfl⟩ := naturalProjection_surjective h x v
  have he := congrArg Multiplicative.ofAdd (naturalProjection_conj h x p b)
  simp only [ofAdd_toAdd] at he
  rw [←he,naturalIntoResidualCentral_projection,naturalIntoResidualCentral_projection]
  change residualCentralActor h hx p (QuotientGroup.mk' _ (inclusion _ b)) = _
  rw [residualCentralActor_mk]
  rfl

/-- The surjection is contragredient for precisely the same quotientActor. -/
theorem residualCentralDualProjection_equivariant (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (p : point h x) (q : residualCore h x ⧸ center (residualCore h x)) :
    (residualCentralDualProjection h hx hU (residualCentralActor h hx p q)).toAdd =
      (quotientActor h x p).symm.dualMap (residualCentralDualProjection h hx hU q).toAdd := by
  induction q using Quotient.inductionOn with
  | h k =>
    change (residualCentralDualProjection h hx hU
      (residualCentralActor h hx p (QuotientGroup.mk' _ k))).toAdd = _
    rw [residualCentralActor_mk,residualCentralDualProjection_mk]
    exact residualCoreDualProjection_conj h hx p k

/-- The original residual is included in its original point parabolic. -/
def residualPointInclusion (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Stellmacher.twoResidualAmbient (point h x) →* point h x :=
  inclusion (le_sup_left.trans (point_eq_residual_sup_componentCore h hx).ge)

/-- The point action remains surjective upon restricting to the literal residual. -/
theorem residualPointActor_surjective (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Function.Surjective ((pointActor h x).comp (residualPointInclusion h hx)) := by
  intro g
  have hg : g ∈ (pResidual 2 (point h x)).map (pointActor h x) := by
    rw [pointActor_residual_image h hx]
    exact mem_top _
  obtain ⟨p,hp,he⟩ := hg
  have hpD : (p:G) ∈ Stellmacher.twoResidualAmbient (point h x) := by
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact mem_map.mpr ⟨p,hp,rfl⟩
  exact ⟨⟨p,hpD⟩,he⟩

/-- The common natural and contragredient marking on the original residual. -/
def residualQuotientActor (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Stellmacher.twoResidualAmbient (point h x) →* BinaryLinear.GL (pointQuotient x) :=
  (quotientActor h x).comp (residualPointInclusion h hx)

theorem residualQuotientActor_surjective (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Function.Surjective (residualQuotientActor h hx) :=
  (quotientAction_surjective x).comp (residualPointActor_surjective h hx)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
