module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.HexadPullback
public import Theory.GroupTheory.Commutator.CentralCoprimeIndexTransfer
public import Theory.GroupTheory.CubicCentralRestriction

/-!
# The triple-cover restriction to the canonical hexad component

Let C = K/O₂(K) be quasisimple with center of order three, and let the
actual quotient K/O₂,Z(K) be identified with the concrete M₂₂. For every
hexad, its canonical lifted solvable residual, modulo its own two-core,
is quasisimple with cubic center and central quotient A₆.

The hexad stabilizer has index 77. Transfer in the perfect group C puts
its cubic center in the derived subgroup of the inverse image. Coprime
central lifting splits the native elementary two-kernel; the resulting
central cover of A₆ is perfect. Its residual has precisely a two-group
kernel, giving the required quotient by O₂. The original cubic center
lies in that residual and intersects its two-core trivially.

All maps use the supplied M₂₂ isomorphism and the actual hexad action.
The central quotient isomorphism agrees with `hexadSixProjection` on
representatives. The full six-point kernel is O₂,Z of the residual; its
two-core is exactly the residual's two-core. This does not equate the
full six-point kernel with a two-group.

Source: Aschbacher--Smith, 13.8.21(2), combined manuscript of 1 March 2004,
printed p.956 (PDF p.973), the passage from M̂₂₂ to Â₆. The invariant
hexad selection and its placement in the local family are separate.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
variable {G : Type*} [Group G]

/-- The actual quotient projection after dividing K by its two-core. -/
noncomputable def mathieuStarProjection (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    (K ⧸ pCore 2 K) →* M22 :=
  QuotientGroup.lift (pCore 2 K) (mathieuProjection K e) (by
    rw [mathieuProjection_ker]
    exact le_centralPreimage _)

theorem mathieuStarProjection_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    Function.Surjective (mathieuStarProjection K e) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (mathieuProjection_surjective K e) _

/-- The kernel upstairs is precisely the center of K/O₂(K). -/
theorem mathieuStarProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    (mathieuStarProjection K e).ker = center (K ⧸ pCore 2 K) := by
  rw [mathieuStarProjection, QuotientGroup.ker_lift, mathieuProjection_ker,
    map_centralPreimage]

/-- The hexad inverse image inside K/O₂(K). -/
noncomputable def hexadStarPreimage (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    Subgroup (K ⧸ pCore 2 K) :=
  (MulAction.stabilizer M22 B).comap (mathieuStarProjection K e)

/-- Restriction of the original cover to the actual hexad stabilizer. -/
noncomputable def hexadStarRestriction (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    hexadStarPreimage K e B →* MulAction.stabilizer M22 B :=
  (mathieuStarProjection K e).subgroupComap (MulAction.stabilizer M22 B)

theorem hexadStarRestriction_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    Function.Surjective (hexadStarRestriction K e B) :=
  (mathieuStarProjection K e).subgroupComap_surjective_of_surjective _
    (mathieuStarProjection_surjective K e)

theorem hexadStarRestriction_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    (hexadStarRestriction K e B).ker =
      (center (K ⧸ pCore 2 K)).subgroupOf (hexadStarPreimage K e B) := by
  ext x
  change hexadStarRestriction K e B x = 1 ↔ _
  rw [Subtype.ext_iff]
  change mathieuStarProjection K e x.val = 1 ↔ _
  rw [← MonoidHom.mem_ker, mathieuStarProjection_ker]
  rfl

theorem center_le_hexadStarPreimage (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    center (K ⧸ pCore 2 K) ≤ hexadStarPreimage K e B := by
  rw [← mathieuStarProjection_ker K e]
  exact ker_le_comap _ _

/-- Reduction of the published hexad pullback modulo O₂(K). -/
noncomputable def hexadStarReduction (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    hexadPreimage K e B →* hexadStarPreimage K e B :=
  ((QuotientGroup.mk' (pCore 2 K)).comp (hexadPreimage K e B).subtype).codRestrict _
    (fun x => x.property)

theorem hexadStarReduction_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    Function.Surjective (hexadStarReduction K e B) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y.val
  have hxP : x ∈ hexadPreimage K e B := by
    change mathieuStarProjection K e (QuotientGroup.mk' (pCore 2 K) x) ∈ MulAction.stabilizer M22 B
    rw [hx]
    exact y.property
  exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩

/-- The reduction kernel is exactly the restricted ambient two-core. -/
theorem hexadStarReduction_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    (hexadStarReduction K e B).ker =
      (pCore 2 K).subgroupOf (hexadPreimage K e B) := by
  ext x
  change hexadStarReduction K e B x = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff x.val

/-- The labelled six-point quotient of the concrete hexad stabilizer. -/
noncomputable def hexadNativeSixProjection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B →* alternatingGroup (Fin 6) :=
  (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    (QuotientGroup.mk' (m22SetAction B).ker)

theorem hexadNativeSixProjection_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadNativeSixProjection hB).ker = (m22SetAction B).ker := by
  dsimp [hexadNativeSixProjection]
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

variable [Finite G]

omit [Finite G] in
/-- The actual lifted hexad has index 77, hence index coprime to three. -/
theorem hexadStarPreimage_index (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadStarPreimage K e B).index = 77 := by
  rw [hexadStarPreimage, index_comap_of_surjective _ (mathieuStarProjection_surjective K e)]
  have hc := (MulAction.stabilizer M22 B).card_mul_index
  rw [m22Hexad_stabilizer_card hB, m22_order] at hc
  omega

/-- Central transfer retains the cubic kernel in the derived subgroup. -/
theorem hexadStarRestriction_ker_le_commutator (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadStarRestriction K e B).ker ≤ commutator (hexadStarPreimage K e B) := by
  have ht := central_le_mapped_commutator_of_coprime_index
    (hexadStarPreimage K e B) (center (K ⧸ pCore 2 K)) le_rfl
    (center_le_hexadStarPreimage K e B) (by
      rw [hcenter, hexadStarPreimage_index K e hB]; decide)
  rw [hexadStarRestriction_ker]
  intro x hx
  obtain ⟨y, hy, he⟩ := ht hx
  exact (Subtype.ext he : y = x) ▸ hy

private theorem alternatingSix_twoCore : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 (alternatingGroup (Fin 6)) :=
      (h ▸ (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 6)))).of_equiv topEquiv
    let : Group.IsNilpotent (alternatingGroup (Fin 6)) := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance).elim


/-- The residual in the reduced pullback gives a cubic central cover of A₆. -/
theorem exists_hexadStarResidual_cover (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ t : (solvableResidual (hexadStarPreimage K e B) ⧸
        pCore 2 (solvableResidual (hexadStarPreimage K e B))) →* alternatingGroup (Fin 6),
      Function.Surjective t ∧ t.ker ≤ center _ ∧ Nat.card t.ker = 3 ∧
      ∀ x : solvableResidual (hexadStarPreimage K e B),
        t (QuotientGroup.mk' (pCore 2 (solvableResidual (hexadStarPreimage K e B))) x) =
          hexadNativeSixProjection hB (hexadStarRestriction K e B x) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hc : (hexadStarRestriction K e B).ker ≤ center (hexadStarPreimage K e B) := by
    rw [hexadStarRestriction_ker]
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y.val)
  have hk : Nat.card (hexadStarRestriction K e B).ker = 3 := by
    rw [hexadStarRestriction_ker,
      Nat.card_congr (subgroupOfEquivOfLe (center_le_hexadStarPreimage K e B)).toEquiv,
      hcenter]
  have hr : Function.Surjective (hexadNativeSixProjection hB) :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsMulCommutative (hexadNativeSixProjection hB).ker := by
    rw [hexadNativeSixProjection_ker]
    let := m22HexadKernel_elementaryAbelian hB
    infer_instance
  have hp : IsPGroup 2 (hexadNativeSixProjection hB).ker := by
    rw [hexadNativeSixProjection_ker]
    exact IsPGroup.of_card (n := 4) (m22HexadKernel_card hB)
  exact CubicCentralRestriction.exists_residual_cover _
    (hexadStarRestriction_surjective K e B) hc hk
    (hexadStarRestriction_ker_le_commutator K e hcenter hB) _ hr hp alternatingSix_twoCore

/-- Identify the intrinsic residual with the published subgroup of G. -/
noncomputable def hexadResidualEmbeddingEquiv (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    solvableResidual (hexadPreimage K e B) ≃* hexadResidualIn K e B :=
  ((hexadPreimage K e B).equivMapOfInjective K.subtype K.subtype_injective).solvableResidualEquiv.trans
    ((solvableResidual (hexadLift K e B)).equivMapOfInjective
      (hexadLift K e B).subtype (hexadLift K e B).subtype_injective)

theorem hexadResidualEmbeddingEquiv_apply (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22))
    (x : solvableResidual (hexadPreimage K e B)) :
    (hexadResidualEmbeddingEquiv K e B x : G) = x.val.val.val := rfl

/-- The literal six-point action restricted to the published ambient residual. -/
noncomputable def hexadResidualInSixProjection (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    hexadResidualIn K e B →* alternatingGroup (Fin 6) :=
  ((hexadSixProjection K e hB).comp (solvableResidual (hexadPreimage K e B)).subtype).comp
    (hexadResidualEmbeddingEquiv K e B).symm.toMonoidHom

theorem hexadResidualInSixProjection_apply (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (x : solvableResidual (hexadPreimage K e B)) :
    hexadResidualInSixProjection K e hB (hexadResidualEmbeddingEquiv K e B x) =
      hexadSixProjection K e hB x.val := by
  simp only [hexadResidualInSixProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Subgroup.subtype_apply]

/-- Transport the central cover through the exact two-core reduction. -/
theorem exists_hexadResidualIn_cover (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ t : (hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) →*
        alternatingGroup (Fin 6),
      Function.Surjective t ∧ t.ker ≤ center _ ∧ Nat.card t.ker = 3 ∧
      ∀ x : hexadResidualIn K e B,
        t (QuotientGroup.mk' (pCore 2 (hexadResidualIn K e B)) x) =
          hexadResidualInSixProjection K e hB x := by
  obtain ⟨s, hs, hsc, hsk, hcompat⟩ := exists_hexadStarResidual_cover K e hcenter hB
  let f := (hexadStarReduction K e B).solvableResidualMap
  have hf : Function.Surjective f :=
    (hexadStarReduction K e B).solvableResidualMap_surjective
      (hexadStarReduction_surjective K e B)
  have hfk : IsPGroup 2 f.ker :=
    (hexadStarReduction K e B).solvableResidualMap_ker_isPGroup (by
      rw [hexadStarReduction_ker]
      exact pCore_isPGroup.comap_of_injective _ (hexadPreimage K e B).subtype_injective)
  let a := hexadResidualEmbeddingEquiv K e B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := f.pCoreQuotientEquiv hf hfk
  let d := aq.symm.trans b
  let t := s.comp d.toMonoidHom
  refine ⟨t, hs.comp d.surjective, ?_, ?_, ?_⟩
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    apply d.injective
    simp only [map_mul]
    exact mem_center_iff.mp (hsc hx) (d y)
  · have hm : t.ker.map d.toMonoidHom = s.ker := by
      rw [← MonoidHom.comap_ker, map_comap_eq_self_of_surjective d.surjective]
    rw [← hsk, ← hm, card_map_of_injective d.injective]
  · intro x
    obtain ⟨y, rfl⟩ := a.surjective x
    have ha : QuotientGroup.mk' (pCore 2 (hexadResidualIn K e B)) (a y) =
        aq (QuotientGroup.mk' (pCore 2 (solvableResidual (hexadPreimage K e B))) y) := rfl
    rw [ha]
    dsimp only [t, d, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_apply, MonoidHom.pCoreQuotientEquiv_apply, hcompat]
    rw [hexadResidualInSixProjection_apply]
    rfl


/-- The six-point map after dividing the residual by its own two-core. -/
noncomputable def hexadResidualCoverProjection (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) →* alternatingGroup (Fin 6) :=
  (exists_hexadResidualIn_cover K e hcenter hB).choose

theorem hexadResidualCoverProjection_spec (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (hexadResidualCoverProjection K e hcenter hB) ∧
      (hexadResidualCoverProjection K e hcenter hB).ker ≤ center _ ∧
      Nat.card (hexadResidualCoverProjection K e hcenter hB).ker = 3 ∧
      ∀ x : hexadResidualIn K e B,
        hexadResidualCoverProjection K e hcenter hB
          (QuotientGroup.mk' (pCore 2 (hexadResidualIn K e B)) x) =
            hexadResidualInSixProjection K e hB x :=
  (exists_hexadResidualIn_cover K e hcenter hB).choose_spec

/-- The remaining six-point kernel is precisely the cubic center. -/
theorem hexadResidualCoverProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadResidualCoverProjection K e hcenter hB).ker =
      center (hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) := by
  obtain ⟨hs, hc, _, _⟩ := hexadResidualCoverProjection_spec K e hcenter hB
  apply le_antisymm hc
  intro x hx
  have hz : hexadResidualCoverProjection K e hcenter hB x ∈
      center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := hs y
    simpa only [map_mul] using congrArg (hexadResidualCoverProjection K e hcenter hB)
      (mem_center_iff.mp hx y)
  rw [alternatingGroup.center_eq_bot (by simp)] at hz
  exact mem_bot.mp hz

/-- The actual central quotient isomorphism with the alternating six-point image. -/
noncomputable def hexadResidualCentralQuotientEquiv (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ((hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) ⧸ center _) ≃*
      alternatingGroup (Fin 6) :=
  QuotientGroup.liftEquiv _ (hexadResidualCoverProjection_spec K e hcenter hB).1
    (hexadResidualCoverProjection_ker K e hcenter hB).symm

theorem hexadResidualIn_isPerfect (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    Group.IsPerfect (hexadResidualIn K e B) :=
  Group.IsPerfect.ofSurjective (f := (hexadResidualEmbeddingEquiv K e B).toMonoidHom)
    (hexadResidualEmbeddingEquiv K e B).surjective

/-- The canonical hexad component restricts the cubic M₂₂ cover to a triple cover of A₆. -/
theorem hexadResidualIn_isTripleCoverSix (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    SolvableExclusion.IsTripleCoverSix
      (hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) := by
  let := hexadResidualIn_isPerfect K e B
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hq : IsQuasisimple (hexadResidualIn K e B ⧸ pCore 2 (hexadResidualIn K e B)) :=
    { toIsPerfect := inferInstance
      simple := (hexadResidualCentralQuotientEquiv K e hcenter hB).isSimpleGroup }
  refine ⟨hq, ?_, ⟨hexadResidualCentralQuotientEquiv K e hcenter hB⟩⟩
  rw [← hexadResidualCoverProjection_ker K e hcenter hB]
  exact (hexadResidualCoverProjection_spec K e hcenter hB).2.2.1

/-- The full six-point kernel is the central preimage of the residual two-core. -/
theorem hexadResidualInSixProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadResidualInSixProjection K e hB).ker =
      centralPreimage (pCore 2 (hexadResidualIn K e B)) := by
  have he : (hexadResidualCoverProjection K e hcenter hB).comp
      (QuotientGroup.mk' (pCore 2 (hexadResidualIn K e B))) =
      hexadResidualInSixProjection K e hB :=
    MonoidHom.ext (hexadResidualCoverProjection_spec K e hcenter hB).2.2.2
  rw [← he, ← MonoidHom.comap_ker, hexadResidualCoverProjection_ker]
  rfl

/-- The two-core of the actual six-point kernel is exactly the residual two-core. -/
theorem hexadResidualInSixProjection_twoCore (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadResidualInSixProjection K e hB).ker.pCoreIn 2 =
      pCore 2 (hexadResidualIn K e B) := by
  apply le_antisymm
  · exact le_sSup ⟨by
      change ((pCore 2 (hexadResidualInSixProjection K e hB).ker).map
        (hexadResidualInSixProjection K e hB).ker.subtype).Normal
      infer_instance, isPGroup_pCoreIn _ _⟩
  · apply le_pCoreIn_of_normalizes pCore_isPGroup
    · rw [hexadResidualInSixProjection_ker K e hcenter hB]
      exact le_centralPreimage _
    · exact le_normalizer_of_normal

/-- The resulting central quotient retains the original labelled hexad action. -/
theorem hexadResidualCentralQuotientEquiv_compatible (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (x : solvableResidual (hexadPreimage K e B)) :
    hexadResidualCentralQuotientEquiv K e hcenter hB
      (QuotientGroup.mk' _ (QuotientGroup.mk' (pCore 2 (hexadResidualIn K e B))
        (hexadResidualEmbeddingEquiv K e B x))) = hexadSixProjection K e hB x.val := by
  change hexadResidualCoverProjection K e hcenter hB _ = _
  rw [(hexadResidualCoverProjection_spec K e hcenter hB).2.2.2,
    hexadResidualInSixProjection_apply]


/-- The original cubic center lies in the residual and survives its two-core quotient. -/
theorem hexadStarCenter_survives (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (center (K ⧸ pCore 2 K)).subgroupOf (hexadStarPreimage K e B) ≤
      solvableResidual (hexadStarPreimage K e B) ∧
    Disjoint ((center (K ⧸ pCore 2 K)).subgroupOf (hexadStarPreimage K e B))
      ((pCore 2 (solvableResidual (hexadStarPreimage K e B))).map
        (solvableResidual (hexadStarPreimage K e B)).subtype) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hc : (hexadStarRestriction K e B).ker ≤ center (hexadStarPreimage K e B) := by
    rw [hexadStarRestriction_ker]
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y.val)
  have hk : Nat.card (hexadStarRestriction K e B).ker = 3 := by
    rw [hexadStarRestriction_ker,
      Nat.card_congr (subgroupOfEquivOfLe (center_le_hexadStarPreimage K e B)).toEquiv,
      hcenter]
  have hr : Function.Surjective (hexadNativeSixProjection hB) :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsMulCommutative (hexadNativeSixProjection hB).ker := by
    rw [hexadNativeSixProjection_ker]
    let := m22HexadKernel_elementaryAbelian hB
    infer_instance
  have hp : IsPGroup 2 (hexadNativeSixProjection hB).ker := by
    rw [hexadNativeSixProjection_ker]
    exact IsPGroup.of_card (n := 4) (m22HexadKernel_card hB)
  constructor
  · rw [← hexadStarRestriction_ker]
    exact CubicCentralRestriction.kernel_le_solvableResidual _
      (hexadStarRestriction_surjective K e B) hc hk
      (hexadStarRestriction_ker_le_commutator K e hcenter hB) _ hr hp
  · rw [← hexadStarRestriction_ker]
    exact IsPGroup.disjoint_of_ne 3 2 (by decide) _ _
      (IsPGroup.of_card (n := 1) (by simpa using hk)) (pCore_isPGroup.map _)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
