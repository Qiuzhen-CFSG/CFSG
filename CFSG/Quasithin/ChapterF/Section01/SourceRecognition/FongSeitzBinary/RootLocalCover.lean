module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalCover

/-!
# The smaller root-generated cover on the original endpoints

Pull back the actual subgroup Rᵢ = ⟨Uᵢ,Uᵢ^{sᵢ}⟩ through each original
endpoint marking. Its generators are the lifted canonical root and its
conjugate by the previously chosen original simple lift. The full panel
kernel pulls back through that same map. The kernel inside Rᵢ lies in
the actual Cartan and meets the original S trivially.

When the earlier local-section containment U_{sᵢ} ≤ Kᵢ is supplied, the
root-generated subgroup is isomorphic to the already constructed local
cover, and its action onto the same local permutation group has central
odd kernel in its derived subgroup. Both the source quotient and the
independently marked apartment quotient can instantiate these formulas.

Source: Fong--Seitz I (5C)(a) and the reduction in (5C)(b), pp.25--26.
The earlier containment from (2B), the rank-one model catalogue and its
central-cover identifications, and the seven-row recognition still require
their source proofs. No small nonperfect group is replaced by its derived
subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

private theorem endpointMap_injective' (i : Fin 2) :
    Function.Injective (endpointMap Q e i) :=
  (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (endpoint Q e i).injective

private theorem endpointMap_range' (i : Fin 2) :
    (endpointMap Q e i).range = Q.tits.standardParabolic {Q.simple i} := by
  rw [endpointMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

@[expose] def originalSimpleRoot (split : SplitData Q.tits) (i : Fin 2) :
    Subgroup (parabolic L S i) := (simpleRoot Q split i).comap (endpointMap Q e i)

@[expose] def originalRankOne (split : SplitData Q.tits) (i : Fin 2) :
    Subgroup (parabolic L S i) := (rankOne Q split i).comap (endpointMap Q e i)

/-- The two generators use the same original lifted simple reflection. -/
theorem originalRankOne_eq (split : SplitData Q.tits) (i : Fin 2) :
    originalRankOne Q e split i = originalSimpleRoot Q e split i ⊔
      (originalSimpleRoot Q e split i).comap
        (MulAut.conj (originalSimpleLift Q e i)).toMonoidHom := by
  have hU : simpleRoot Q split i ≤ Q.tits.standardParabolic {Q.simple i} :=
    (simpleRoot_le Q split i).trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hV : rootAt Q split i (Q.simple i) ≤ Q.tits.standardParabolic {Q.simple i} :=
    (show rootAt Q split i (Q.simple i) ≤ rankOne Q split i from le_sup_right).trans
      (rankOne_le_parabolic Q split i)
  change ((simpleRoot Q split i ⊔ rootAt Q split i (Q.simple i)).subgroupOf
    (Q.tits.standardParabolic {Q.simple i})).comap (endpoint Q e i).toMonoidHom = _
  rw [subgroupOf_sup hU hV, ← comap_sup_eq _ _ _ (endpoint Q e i).surjective]
  change originalSimpleRoot Q e split i ⊔
    (rootAt Q split i (Q.simple i)).comap (endpointMap Q e i) = _
  congr 1
  ext x
  change (representative (Q.simple i) : X ⧸ Q.D) * endpointMap Q e i x *
    (representative (Q.simple i) : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i ↔ _
  rw [← originalSimpleLift_map Q e i, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem originalRankOne_map (split : SplitData Q.tits) (i : Fin 2) :
    (originalRankOne Q e split i).map (endpointMap Q e i) = rankOne Q split i := by
  rw [originalRankOne, map_comap_eq, endpointMap_range']
  exact inf_eq_right.mpr (rankOne_le_parabolic Q split i)

theorem originalRankOne_le_localClosure (split : SplitData Q.tits) (i : Fin 2) :
    originalRankOne Q e split i ≤ originalLocalClosure Q e split i :=
  comap_mono (rankOne_le_localClosure Q split i)

def originalRankOneEquiv (split : SplitData Q.tits) (i : Fin 2) :
    originalRankOne Q e split i ≃* rankOne Q split i :=
  ((originalRankOne Q e split i).equivMapOfInjective (endpointMap Q e i)
    (endpointMap_injective' Q e i)).trans
      (MulEquiv.subgroupCongr (originalRankOne_map Q e split i))

@[simp] theorem originalRankOneEquiv_apply (split : SplitData Q.tits) (i : Fin 2)
    (r : originalRankOne Q e split i) :
    (originalRankOneEquiv Q e split i r : X ⧸ Q.D) = endpointMap Q e i r := by rfl

include e in
theorem originalRankOne_inf_kernel_le_cartan (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    originalRankOne Q e split i ⊓ originalPanelKernel (L := L) (S := S) i ≤
      (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) := by
  rw [← originalPanelKernel_comap Q e h i]
  exact comap_mono (RootLocalCover.rankOne_inf_kernel_le_torus Q split i)

include e in
/-- The pulled-back Cartan normalizes the exact original root kernel. -/
theorem originalCartan_normalizes_rootKernel (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) ≤
      normalizer (originalRankOne Q e split i ⊓
        originalPanelKernel (L := L) (S := S) i : Set (parabolic L S i)) := by
  rw [← originalPanelKernel_comap Q e h i]
  change (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) ≤
    normalizer ((rankOne Q split i ⊓ localKernel Q i).comap (endpointMap Q e i) :
      Set (parabolic L S i))
  exact (comap_mono (RootLocalCover.torus_normalizes_rankOne_kernel Q split i)).trans
    ((rankOne Q split i ⊓ localKernel Q i).le_normalizer_comap (endpointMap Q e i))

include e in
/-- The equality in source (5C)(a), on the original endpoint carrier. -/
theorem originalSylow_inf_rootKernel (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    S.subgroupOf (parabolic L S i) ⊓ (originalRankOne Q e split i ⊓
        originalPanelKernel (L := L) (S := S) i) =
      S.subgroupOf (parabolic L S i) ⊓
        (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) ⊓
        originalPanelKernel (L := L) (S := S) i := by
  rw [← endpoint_unipotent_comap Q e h split i, ← originalPanelKernel_comap Q e h i]
  exact congrArg (Subgroup.comap (endpointMap Q e i))
    (RootLocalCover.unipotent_inf_rankOne_kernel Q split i)

include e in
theorem originalRankOne_disjoint_radical (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    Disjoint (originalRankOne Q e split i)
      (S.subgroupOf (parabolic L S i) ⊓ originalPanelKernel (L := L) (S := S) i) := by
  rw [← original_radical_comap Q e h split i]
  apply disjoint_def.mpr
  intro r hr hv
  apply endpointMap_injective' Q e i
  rw [map_one]
  exact (disjoint_def.mp (RootLocalCover.rankOne_disjoint_radical Q split i)) hr hv

/-- The smaller original group maps to the original whole-root cover itself. -/
def originalRootCoverEquiv (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalRankOne Q e split i ≃*
      originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i := by
  let := originalRadicalInClosure_normal Q e h split i
  exact ((originalRankOneEquiv Q e split i).trans (RootLocalCover.coverEquiv Q split i hV)).trans
    (originalCoverEquiv Q e h split i).symm

/-- This equivalence is literally inclusion followed by the original quotient. -/
@[simp] theorem originalRootCoverEquiv_apply (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalRootCoverEquiv Q e h split i hV r = QuotientGroup.mk'
      (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r) := by
  let := originalRadicalInClosure_normal Q e h split i
  apply (originalCoverEquiv Q e h split i).injective
  change originalCoverEquiv Q e h split i ((originalCoverEquiv Q e h split i).symm
    (RootLocalCover.coverEquiv Q split i hV (originalRankOneEquiv Q e split i r))) = _
  rw [MulEquiv.apply_symm_apply, RootLocalCover.coverEquiv_apply, originalCoverEquiv_mk]
  apply congrArg (QuotientGroup.mk' (LocalCover.radicalInClosure Q split i))
  apply Subtype.ext
  rw [originalLocalClosureEquiv_apply]
  exact originalRankOneEquiv_apply Q e split i r

def originalRootProjection (split : SplitData Q.tits) (i : Fin 2) :
    originalRankOne Q e split i →* localGroup Q split i :=
  (RootLocalCover.projection Q split i).comp (originalRankOneEquiv Q e split i).toMonoidHom

@[simp] theorem originalRootProjection_apply (split : SplitData Q.tits) (i : Fin 2)
    (r : originalRankOne Q e split i) :
    (originalRootProjection Q e split i r : Equiv.Perm (Panel Q i)) =
      localAction Q split i (inclusion (rankOne_le_localClosure Q split i)
        (originalRankOneEquiv Q e split i r)) := by
  change (RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) :
    Equiv.Perm (Panel Q i)) = _
  exact RootLocalCover.projection_apply Q split i _

theorem originalRootProjection_ker (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    (originalRootProjection Q e split i).ker =
      (originalPanelKernel (L := L) (S := S) i).subgroupOf (originalRankOne Q e split i) := by
  change (RootLocalCover.projection Q split i).ker.comap
    (originalRankOneEquiv Q e split i).toMonoidHom = _
  rw [RootLocalCover.projection_ker]
  ext r
  change (originalRankOneEquiv Q e split i r : X ⧸ Q.D) ∈ localKernel Q i ↔ _
  rw [originalRankOneEquiv_apply]
  change r.val ∈ (localKernel Q i).comap (endpointMap Q e i) ↔ _
  rw [originalPanelKernel_comap Q e h i]
  rfl

/-- The original root-cover square commutes with the previously constructed action. -/
theorem originalRootCoverEquiv_projection (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalProjection Q e h split i (originalRootCoverEquiv Q e h split i hV r) =
      originalRootProjection Q e split i r := by
  let := originalRadicalInClosure_normal Q e h split i
  apply Subtype.ext
  rw [originalRootCoverEquiv_apply, originalProjection_mk, originalRootProjection_apply]
  apply congrArg (localAction Q split i)
  apply Subtype.ext
  rw [originalLocalClosureEquiv_apply]
  exact (originalRankOneEquiv_apply Q e split i r).symm

/-- Fong--Seitz's smaller cover, with the original full local kernel. -/
theorem original_root_central_odd_cover (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Surjective (originalRootProjection Q e split i) ∧
      (originalRootProjection Q e split i).ker ≤ center (originalRankOne Q e split i) ∧
      Nat.Coprime 2 (Nat.card (originalRootProjection Q e split i).ker) ∧
      (originalRootProjection Q e split i).ker ≤ _root_.commutator (originalRankOne Q e split i) := by
  let a := originalRankOneEquiv Q e split i
  have hk : (originalRootProjection Q e split i).ker =
      (RootLocalCover.projection Q split i).ker.comap a.toMonoidHom := rfl
  obtain ⟨hs,hc,ho,hd⟩ := RootLocalCover.central_odd_cover Q split i hV
  refine ⟨hs.comp a.surjective, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := hc (hk ▸ hx)
    apply mem_center_iff.mpr
    intro y
    apply a.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hx' (a y)
  · rw [hk, comap_equiv_eq_map_symm', card_map_of_injective a.symm.injective]
    exact ho
  · intro x hx
    have hx' := hd (hk ▸ hx)
    have hm : a.symm (a x) ∈
        (_root_.commutator (rankOne Q split i)).map a.symm.toMonoidHom := mem_map_of_mem _ hx'
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.symm.surjective] at hm
    simpa only [MulEquiv.symm_apply_apply, _root_.commutator_def] using hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The smaller root-generated group's representatives use the SAME q:X→X/D. -/
theorem quotient_originalRankOneEquiv_apply (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (r : MarkedLocal.originalRankOne Q (originalMarkedIso Q) split i) :
    (MarkedLocal.originalRankOneEquiv Q (originalMarkedIso Q) split i r :
      (generated L S) ⧸ Q.D) = Q.q ⟨r.val,parabolic_le_generated i r.val.property⟩ := by
  rw [MarkedLocal.originalRankOneEquiv_apply, original_endpointMap_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
