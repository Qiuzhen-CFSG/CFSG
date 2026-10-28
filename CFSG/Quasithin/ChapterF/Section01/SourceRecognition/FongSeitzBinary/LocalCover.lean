module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CartanTransport
public import Theory.GroupTheory.NormalCoreTwoClosedTransport

/-!
# The local cover on the original marked endpoints

Transport the full kernel of Pᵢ acting on Pᵢ/B through the given amalgam
isomorphism. The inverse image of U is the original S, so U ∩ Kᵢ pulls
back to the original S intersected with that full panel kernel. The
inverse image of ⟨U,U^{sᵢ}⟩ is exactly ⟨S,S^{sᵢ}⟩, where sᵢ is lifted
through its own original endpoint. Restriction of the same marking and
quotienting by these corresponding intersections gives an actual group
isomorphism of the two local-cover numerators modulo their radicals.

The Fong--Seitz I (5B) projection therefore gives a surjective central
odd stem cover on the original endpoint, with an exact kernel formula
and representative equation. Both endpoints and the entire original
Borel are retained. The final specializations use the original q:X→X/D
on every representative. The independent quotient carrier also permits
the universal geometric marking; no descent to the original completion
is asserted. Perfectness of either original local factor is unnecessary.

Source: Fong--Seitz I, printed p.25, (5B); DGS (3.6)--(3.7), pp.77--80,
and Theorem D, p.224. Recognition of the local permutation groups and
the smaller Rᵢ covers, and the seven marked Lie comparisons, remain.
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

@[expose] def originalPanelKernel (i : Fin 2) : Subgroup (parabolic L S i) :=
  ((commonBorel L S).subgroupOf (parabolic L S i)).normalCore

private theorem endpointMap_injective' (i : Fin 2) :
    Function.Injective (endpointMap Q e i) :=
  (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (endpoint Q e i).injective

private theorem endpointMap_range' (i : Fin 2) :
    (endpointMap Q e i).range = Q.tits.standardParabolic {Q.simple i} := by
  rw [endpointMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

include e in
theorem originalPanelKernel_comap (h : HypothesisF11 L S) (i : Fin 2) :
    (localKernel Q i).comap (endpointMap Q e i) = originalPanelKernel (L := L) (S := S) i := by
  change ((localKernel Q i).subgroupOf (Q.tits.standardParabolic {Q.simple i})).comap
    (endpoint Q e i).toMonoidHom = _
  rw [localKernel_subgroupOf, ← normalCore_comap_of_surjective _ (endpoint Q e i).surjective]
  change (Q.tits.B.comap (endpointMap Q e i)).normalCore = _
  rw [endpoint_borel_comap Q e h i]
  rfl

include e in
theorem endpoint_unipotent_comap (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    split.U.comap (endpointMap Q e i) = S.subgroupOf (parabolic L S i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩ := (sylow_range Q e h split).symm ▸ hx
    rw [← endpoint_sylow Q e h i s] at hs
    have he := congrArg Subtype.val (endpointMap_injective' Q e i hs)
    change (x : G) ∈ S
    exact he ▸ s.property
  · intro hx
    rw [← sylow_range Q e h split]
    exact ⟨⟨x,hx⟩,(endpoint_sylow Q e h i ⟨x,hx⟩).symm⟩

include e in
theorem original_radical_comap (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    (LocalCover.radical Q split i).comap (endpointMap Q e i) =
      S.subgroupOf (parabolic L S i) ⊓ originalPanelKernel (L := L) (S := S) i := by
  rw [LocalCover.radical, comap_inf, endpoint_unipotent_comap Q e h split i,
    originalPanelKernel_comap Q e h i]

private theorem simpleLift_mem_parabolic (i : Fin 2) :
    (representative (Q.simple i) : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
  Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _))

def originalSimpleLift (i : Fin 2) : parabolic L S i :=
  (endpoint Q e i).symm ⟨representative (Q.simple i),simpleLift_mem_parabolic Q i⟩

@[simp] theorem originalSimpleLift_map (i : Fin 2) :
    endpointMap Q e i (originalSimpleLift Q e i) =
      (representative (Q.simple i) : X ⧸ Q.D) := by
  exact congrArg Subtype.val ((endpoint Q e i).apply_symm_apply _)

@[expose] def originalLocalClosure (split : SplitData Q.tits) (i : Fin 2) :
    Subgroup (parabolic L S i) := (localClosure Q split i).comap (endpointMap Q e i)

include e in
/-- The numerator is generated by the original S and its conjugate by the same lifted reflection. -/
theorem originalLocalClosure_eq (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    originalLocalClosure Q e split i = S.subgroupOf (parabolic L S i) ⊔
      (S.subgroupOf (parabolic L S i)).comap
        (MulAut.conj (originalSimpleLift Q e i)).toMonoidHom := by
  have hU : split.U ≤ Q.tits.standardParabolic {Q.simple i} :=
    split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hV : unipotentConjugate split (Q.simple i) ≤ Q.tits.standardParabolic {Q.simple i} :=
    (show unipotentConjugate split (Q.simple i) ≤ localClosure Q split i from le_sup_right).trans
      (localClosure_le_parabolic Q split i)
  change ((split.U ⊔ unipotentConjugate split (Q.simple i)).subgroupOf
    (Q.tits.standardParabolic {Q.simple i})).comap (endpoint Q e i).toMonoidHom = _
  rw [subgroupOf_sup hU hV, ← comap_sup_eq _ _ _ (endpoint Q e i).surjective]
  change split.U.comap (endpointMap Q e i) ⊔
    (unipotentConjugate split (Q.simple i)).comap (endpointMap Q e i) = _
  rw [endpoint_unipotent_comap Q e h split i]
  congr 1
  ext x
  change (representative (Q.simple i) : X ⧸ Q.D) * endpointMap Q e i x *
    (representative (Q.simple i) : X ⧸ Q.D)⁻¹ ∈ split.U ↔ _
  rw [← originalSimpleLift_map Q e i, ← map_inv, ← map_mul, ← map_mul]
  change (originalSimpleLift Q e i * x * (originalSimpleLift Q e i)⁻¹) ∈
    split.U.comap (endpointMap Q e i) ↔ _
  rw [endpoint_unipotent_comap Q e h split i]
  rfl

theorem originalLocalClosure_map (split : SplitData Q.tits) (i : Fin 2) :
    (originalLocalClosure Q e split i).map (endpointMap Q e i) = localClosure Q split i := by
  rw [originalLocalClosure, map_comap_eq, endpointMap_range']
  exact inf_eq_right.mpr (localClosure_le_parabolic Q split i)

def originalLocalClosureEquiv (split : SplitData Q.tits) (i : Fin 2) :
    originalLocalClosure Q e split i ≃* localClosure Q split i :=
  ((originalLocalClosure Q e split i).equivMapOfInjective (endpointMap Q e i)
    (endpointMap_injective' Q e i)).trans (MulEquiv.subgroupCongr (originalLocalClosure_map Q e split i))

@[simp] theorem originalLocalClosureEquiv_apply (split : SplitData Q.tits) (i : Fin 2)
    (x : originalLocalClosure Q e split i) :
    (originalLocalClosureEquiv Q e split i x : X ⧸ Q.D) = endpointMap Q e i x := by rfl

@[expose] def originalRadicalInClosure (split : SplitData Q.tits) (i : Fin 2) :
    Subgroup (originalLocalClosure Q e split i) :=
  (S.subgroupOf (parabolic L S i) ⊓ originalPanelKernel (L := L) (S := S) i).subgroupOf
    (originalLocalClosure Q e split i)

include e in
theorem originalRadicalInClosure_eq_comap (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) : originalRadicalInClosure Q e split i =
      (LocalCover.radicalInClosure Q split i).comap
        (originalLocalClosureEquiv Q e split i).toMonoidHom := by
  ext x
  change (x : parabolic L S i) ∈ S.subgroupOf (parabolic L S i) ⊓
    originalPanelKernel (L := L) (S := S) i ↔
      (originalLocalClosureEquiv Q e split i x : X ⧸ Q.D) ∈ LocalCover.radical Q split i
  rw [originalLocalClosureEquiv_apply, ← original_radical_comap Q e h split i]
  rfl

theorem originalRadicalInClosure_normal (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) : (originalRadicalInClosure Q e split i).Normal := by
  rw [originalRadicalInClosure_eq_comap Q e h split i]
  infer_instance

def originalCoverEquiv (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i ≃*
      LocalCover.CoverGroup Q split i := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact QuotientGroup.equivOfSurjectiveComap (originalLocalClosureEquiv Q e split i).toMonoidHom
    (originalLocalClosureEquiv Q e split i).surjective _ _
    (originalRadicalInClosure_eq_comap Q e h split i).symm

@[simp] theorem originalCoverEquiv_mk (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (x : originalLocalClosure Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalCoverEquiv Q e h split i (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (originalLocalClosureEquiv Q e split i x) := by
  rfl

def originalProjection (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i →*
      (localAction Q split i).range := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact (LocalCover.projection Q split i).comp (originalCoverEquiv Q e h split i).toMonoidHom

@[simp] theorem originalProjection_mk (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (x : originalLocalClosure Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalProjection Q e h split i (QuotientGroup.mk' _ x) : Equiv.Perm (Panel Q i)) =
      localAction Q split i (originalLocalClosureEquiv Q e split i x) := by
  simp only [originalProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    originalCoverEquiv_mk, LocalCover.projection_mk]

theorem originalProjection_ker (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalProjection Q e h split i).ker =
      ((originalPanelKernel (L := L) (S := S) i).subgroupOf
        (originalLocalClosure Q e split i)).map (QuotientGroup.mk' (originalRadicalInClosure Q e split i)) := by
  let := originalRadicalInClosure_normal Q e h split i
  let q := QuotientGroup.mk' (originalRadicalInClosure Q e split i)
  have hcomp : (originalProjection Q e h split i).comp q =
      (localAction Q split i).rangeRestrict.comp (originalLocalClosureEquiv Q e split i).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact originalProjection_mk Q e h split i x
  have hkernel : ((localAction Q split i).ker).comap
      (originalLocalClosureEquiv Q e split i).toMonoidHom =
      (originalPanelKernel (L := L) (S := S) i).subgroupOf (originalLocalClosure Q e split i) := by
    rw [localAction_ker]
    ext x
    change (originalLocalClosureEquiv Q e split i x : X ⧸ Q.D) ∈ localKernel Q i ↔ _
    rw [originalLocalClosureEquiv_apply]
    change x.val ∈ (localKernel Q i).comap (endpointMap Q e i) ↔ _
    rw [originalPanelKernel_comap Q e h i]
    rfl
  apply comap_injective (QuotientGroup.mk'_surjective (originalRadicalInClosure Q e split i))
  rw [MonoidHom.comap_ker, hcomp, ← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict, hkernel,
    comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr (show originalRadicalInClosure Q e split i ≤
      (originalPanelKernel (L := L) (S := S) i).subgroupOf (originalLocalClosure Q e split i) from
        fun _ hx => hx.2)]

/-- The central odd stem cover is transported to the original endpoint numerator,
with its actual local panel kernel and the same lifted simple reflection. -/
theorem original_central_odd_cover (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    let := originalRadicalInClosure_normal Q e h split i
    let E := originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i
    Function.Surjective (originalProjection Q e h split i) ∧
      (originalProjection Q e h split i).ker ≤ center E ∧
      Nat.Coprime 2 (Nat.card (originalProjection Q e h split i).ker) ∧
      (originalProjection Q e h split i).ker ≤ _root_.commutator E := by
  let := originalRadicalInClosure_normal Q e h split i
  let a := originalCoverEquiv Q e h split i
  have hk : (originalProjection Q e h split i).ker =
      (LocalCover.projection Q split i).ker.comap a.toMonoidHom := by
    rfl
  refine ⟨(LocalCover.projection_surjective Q split i).comp a.surjective, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := LocalCover.projection_ker_central Q split i (hk ▸ hx)
    apply mem_center_iff.mpr
    intro y
    apply a.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hx' (a y)
  · rw [hk, comap_equiv_eq_map_symm', card_map_of_injective a.symm.injective]
    exact LocalCover.projection_ker_odd Q split i
  · intro x hx
    have hx' := LocalCover.projection_ker_le_commutator Q split i (hk ▸ hx)
    have hm : (a.symm (a x)) ∈
        (_root_.commutator (LocalCover.CoverGroup Q split i)).map a.symm.toMonoidHom :=
      mem_map_of_mem _ hx'
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.symm.surjective] at hm
    simpa only [MulEquiv.symm_apply_apply, _root_.commutator_def] using hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal


namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both endpoint maps in the local-cover construction use the same original quotient. -/
theorem original_endpointMap_apply (Q : SourceQuotient L S) (i : Fin 2)
    (x : parabolic L S i) :
    MarkedLocal.endpointMap Q (originalMarkedIso Q) i x =
      Q.q ⟨x,parabolic_le_generated i x.property⟩ := by
  fin_cases i
  · exact originalMarkedIso_left_apply Q x
  · exact originalMarkedIso_right_apply Q x

/-- The chosen simple reflection is lifted through its marked original endpoint. -/
theorem quotient_originalSimpleLift (Q : SourceQuotient L S) (i : Fin 2) :
    Q.q ⟨MarkedLocal.originalSimpleLift Q (originalMarkedIso Q) i,
      parabolic_le_generated i (MarkedLocal.originalSimpleLift Q (originalMarkedIso Q) i).property⟩ =
      (representative (Q.simple i) : (generated L S) ⧸ Q.D) := by
  rw [← original_endpointMap_apply]
  exact MarkedLocal.originalSimpleLift_map Q (originalMarkedIso Q) i

/-- Every representative of the local-cover numerator retains that literal quotient map. -/
theorem quotient_originalLocalClosureEquiv_apply (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (x : MarkedLocal.originalLocalClosure Q (originalMarkedIso Q) split i) :
    (MarkedLocal.originalLocalClosureEquiv Q (originalMarkedIso Q) split i x :
      (generated L S) ⧸ Q.D) =
      Q.q ⟨x.val,parabolic_le_generated i x.val.property⟩ := by
  rw [MarkedLocal.originalLocalClosureEquiv_apply, original_endpointMap_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
