module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure.OriginalFlag
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.ModelImage

/-!
# The marked normalizer projection on the original group

The chosen component is normalized by T, and the original flag makes T
normalize V. Its full natural action makes the Sylow action inner; the
outer two-group argument extends innerness to N_G(L). Aligning the actual
point and plane then constructs the original residual projection and
excludes Y ≤ N_G(L). This needs no universal structural theorem.
The quotient is L/O₂(L), and both parabolic images are residuals.
Source: Aschbacher–Smith 14.7.70, printed p.1074.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
open Chapter12.Section08 Matrix.PSL3Two
open NormalizerStructure
universe u
variable {G : Type u} [Group G] {L V : Subgroup G}
variable [Finite G] {T : Sylow 2 G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d

/-- T implements its quotient action inside L, using the full natural action on V. -/
theorem sylow_action_inner
    (t : T) : ∃ l : L,
      quotientAction L ⟨t, d.natural.chosen.sylow_normalizes_component t.property⟩ =
        MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  let a := V.normalizerMonoidHom
    ⟨t, (show (T : Subgroup G) ≤ normalizer (V : Set G) from by
        simpa only [F.last] using F.invariant 3) t.property⟩
  obtain ⟨l, hl, he⟩ := d.natural.full_L_action a
  let l' : L := ⟨l, hl⟩
  let t' : normalizer (L : Set G) :=
    ⟨t, d.natural.chosen.sylow_normalizes_component t.property⟩
  let lM := inclusion L.le_normalizer l'
  have hc : ((lM⁻¹ * t' : normalizer (L : Set G)) : G) ∈ centralizer (V : Set G) := by
    intro v hv
    have h := he ⟨v, hv⟩
    change l * v * l⁻¹ = (t : G) * v * (t : G)⁻¹ at h
    change v * (l⁻¹ * (t : G)) = (l⁻¹ * (t : G)) * v
    calc
      _ = l⁻¹ * (l * v * l⁻¹) * (t : G) := by group
      _ = l⁻¹ * ((t : G) * v * (t : G)⁻¹) * (t : G) := by rw [h]
      _ = _ := by group
  have hk := seed_centralizer_fixes_quotient d.natural.chosen.normalizes
    d.natural.centralizer_L (lM⁻¹ * t') hc
  rw [map_mul, map_inv, inv_mul_eq_one] at hk
  exact ⟨l', hk.symm.trans (quotientAction_inner L l')⟩

omit [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W] d in
/-- A two-group homomorphic image is detected by any Sylow two-subgroup. -/
private theorem hom_eq_one_of_sylow {X A : Type*} [Group X] [Finite X] [Group A]
    (S : Sylow 2 X) (f : X →* A) (hp : IsPGroup 2 A)
    (hS : ∀ s ∈ S, f s = 1) : ∀ x, f x = 1 := by
  let P := S.mapSurjective f.rangeRestrict_surjective
  have he : (P : Subgroup f.range) = ⊤ :=
    (P.is_maximal' ((hp.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  intro x
  have hx : f.rangeRestrict x ∈ (P : Subgroup f.range) := he ▸ mem_top _
  obtain ⟨s, hs, hse⟩ := hx
  exact (congrArg Subtype.val hse).symm.trans (hS s hs)

/-- The genuine outer-two-group argument extends innerness from T to N_G(L). -/
theorem markedAction_range_inner
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (markedAction L e).range ≤ MulAut.innerSubgroup SL := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup SL)).comp (markedAction L e)
  have hf : ∀ x, f x = 1 := by
    apply hom_eq_one_of_sylow (T.subtype (d.natural.chosen.sylow_normalizes_component)) f
      Automorphisms.outer_sl_isTwoGroup
    intro t ht
    obtain ⟨l, hl⟩ := sylow_action_inner d ⟨t, ht⟩
    have he : markedAction L e t = markedAction L e (inclusion L.le_normalizer l) := by
      apply congrArg (MulAut.congr e)
      exact hl.trans (quotientAction_inner L l).symm
    change QuotientGroup.mk' (MulAut.innerSubgroup SL) (markedAction L e t) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [he, markedAction_inner]
    exact ⟨_, rfl⟩
  rintro a ⟨x, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp (hf x)

/-- The projection obtained from the proved inner action of the full normalizer. -/
noncomputable def project
    (e : (L ⧸ pCore 2 L) ≃* SL) : normalizer (L : Set G) →* SL :=
  innerEquiv.symm.toMonoidHom.comp ((markedAction L e).codRestrict
    (MulAut.innerSubgroup SL) (fun x => markedAction_range_inner d e ⟨x, rfl⟩))

theorem conj_project
    (e : (L ⧸ pCore 2 L) ≃* SL) (x : normalizer (L : Set G)) :
    MulAut.conj (project d e x) = markedAction L e x := by
  exact congrArg Subtype.val (innerEquiv.apply_symm_apply
    (⟨markedAction L e x, markedAction_range_inner d e ⟨x, rfl⟩⟩))

theorem project_on_L
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (project d e).comp (inclusion L.le_normalizer) =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) := by
  apply MonoidHom.ext
  intro l
  apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  exact (conj_project d e _).trans (markedAction_inner L e l)

@[simp] theorem project_apply_L
    (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    project d e (inclusion L.le_normalizer l) =
      e (QuotientGroup.mk' (pCore 2 L) l) :=
  DFunLike.congr_fun (project_on_L d e) l

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
open Chapter12.Section08 Matrix.PSL3Two
open NormalizerStructure
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem map_subgroupOf_inclusion (A H J : Subgroup G)
    (hAH : A ≤ H) (hHJ : H ≤ J) :
    (A.subgroupOf H).map (inclusion hHJ) = A.subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [map_map, show J.subtype.comp (inclusion hHJ) = H.subtype from rfl,
    map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le (hAH.trans hHJ)]

private theorem residual_subgroupOf (i : ℕ) :
    (F.Li L i).subgroupOf (normalizer (L : Set G)) =
      (pResidual 2 ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G)))).map
        ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G))).subtype := by
  apply map_injective (normalizer (L : Set G)).subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L i).trans (inf_le_left.trans L.le_normalizer)),
    map_embedded_pResidual,
    map_subgroupOf_eq_of_le (show L ⊓ F.Gi i ≤ normalizer (L : Set G)
      from inf_le_left.trans L.le_normalizer)]
  simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (i = 2 ∨ i = 3)) by omega, if_false]

variable (d : Data T L V F W)

  (e : (L ⧸ pCore 2 L) ≃* SL)

private theorem stabilizer_image (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G))).map
      (project d e) = P := by
  rw [← map_subgroupOf_inclusion _ _ _ (inf_le_left : L ⊓ F.Gi i ≤ L) L.le_normalizer,
    map_map, project_on_L]
  have hH : (L ⊓ F.Gi i).subgroupOf L = (F.Gi i).subgroupOf L := by
    ext l
    exact and_iff_right l.property
  rw [hH, hP, map_comap_eq_self_of_surjective
    (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)))]

private theorem residual_image (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    ((F.Li L i).subgroupOf (normalizer (L : Set G))).map (project d e) =
      MarkedAutomorphisms.residual P := by
  rw [residual_subgroupOf, map_embedded_pResidual, stabilizer_image d e i P hP]
  rfl

private theorem point_normalizer_le :
    normalizer (MarkedAutomorphisms.pointA : Set SL) ≤ pointParabolicSL := by
  intro x hx
  obtain ⟨g, hg, he⟩ := MarkedAutomorphisms.point_implementer (MulAut.conj x)
    (fun a ha => (mem_normalizer_iff.mp hx a).mp ha)
  have heq : x = g := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot he
  exact heq ▸ hg

private theorem stabilizer_preimage (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    (L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G)) =
      L.subgroupOf (normalizer (L : Set G)) ⊓ P.comap (project d e) := by
  ext m
  constructor
  · rintro ⟨hmL, hmH⟩
    refine ⟨hmL, ?_⟩
    have hl : (⟨m, hmL⟩ : L) ∈ (F.Gi i).subgroupOf L := hmH
    rw [hP] at hl
    change e (QuotientGroup.mk' (pCore 2 L) ⟨m, hmL⟩) ∈ P at hl
    rw [← project_apply_L d e] at hl
    exact hl
  · rintro ⟨hmL, hmP⟩
    refine ⟨hmL, ?_⟩
    have hl : (⟨m, hmL⟩ : L) ∈ P.comap
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
      change e (QuotientGroup.mk' (pCore 2 L) ⟨m, hmL⟩) ∈ P
      rw [← project_apply_L d e]
      exact hmP
    rw [← hP] at hl
    exact hl

/-- Lifting uses the literal stabilizer preimage and its characteristic residual.
It places no two-group condition on the ambient projection kernel. -/
theorem lift_point_normalizer
    (hP : (F.Gi 1).subgroupOf L =
      pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    (normalizer (MarkedAutomorphisms.pointA : Set SL)).comap (project d e) ≤
      (normalizer (F.Li L 1 : Set G)).subgroupOf (normalizer (L : Set G)) := by
  let M := normalizer (L : Set G)
  let H := (L ⊓ F.Gi 1).subgroupOf M
  let C := pointParabolicSL.comap (project d e)
  have hn : C ≤ normalizer (H : Set M) := by
    rw [show H = L.subgroupOf M ⊓ C from stabilizer_preimage d e 1 _ hP]
    apply le_normalizer_iff.mpr
    intro m hm a ha
    exact ⟨(inferInstance : (L.subgroupOf M).Normal).conj_mem a ha.1 m,
      C.mul_mem (C.mul_mem hm ha.2) (C.inv_mem hm)⟩
  have hr := normalizer_le_normalizer_characteristic_image H (pResidual 2 H)
  have hLi : (pResidual 2 H).map H.subtype = (F.Li L 1).subgroupOf M :=
    (residual_subgroupOf 1).symm
  rw [hLi] at hr
  rw [subgroupOf_normalizer_eq ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))]
  exact (comap_mono point_normalizer_le).trans (hn.trans hr)

include d

/-- All projection fields follow once one quotient marking matches the original
Sylow, point, and plane stabilizers. The missing flag marking is independent
of the ambient inner-action and direct-product construction. -/
theorem nonempty_of_flag_marking
    (hB : (((T : Subgroup G) ⊓ L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = borelSL)
    (hP : (F.Gi 1).subgroupOf L =
      pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hQ : (F.Gi 2).subgroupOf L =
      lineParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    Nonempty (NormalizerProjection T L V F) := by
  refine ⟨{
    quotientEquiv := e
    project := project d e
    on_L := project_on_L d e
    sylow_le := d.natural.chosen.sylow_normalizes_component
    inner_sylow_image := ?_
    point_image := ?_
    line_image := ?_
    lift_point_normalizer := lift_point_normalizer d e hP }⟩
  · rw [← map_subgroupOf_inclusion _ _ _ (inf_le_right : (T : Subgroup G) ⊓ L ≤ L)
      L.le_normalizer, map_map, project_on_L]
    exact hB
  · rw [residual_image d e 1 _ hP, MarkedAutomorphisms.point_residual]
  · rw [residual_image d e 2 _ hQ, MarkedAutomorphisms.line_residual]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
open Chapter12.Section08 Matrix.PSL3Two Stellmacher
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u

private theorem cut_coordinates (b : Basis 2) (i : Fin 2) (v : Space 3) :
    v ∈ cutSpace b i ↔ ∀ j : Fin 3, i.val < j.val → b.equivFun v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 3, b.equivFun v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem point_cut (b : Basis 2) (v : Space 3) :
    v ∈ cutSpace b 0 ↔ b.equivFun v 1 = 0 ∧ b.equivFun v 2 = 0 := by
  rw [cut_coordinates]
  constructor
  · intro h; exact ⟨h 1 (by decide),h 2 (by decide)⟩
  · rintro ⟨h1,h2⟩ j hj
    fin_cases j <;> simp_all

private theorem line_cut (b : Basis 2) (v : Space 3) :
    v ∈ cutSpace b 1 ↔ b.equivFun v 2 = 0 := by
  rw [cut_coordinates]
  constructor
  · intro h; exact h 2 (by decide)
  · intro h j hj
    fin_cases j <;> simp_all

private noncomputable def basisModel (b : Basis 2) : LinearGroup 3 ≃* SL :=
  (MulAut.conj b.equivFun).trans (slEquivLinear 3).symm

private theorem basisModel_act (b : Basis 2) (a : LinearGroup 3) (v : Space 3) :
    (basisModel b a).val.mulVec (b.equivFun v) = b.equivFun (a v) := by
  rw [← slEquivLinear_apply]
  change (slEquivLinear 3) ((slEquivLinear 3).symm ((MulAut.conj b.equivFun) a))
    (b.equivFun v) = _
  rw [MulEquiv.apply_symm_apply]
  change b.equivFun (a (b.equivFun.symm (b.equivFun v))) = _
  rw [b.equivFun.symm_apply_apply]

private theorem basisModel_point (b : Basis 2) (a : LinearGroup 3) :
    basisModel b a ∈ pointParabolicSL ↔ a ∈ parabolic (cutSpace b 0) := by
  rw [pointParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ v : Space 3, _ ↔ _) ↔ ∀ v : Space 3, _ ↔ _
  constructor
  · intro h v
    have hv := h (b.equivFun v)
    change ((basisModel b a).val.mulVec (b.equivFun v) 1 = 0 ∧
      (basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _ at hv
    rw [basisModel_act] at hv
    exact (point_cut b (a v)).trans (hv.trans (point_cut b v).symm)
  · intro h v
    obtain ⟨v,rfl⟩ := b.equivFun.surjective v
    have hv := h v
    rw [point_cut, point_cut] at hv
    change ((basisModel b a).val.mulVec (b.equivFun v) 1 = 0 ∧
      (basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _
    rwa [basisModel_act]

private theorem basisModel_line (b : Basis 2) (a : LinearGroup 3) :
    basisModel b a ∈ lineParabolicSL ↔ a ∈ parabolic (cutSpace b 1) := by
  rw [lineParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ v : Space 3, _ ↔ _) ↔ ∀ v : Space 3, _ ↔ _
  constructor
  · intro h v
    have hv := h (b.equivFun v)
    change ((basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _ at hv
    rw [basisModel_act] at hv
    exact (line_cut b (a v)).trans (hv.trans (line_cut b v).symm)
  · intro h v
    obtain ⟨v,rfl⟩ := b.equivFun.surjective v
    have hv := h v
    rw [line_cut, line_cut] at hv
    change ((basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _
    rwa [basisModel_act]

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem original_natural_action : letI := d.natural.chosen.elementary
    ∀ l : L, InvariantFlag.naturalFlagActorEquiv d.natural.naturalMarking.coordinates
      (setupSeedAction L V d.natural.chosen.normalizes l) =
        d.natural.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  let := d.natural.chosen.elementary
  intro l
  apply LinearEquiv.ext
  intro v
  obtain ⟨v,rfl⟩ := d.natural.naturalMarking.coordinates.surjective v
  obtain ⟨v,rfl⟩ := Additive.ofMul.surjective v
  rw [InvariantFlag.naturalFlagActorEquiv_intertwines]
  exact d.natural.naturalMarking.equivariant l (Additive.ofMul v)

private theorem original_stabilizer_iff : letI := d.natural.chosen.elementary
    ∀ (l : L) (i : ℕ), (l : G) ∈ F.Gi i ↔
      d.natural.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) ∈
        parabolic (F.naturalFlagSpace d.natural.naturalMarking.coordinates i) := by
  let := d.natural.chosen.elementary
  intro l i
  rw [← F.naturalFlagStabilizer_map, ← original_natural_action d,
    mem_map_equiv, MulEquiv.symm_apply_apply]
  exact (F.naturalFlagAction_mem_stabilizer L d.natural.chosen.normalizes i
    ⟨l,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩).symm

include d

/-- A quotient marking adapted to the very same original point and plane. -/
theorem exists_original_flag_marking
     :
    ∃ e : (L ⧸ pCore 2 L) ≃* SL,
      (((T : Subgroup G) ⊓ L).subgroupOf L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = borelSL ∧
      (F.Gi 1).subgroupOf L =
        pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ∧
      (F.Gi 2).subgroupOf L =
        lineParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
  let := d.natural.chosen.elementary
  let A := d.natural.naturalMarking
  obtain ⟨b,hb,hcuts⟩ := F.exists_naturalFlag_marking L d.natural.chosen.normalizes
    d.natural.full_L_action A.coordinates
  let e := A.quotientEquiv.trans (basisModel b)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hp (l : L) : (l : G) ∈ F.Gi 1 ↔ q l ∈ pointParabolicSL := by
    change _ ↔ basisModel b (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∈ _
    rw [basisModel_point, ← hcuts 0]
    exact original_stabilizer_iff d l 1
  have hq (l : L) : (l : G) ∈ F.Gi 2 ↔ q l ∈ lineParabolicSL := by
    change _ ↔ basisModel b (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∈ _
    rw [basisModel_line, ← hcuts 1]
    exact original_stabilizer_iff d l 2
  refine ⟨e,?_,?_,?_⟩
  · let M := normalizer (L : Set G)
    let LN := L.subgroupOf M
    let : LN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
    obtain ⟨S,hS⟩ := (T.subtype (d.natural.chosen.sylow_normalizes_component)).exists_subgroupOf_eq_of_normal LN
    let a : LN ≃* L := subgroupOfEquivOfLe L.le_normalizer
    let S' : Sylow 2 L := S.mapSurjective (f := a.toMonoidHom) a.surjective
    have hS' : (S' : Subgroup L) = ((T : Subgroup G) ⊓ L).subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [hS] at hx
        exact ⟨hx,(a x).property⟩
      · intro hl
        refine ⟨a.symm l,?_,a.apply_symm_apply l⟩
        rw [hS]
        exact hl.1
    let P : Sylow 2 SL := S'.mapSurjective (f := q)
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hP : (P : Subgroup SL) ≤ borelSL := by
      rintro x ⟨l,hl,rfl⟩
      rw [hS'] at hl
      exact ⟨(hp l).mp (F.invariant 1 hl.1), (hq l).mp (F.invariant 2 hl.1)⟩
    have heq := P.is_maximal' (IsPGroup.of_card (n := 3) card_borelSL) hP
    exact (congrArg (fun H : Subgroup L => H.map q) hS').symm.trans heq.symm
  · ext l; exact hp l
  · ext l; exact hq l

/-- Construct the marked normalizer projection from the actual chosen module and flag. -/
theorem nonempty_of_source
     :
    Nonempty (NormalizerProjection T L V F) := by
  obtain ⟨e,hB,hP,hQ⟩ := exists_original_flag_marking d
  exact nonempty_of_flag_marking d e hB hP hQ

/-- The actual projection and finite parabolic calculation give the source escape. -/
theorem normalizer_escape {c : CriticalPath (L := L) F}
    (h : Geometry d c) (k : CoreFacts c) : ¬ Y c ≤ normalizer (L : Set G) := by
  obtain ⟨p⟩ := nonempty_of_source d
  exact normalizer_escape_of_projection p parabolicImageTheorem h k

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructureAt
