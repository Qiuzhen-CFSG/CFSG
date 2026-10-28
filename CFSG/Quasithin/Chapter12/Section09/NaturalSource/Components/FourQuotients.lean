module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeComplete
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MatchingBinary
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
/-!
# The original degree-four point intersection and its quotient

The original point residual and its Sylow join induce the full natural
point parabolic. Passing through its actual two-core identifies the join
quotient order as 168. Every image of the intersection of that join with a
containing component therefore has two-core quotient order dividing 168.
Relative subnormality supplies a full Sylow subgroup in that same image.
The original residual image stays normalized and retains its SL₃(2) section.

FourRankOne and FourTernary use these literal maps to exclude the odd
rank-one and ternary enlargements in the degree-four branch of 12.9.3.
Source: Aschbacher--Smith, printed p.858, with the comparison in 12.5.3,
pp.817--818. The quotient-kernel argument follows the checked Section05
point-intersection development, adapted to the original natural module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
include h earlier

omit earlier in
/-- The original point residual is perfect. -/
theorem four_point_residual_perfect : Group.IsPerfect (F.Li L 1) := by
  let := h.chosen.elementary
  let : IsQuasisimple (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
    Li_core_quasisimple F h.naturalMarking 1 (Or.inr ⟨rfl,Or.inl rfl⟩)
  have hh := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (F.Li L 1)) pCore_isPGroup (Li_twoPerfect F 1)
  let := hh.perfect
  exact Group.IsPerfect.ofSurjective (f := (topEquiv (G := F.Li L 1)).toMonoidHom)
    topEquiv.surjective

/-- Normalization in the original Sylow join, with no ambient normality. -/
theorem four_point_join_normalizes : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) :=
  sup_le (F.Li L 1).le_normalizer (sylow_normalizes_Li h earlier F 1)

/-- The literal point residual with its original Sylow has quotient of order 168. -/
theorem four_point_residual_join_core_card :
    Nat.card ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) = 168 := by
  let := h.chosen.elementary
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let W := space (V := V) (F.Vi 1)
  obtain ⟨a,hak,ha⟩ := point_join_action h (by decide) earlier F
  have ha' : Function.Surjective a := by
    intro y
    obtain ⟨b,hb⟩ := ha y
    exact ⟨inclusion le_sup_left b,hb⟩
  have hJ : J ≤ L ⊔ (T : Subgroup G) := sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  have hk : IsPGroup 2 a.ker := by
    have hh := (h.action_kernel_isPGroup earlier.structural).comap_of_injective
      (inclusion hJ) (inclusion_injective hJ)
    rw [setupSeedAction_ker] at hh
    rw [hak]
    exact hh
  let e := a.pCoreQuotientEquiv ha' hk
  have hv : Module.finrank (ZMod 2) (Additive V) = 4 :=
    h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  have hw : Module.finrank (ZMod 2) W = 1 := flag_space_finrank F 1 (by decide)
  have hq : Module.finrank (ZMod 2) (Additive V ⧸ W) = 3 := by
    have hh := W.finrank_quotient_add_finrank
    omega
  let b := (Module.finBasisOfFinrankEq (ZMod 2) W hw).equivFun
  let c := (Module.finBasisOfFinrankEq (ZMod 2) (Additive V ⧸ W) hq).equivFun
  let d := quotientTwoCoreEquivOfCoordinates W b c
  rw [Nat.card_congr (e.trans d).toEquiv,Nat.card_prod]
  have hc1 : Nat.card (LinearGroup 1) = 1 := by
    rw [← Nat.card_congr (matrixEquivLinear 1).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc1,one_mul,←Nat.card_congr (slEquivLinear 3).toEquiv]
  exact Atlas.Comparisons.Exceptional.sl3Two_card

/-- The image of the original Sylow join intersected with its containing component. -/
@[expose] def fourPointIntersectionImage (L : Subgroup G) (D : Subgroup G)
    {X : Type*} [Group X] (f : D →* X) : Subgroup X :=
  (f.comp (inclusion (show (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ D ≤ D from inf_le_right))).range

/-- A two-core-free image of the original intersection has order dividing 168. -/
theorem four_point_intersection_corefree_card {K : Subgroup G}
    {X : Type*} [Group X] [Finite X] (ψ : K →* X)
    (hcore : pCore 2 (fourPointIntersectionImage F L K ψ) = ⊥) :
    Nat.card (fourPointIntersectionImage F L K ψ) ∣ 168 := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let f := ψ.comp (inclusion (show A ≤ K from inf_le_right))
  change pCore 2 f.range = ⊥ at hcore
  have hcoref : pCore 2 A ≤ f.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    rw [hcore] at hh
    have hh' := (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)
    intro x hx
    exact congrArg Subtype.val (hh' hx)
  let g := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (show A ≤ J from inf_le_left))
  have hkg : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hgcore : g.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hkg⟩
  have hgf : g.ker ≤ f.ker := hgcore.trans hcoref
  let r : (A ⧸ g.ker) →* f.range := QuotientGroup.lift g.ker f.rangeRestrict
    (fun x hx => Subtype.ext (hgf hx))
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' g.ker x,hx⟩
  have hcard : Nat.card f.range ∣ 168 := by
    have hd := card_dvd_of_surjective r hr
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
    exact (hd.trans g.range.card_subgroup_dvd_card).trans
      (dvd_of_eq (four_point_residual_join_core_card h earlier F))
  exact hcard

omit h earlier in
/-- Relative subnormality preserves the full original Sylow in the literal image. -/
theorem four_point_intersection_sylow {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    {X : Type*} [Group X] [Finite X] (ψ : K →* X) (hψ : Function.Surjective ψ) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ fourPointIntersectionImage F L K ψ := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let H := F.H
  let C := K.subgroupOf H
  obtain ⟨S,hS⟩ := (T.subtype (F.invariant 1)).exists_subgroupOf_eq_of_subnormal C hK.2.subnormal
  let c : C ≃* K := subgroupOfEquivOfLe hK.1
  let P := (S.mapSurjective (f := c.toMonoidHom) c.surjective).mapSurjective hψ
  refine ⟨P,?_⟩
  rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
  have hyT : (y : G) ∈ (T : Subgroup G) := by
    rw [hS] at hy
    exact hy
  have hyA : (y : G) ∈ A := ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hyT,y.property⟩
  exact ⟨⟨y,hyA⟩,rfl⟩

/-- The original intersection retains the order-168 bound even when its
two-core is nontrivial. -/
theorem four_point_intersection_core_quotient_card {K : Subgroup G}
    {X : Type*} [Group X] [Finite X] (ψ : K →* X) :
    Nat.card (fourPointIntersectionImage F L K ψ ⧸
      pCore 2 (fourPointIntersectionImage F L K ψ)) ∣ 168 := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let f := ψ.comp (inclusion (show A ≤ K from inf_le_right))
  let q := (QuotientGroup.mk' (pCore 2 f.range)).comp f.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective
  have hcoref : pCore 2 A ≤ q.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hh (mem_map_of_mem f.rangeRestrict hx))
  let g := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (show A ≤ J from inf_le_left))
  have hkg : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hgcore : g.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hkg⟩
  let r : (A ⧸ g.ker) →* (f.range ⧸ pCore 2 f.range) :=
    QuotientGroup.lift g.ker q (fun x hx => hcoref (hgcore hx))
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨QuotientGroup.mk' g.ker x,hx⟩
  have hd := card_dvd_of_surjective r hr
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  exact (hd.trans g.range.card_subgroup_dvd_card).trans
    (dvd_of_eq (four_point_residual_join_core_card h earlier F))

/-- The original point residual remains a local C-component in the literal point normalizer. -/
theorem four_point_local_in_normalizer :
    (F.Li L 1).subgroupOf F.H ∈ Chapter1.L F.H ((T : Subgroup G).subgroupOf F.H) := by
  exact (Chapter1.mem_LIn_iff_subgroupOf (F.invariant 1) ((F.Li_le L 1).trans inf_le_right)).mp
      ⟨(F.Li_le L 1).trans inf_le_right,Li_mem_local h earlier F 1 (Or.inr ⟨rfl,Or.inl rfl⟩)⟩

omit earlier in
/-- The literal point image in G₁/O₂(G₁) retains the original simple section. -/
theorem four_point_image_core_card :
    let B := (F.Li L 1).subgroupOf F.H
    let q := QuotientGroup.mk' (pCore 2 F.H)
    Nat.card (B.map q ⧸ pCore 2 (B.map q)) = 168 := by
  let B := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' (pCore 2 F.H)
  let a := subgroupOfEquivOfLe ((F.Li_le L 1).trans inf_le_right)
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  exact (Nat.card_congr (e.symm.trans b).toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card

/-- The literal residual image and intersection retain the full quotient Sylow,
normalization, and the SL₃(2) section simultaneously. -/
theorem four_point_image_data {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H) (hLD : F.Li L 1 ≤ D) :
    let q := QuotientGroup.mk' (pCore 2 D)
    let B := ((F.Li L 1).subgroupOf D).map q
    ∃ S : Sylow 2 (D ⧸ pCore 2 D),
      (S : Subgroup _) ≤ fourPointIntersectionImage F L D q ∧
      B ≤ fourPointIntersectionImage F L D q ∧
      fourPointIntersectionImage F L D q ≤ normalizer (B : Set _) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 D)
  let B := (F.Li L 1).subgroupOf D
  obtain ⟨S,hSJ⟩ := four_point_intersection_sylow (L := L) F hD q (QuotientGroup.mk'_surjective _)
  refine ⟨S,hSJ,?_,?_,?_⟩
  · rintro _ ⟨b,hb,rfl⟩
    exact ⟨⟨b,⟨(show F.Li L 1 ≤ F.Li L 1 ⊔ (T : Subgroup G) from le_sup_left) hb,b.property⟩⟩,rfl⟩
  · rintro _ ⟨a,rfl⟩
    apply B.le_normalizer_map q
    apply mem_map_of_mem
    intro b
    exact four_point_join_normalizes h earlier F a.property.1 (b : G)
  · let a : B ≃* F.Li L 1 := subgroupOfEquivOfLe hLD
    have hk : IsPGroup 2 (q.subgroupMap B).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    exact ⟨((q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
        (Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some)⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
