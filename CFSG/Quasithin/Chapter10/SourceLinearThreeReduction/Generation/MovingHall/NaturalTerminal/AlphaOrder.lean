module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaEntrance
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Field
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedAlphaCard
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.AlphaTransport
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The original natural field and Thompson alpha order

The first component of the selected paired source is a Sylow conjugate of
our original component. Their literal action images therefore have the
same SL₂ order. Strict monotonicity of q(q²−1) identifies the two field
orders. After the original fixed center vanishes, E.2.3 gives the order
of the common Thompson alpha subgroup as q².

Source: Aschbacher–Smith E.2.3 and 10.2.3(4), printed pp.216–217,746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
set_option backward.isDefEq.respectTransparency false
theorem source_natural_local_module_kernel_eq_twoCore
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) : Subgroup (localJoin T L)) ≤ centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) :
    centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
      pCore 2 (localJoin T L) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, source_natural_module_centralizer_isTwoGroup D degree hdegree hF e hn hJ⟩
  · intro x hx v hv
    exact Subtype.ext (D.core_centralizes_module (mem_map_of_mem H.subtype hx) v hv)

theorem source_natural_local_action_original_component
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) : Subgroup (localJoin T L)) ≤ centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) :
    let H := localJoin T L
    let U := D.moduleSubgroup.subgroupOf H
    letI : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    IsComponent (H ⧸ centralizer (U : Set H)) ((L.subgroupOf H).map q) ∧
      Nonempty (((L.subgroupOf H).map q) ≃* SL(2,F₀)) := by
  dsimp only
  let H := localJoin T L
  let : (D.moduleSubgroup.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let eqt := cComponentTwoCoreQuotientEquiv hA
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hh : IsComponent (H ⧸ pCore 2 H) (A.map (QuotientGroup.mk' (pCore 2 H))) ∧
      Nonempty ((A.map (QuotientGroup.mk' (pCore 2 H))) ≃* SL(2,F₀)) :=
    ⟨⟨hA.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv eqt⟩, ⟨eqt.symm.trans (aq.trans e)⟩⟩
  have htransfer (C : Subgroup H) [C.Normal] (hc : C = pCore 2 H) :
      IsComponent (H ⧸ C) (A.map (QuotientGroup.mk' C)) ∧
        Nonempty ((A.map (QuotientGroup.mk' C)) ≃* SL(2,F₀)) := by
    subst C
    exact hh
  exact htransfer _ (source_natural_local_module_kernel_eq_twoCore D degree hdegree hF e hn hJ)

theorem source_natural_paired_field_card
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      Nat.card F.Carrier = Nat.card F₀ := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
    (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  have hP := source_natural_minimal_parabolic D e degree hdegree hF hn
  obtain ⟨K,hK,hi,hcan,_,_,_,_⟩ := first_component_localClass h36 hG S hP U hU hJ q hq hk
    (source_join_not_solvable D) (source_join_fitting D) d F c hexchange
  have hJY : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  let := d.product.first_normal
  have hYA : Y ≤ normalizer (d.first.map Y.subtype : Set (X ⧸ C)) := by
    have hh := d.first.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hgen := selected_component_sup_sylow S hP U hU hJ q hq hk Y _ hJY hYA K hK hcan
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  have hm : (L.subgroupOf X).map q =
      (d.first.map (MulAut.conjNormal (q (s:X))).toMonoidHom).map Y.subtype := by
    rw [hs,map_map]
    have hcomp : q.comp (MulAut.conj (s:X)).toMonoidHom =
        (MulAut.conj (q (s:X))).toMonoidHom.comp q := by
      ext x
      change q ((s:X)*x*(s:X)⁻¹) = q (s:X)*q x*(q (s:X))⁻¹
      rw [map_mul,map_mul,map_inv]
    rw [hcomp,←map_map,hi,map_map,map_map]
    rfl
  have hcard : Nat.card ((L.subgroupOf X).map q) = Nat.card SL(2,F₀) := by
    obtain ⟨a⟩ := (source_natural_local_action_original_component D degree hdegree hF e hn hJ).2
    exact Nat.card_congr a.toEquiv
  have hfirst : Nat.card d.first = Nat.card SL(2,F₀) := by
    rwa [hm,card_map_of_injective Y.subtype_injective,
      card_map_of_injective (f := (MulAut.conjNormal (q (s:X)) : MulAut Y).toMonoidHom)
        (MulAut.conjNormal (q (s:X)) : MulAut Y).injective] at hcard
  have hSL : Nat.card SL(2,F.Carrier) = Nat.card SL(2,F₀) := by
    rw [←c.first_eq,card_map_of_injective c.action.groupEquiv.symm.injective] at hfirst
    rw [Nat.card_congr ((⊤ : Subgroup SL(2,F.Carrier)).prodEquiv
      (⊥ : Subgroup SL(2,F.Carrier))).toEquiv,
      Nat.card_prod,card_top,card_bot,mul_one] at hfirst
    exact hfirst
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at hSL
  have ha : 1 < Nat.card F.Carrier := Finite.one_lt_card
  have hb : 1 < Nat.card F₀ := Finite.one_lt_card
  have hsa : 1 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
  have hsb : 1 ≤ Nat.card F₀ ^ 2 := by nlinarith
  have hpa := Nat.sub_add_cancel hsa
  have hpb := Nat.sub_add_cancel hsb
  apply le_antisymm <;> by_contra! hh
  · have hmul := Nat.mul_lt_mul_of_lt_of_le hh (by nlinarith : Nat.card F₀ ^ 2 - 1 ≤ Nat.card F.Carrier ^ 2 - 1)
      (by nlinarith : 0 < Nat.card F.Carrier ^ 2 - 1)
    omega
  · have hmul := Nat.mul_lt_mul_of_lt_of_le hh (by nlinarith : Nat.card F.Carrier ^ 2 - 1 ≤ Nat.card F₀ ^ 2 - 1)
      (by nlinarith : 0 < Nat.card F₀ ^ 2 - 1)
    omega

theorem source_natural_alpha_card_of_paired_linear
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      Nat.card (thompsonAlpha (T : Subgroup G)) = Nat.card F₀ ^ 2 := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have hfield := source_natural_paired_field_card D degree hdegree hF e hn hJ d F c hexchange
  have hzS : (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X) = ⊥ := by
    apply bot_unique
    rintro x ⟨hx,hxc⟩
    have hh : (x:G) ∈ (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
      refine ⟨hx,?_⟩
      intro l hl
      obtain ⟨a,ha,rfl⟩ := (source_join_residual D).symm ▸ hl
      exact congrArg X.subtype (hxc a ha)
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp ((source_sylow_orbit_centralizer_eq_bot hz) ▸ hh)))
  have hcard := RankOneBaumann.PairedFactorOrbit.source_alpha_card_of_trivial_sylow_residual_centralizer
    S (source_natural_minimal_parabolic D e degree hdegree hF hn) U hU hJ q hq hk d F c hexchange hzS
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hα : (thompsonAlpha (S : Subgroup X)).map X.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      hS]
  have hm := card_map_of_injective (K := thompsonAlpha (S : Subgroup X)) X.subtype_injective
  rw [hα] at hm
  rw [hfield] at hcard
  exact hm.trans hcard

/-- The common alpha order in the original moving natural branch. -/
theorem Context.original_alpha_card
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    Nat.card (thompsonAlpha (T : Subgroup G)) = Nat.card F₀ ^ 2 := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D degree hdegree hF e
  exact source_natural_alpha_card_of_paired_linear D degree hdegree hF e ctx.nonnormal
    (ctx.fixed_centers_of_natural_marking D degree hdegree hF e mark hBR).1
    (source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving) d K c hexchange

/-- The binary rank is twice the original field degree, with no new rank premise. -/
theorem Context.original_alpha_rank
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F₀ = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F₀)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    primeRank 2 (thompsonAlpha (T : Subgroup G)) = 2 * degree := by
  let : IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G)) := omegaOneCenterAmbient_elementaryAbelian _
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),
    ctx.original_alpha_card D degree hdegree hF e mark hBR, hF, ←pow_mul,
    Nat.log_pow (by decide : 1 < 2), mul_comm]

end CFSG.Quasithin.Chapter10.MovingHall
