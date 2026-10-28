module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Models
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# The plane-component reduction in degree five

The literal action of G₂=N_G(V₂) maps onto GL₂(2)≃S₃. Every perfect
subgroup of G₂ centralizes V₂. A normal C-component whose two-core
quotient is centerless with outer automorphism group of order prime to
three therefore has quotient three-rank at most one: otherwise A.3.18's
index argument contradicts this S₃ quotient. The actual PSL₄(2), PSL₅(2)
and M₂₄ models are consequently excluded.

The original solvable residual L₂ lies in L₁. Every containing plane
component lies strictly inside the constructed point component. If L₁ is
normal in G₁, this proves the plane component is L₂. Every remaining
failure gives a strict nested pair with larger point model and with all
three terminal plane models excluded. The ComponentGeometry application
leaves precisely the source plane-overgroup comparison and the i=3
component assertion explicit; qt-d-1291-natural-source retains their
proofs, the other source branches, and final assembly.

Source: Aschbacher--Smith, 12.9.3, printed pp.858--859 of
refs/quasithin.pdf, and the index argument of A.3.18, pp.51--52.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ} {K : GroupClass.{u}}

/-- The original plane action, in coordinates on the three nonzero vectors. -/
noncomputable def planeAction [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (hn : 2 ≤ n) : F.Gi 2 →* Equiv.Perm (Fin 3) :=
  let e := (Module.finBasisOfFinrankEq (ZMod 2) _ (flag_space_finrank F 2 hn)).equivFun
  linearTwoEquivSymmetricThree.toMonoidHom.comp
    ((linearGroupCongr e).toMonoidHom.comp (flagLinearAction F 2))

/-- The original natural marking supplies the full S₃ action on the plane. -/
theorem planeAction_surjective [IsElementaryAbelian 2 V]
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) (hn : 2 ≤ n) :
    Function.Surjective (planeAction F hn) := by
  apply linearTwoEquivSymmetricThree.surjective.comp
  apply (linearGroupCongr _).surjective.comp
  intro a
  obtain ⟨l,hl,he⟩ := normalizer_full_action h.naturalMarking.geometryAction
    (F.Vi 2) (F.le_seed 2) a
  refine ⟨⟨l,hl⟩,?_⟩
  ext v
  exact (h.naturalMarking.geometryAction.conjugation l v.val).symm.trans
    (congrArg (fun w : Additive V => (w.toMul : G)) (he v))

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- Every perfect subgroup of the plane normalizer fixes the plane pointwise. -/
theorem plane_perfect_centralizes [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (hn : 2 ≤ n) (D : Subgroup G)
    (hDG : D ≤ F.Gi 2) [Group.IsPerfect D] : D ≤ centralizer (F.Vi 2 : Set G) := by
  let f := (planeAction F hn).comp (inclusion hDG)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetricThree_solvable
  have hf : f = 1 := by
    apply MonoidHom.range_eq_bot_iff.mp
    apply bot_unique
    have hm := map_solvableResidual_le f
    simpa only [solvableResidual_eq_top, solvableResidual_eq_bot,
      ← MonoidHom.range_eq_map] using hm
  intro d hd v hv
  have he := DFunLike.congr_fun hf (⟨d,hd⟩ : D)
  change planeAction F hn ⟨d,hDG hd⟩ = 1 at he
  have he' : flagLinearAction F 2 ⟨d,hDG hd⟩ = 1 := by
    let e := (Module.finBasisOfFinrankEq (ZMod 2) _ (flag_space_finrank F 2 hn)).equivFun
    apply (linearGroupCongr e).injective
    apply linearTwoEquivSymmetricThree.injective
    simpa only [e,planeAction,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_one] using he
  have hval := congrArg (fun a => (a
    (⟨Additive.ofMul ⟨v,F.le_seed 2 hv⟩,hv⟩ : space (V := V) (F.Vi 2))).val.toMul.val) he'
  change d * v * d⁻¹ = v at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- A.3.18 applied to the literal normal plane component: its centerless
quotient has three-rank at most one when its outer group has order prime to three. -/
theorem plane_component_three_rank_le_one
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hnD : (D.subgroupOf (F.Gi 2)).Normal)
    (hz : center (D ⧸ pCore 2 D) = ⊥)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (D ⧸ pCore 2 D)))) :
    primeRank 3 (D ⧸ pCore 2 D) ≤ 1 := by
  let := h.chosen.elementary
  let C := D.subgroupOf (F.Gi 2)
  let := hnD
  let := hD.2.perfect
  let e := subgroupOfEquivOfLe hD.1
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hz' : center (C ⧸ pCore 2 C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hm := (centerCongr eQ ⟨x,hx⟩).property
    change eQ x ∈ center (D ⧸ pCore 2 D) at hm
    rw [hz,mem_bot] at hm
    exact mem_bot.mpr (eQ.injective (hm.trans (map_one eQ).symm))
  have ho' : Nat.Coprime 3 (Nat.card (MulAut.Outer (C ⧸ pCore 2 C))) := by
    rwa [Nat.card_congr (MulAut.outerCongr eQ).toEquiv]
  have hG : primeRank 3 (F.Gi 2) ≤ 2 :=
    (CFSG.Quasithin.isQuasithin_iff_twoLocal.mp h.source.simpleQTKE.quasithin)
      _ (Gi_twoLocal h F 2 (by decide)) 3 Nat.prime_three (by decide)
  by_contra hle
  have hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by
    rw [primeRank_equiv 3 eQ]
    omega
  have hi := cComponent_index_coprime_three_of_quotient C hD.2 hz' hr hG ho'
  let f := planeAction F (show 2 ≤ n from by have := h.rank; omega)
  have hf : Function.Surjective f := planeAction_surjective h F _
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetricThree_solvable
  have hk : C ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply bot_unique
    have hC := le_solvableResidual_of_isPerfect C
    exact (map_mono hC).trans (by simpa only [solvableResidual_eq_bot] using map_solvableResidual_le f)
  have hd := index_dvd_of_le hk
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (topEquiv (G := Equiv.Perm (Fin 3))).toEquiv] at hd
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by rw [Nat.card_eq_fintype_card]; decide
  rw [h6] at hd
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hi) ((by decide : 3 ∣ 6).trans hd)

private theorem center_bot_transfer {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hy : center Y = ⊥) : center X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hm : e x ∈ center Y := (centerCongr e ⟨x,hx⟩).property
  rw [hy,mem_bot] at hm
  exact mem_bot.mpr (e.map_eq_one_iff.mp hm)

private theorem coprime_three_of_two {X : Type*} [Group X] [Finite X]
    (hp : IsPGroup 2 X) : Nat.Coprime 3 (Nat.card X) := by
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [hk]
  exact (by decide : Nat.Coprime 3 2).pow_right k

/-- Neither PSL₄(2) nor PSL₅(2) can be the two-core quotient of a
normal plane component. Both intrinsic three-rank and outer-action premises
are discharged on the actual binary linear model. -/
theorem plane_component_not_linear
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hnD : (D.subgroupOf (F.Gi 2)).Normal) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) d 2 := by
  rintro ⟨k,hk,hfin,hcard,⟨e₀⟩⟩
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let e := ((e₀.trans (Atlas.fieldEquivPSL d ek)).trans
    (projectiveEquivLinear (by omega : 0 < d))).trans (slEquivLinear d).symm
  have hz := center_bot_transfer e (binary_center_eq_bot (by omega))
  have ho : IsPGroup 2 (MulAut.Outer (D ⧸ pCore 2 D)) :=
    (sl_outer_isTwoGroup hd).of_equiv (MulAut.outerCongr e).symm
  have hr := plane_component_three_rank_le_one h F D hD hnD hz
    (coprime_three_of_two ho)
  rw [primeRank_equiv 3 e] at hr
  have hlo := BinaryLinear.SmallCubicRank.four_or_five hd
  omega

/-- The M₂₄ alternative in the last paragraph of 12.9.3 is impossible.
Its actual nonabelian Sylow three-group and outer automorphisms supply the
rank and index obstruction. -/
theorem plane_component_not_mathieu
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hnD : (D.subgroupOf (F.Gi 2)).Normal) :
    ¬ Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M24) := by
  rintro ⟨e⟩
  have hz := center_bot_transfer e Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
  have ho : IsPGroup 2 (MulAut.Outer (D ⧸ pCore 2 D)) :=
    Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  have hr := plane_component_three_rank_le_one h F D hD hnD hz
    (coprime_three_of_two ho)
  rw [primeRank_equiv 3 e] at hr
  let : IsCyclic (Sporadic.Mathieu.m24Sylow3 : Subgroup Sporadic.Mathieu.M24) :=
    Sporadic.Mathieu.m24Sylow3.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let eS := MulEquiv.subgroupCongr Sporadic.Mathieu.m24Sylow3_coe
  let : IsCyclic Sporadic.Mathieu.m24Sylow3Subgroup := isCyclic_of_surjective eS eS.surjective
  exact Sporadic.Mathieu.m24Sylow3Subgroup_isNonabelian inferInstance

/-- The point residual does not preserve the intermediate plane: its
action on V/V₁ is irreducible. -/
theorem point_residual_not_le_plane_normalizer
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) :
    ¬ F.Li L 1 ≤ F.Gi 2 := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let : IsElementaryAbelian 2 (F.tilde V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
  intro hn
  obtain he | he := F.invariant_subgroup_of_ambient_natural h.naturalMarking h.rank.1
    (F.Vi 2) (F.monotone (by decide : 1 ≤ 2)) (F.le_seed 2) hn
  · have hc := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [F.card 2 (by have := h.rank; omega),F.card 1 (by have := h.rank; omega)] at hc
    norm_num at hc
  · have hc := congrArg (fun A : Subgroup G => Nat.card A) (he.trans F.last.symm)
    rw [F.card 2 (by have := h.rank; omega),F.card n le_rfl] at hc
    have hp := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc
    have := h.rank
    omega

/-- The degree-five L₂ is perfect because it is the solvable residual,
with its original ambient embedding. -/
theorem five_plane_residual_perfect (F : InvariantFlag T V 5) :
    Group.IsPerfect (F.Li L 2) := by
  have he : F.Li L 2 = (solvableResidual (L ⊓ F.Gi 2 : Subgroup G)).map
      (L ⊓ F.Gi 2).subtype := by
    unfold Li
    rw [if_pos (by decide)]
  let : Group.IsPerfect ((solvableResidual (L ⊓ F.Gi 2 : Subgroup G)).map
      (L ⊓ F.Gi 2).subtype) := Group.IsPerfect.map _
  let e := MulEquiv.subgroupCongr he
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Every containing plane C-component centralizes the literal V₂. -/
theorem plane_component_centralizes
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2)) :
    D ≤ centralizer (F.Vi 2 : Set G) := by
  let := h.chosen.elementary
  let e := subgroupOfEquivOfLe hD.1
  let := hD.2.perfect
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact plane_perfect_centralizes F (by have := h.rank; omega) D hD.1

/-- The original L₂ lies in L₁, using perfectness and the point-normalizer
two-residual rather than replacing either residual convention. -/
theorem five_plane_residual_le_point
    (h : HigherRankHypothesis K T L V 5) (F : InvariantFlag T V 5) :
    F.Li L 2 ≤ F.Li L 1 := by
  let := h.chosen.elementary
  let := five_plane_residual_perfect (L := L) F
  have hc := plane_perfect_centralizes F (by decide) (F.Li L 2)
    ((F.Li_le L 2).trans inf_le_right)
  have hH : F.Li L 2 ≤ F.H :=
    (hc.trans (centralizer_le (F.monotone (by decide : 1 ≤ 2)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hLH : F.Li L 2 ≤ L ⊓ F.H := le_inf ((F.Li_le L 2).trans inf_le_left) hH
  let B := (F.Li L 2).subgroupOf (L ⊓ F.H)
  let e := subgroupOfEquivOfLe hLH
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent ((L ⊓ F.H : Subgroup G) ⧸ pResidual 2 (L ⊓ F.H : Subgroup G)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hb := le_of_isPerfect_of_solvable_quotient B (pResidual 2 (L ⊓ F.H : Subgroup G))
  have hm := map_mono (f := (L ⊓ F.H).subtype) hb
  rw [map_subgroupOf_eq_of_le hLH] at hm
  have he : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map
      (L ⊓ F.H).subtype := by
    unfold Li
    rw [if_neg (by decide)]
    rfl
  rwa [he]

/-- A containing plane component lies strictly inside any relatively
normal point overgroup containing L₁. The nonsolvable L₂ forces containment;
irreducibility of V/V₁ makes it strict. -/
theorem five_plane_component_lt_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hLD : F.Li L 2 ≤ D) (J : Subgroup G) (hJH : J ≤ F.H)
    (hLJ : F.Li L 1 ≤ J) (hJn : (J.subgroupOf F.H).Normal) : D < J := by
  have hDH : D ≤ F.H :=
    ((plane_component_centralizes h F D hD).trans
      (centralizer_le (F.monotone (by decide : 1 ≤ 2)))).trans
      (Subgroup.centralizer_le_normalizer _)
  let C := D.subgroupOf (F.Gi 2)
  let e := subgroupOfEquivOfLe hD.1
  have htop : (⊤ : Subgroup D).IsCComponent := by
    have hc : (⊤ : Subgroup C).IsCComponent := by
      simpa only [subgroupOf_self] using hD.2.subgroupOf (le_refl _)
    have he := hc.map_equiv e
    rw [map_top_of_surjective e.toMonoidHom e.surjective] at he
    exact he
  let N := J.subgroupOf D
  have hnN : N.Normal := by
    constructor
    intro x hx d
    exact (mem_normalizer_iff.mp
      (((normal_subgroupOf_iff_le_normalizer hJH).mp hJn) (hDH d.property)) (x : G)).mp hx
  let := hnN
  let B := (F.Li L 2).subgroupOf D
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let eB := subgroupOfEquivOfLe hLD
    let : Group.IsSolvable (F.Li L 2) := Group.isSolvable_of_surjective
      (f := eB.toMonoidHom) eB.surjective
    have hl := (Li_mem_local h earlier F 2 (Or.inl ⟨rfl,by decide,by decide⟩)).1
    let eL := subgroupOfEquivOfLe (show F.Li L 2 ≤ F.Li L 2 ⊔ (T : Subgroup G) from le_sup_left)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := eL.toMonoidHom) eL.injective)
  have ht : (⊤ : Subgroup D) ≤ N := htop.le_normal_of_nonsolvable_subgroup hB le_top
    (comap_mono ((five_plane_residual_le_point h F).trans hLJ))
  have hDJ : D ≤ J := subgroupOf_eq_top.mp (top_unique ht)
  refine lt_of_le_of_ne hDJ ?_
  intro he
  exact point_residual_not_le_plane_normalizer h F (hLJ.trans (he ▸ hD.1))

/-- The model exclusions discharge the final contradiction in the plane-index
branch once the source Sylow-overgroup comparison has supplied its shortlist. -/
theorem five_plane_component_of_enlargement_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hmodels : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn (F.Gi 2) →
      F.Li L 2 < D → (D.subgroupOf (F.Gi 2)).Normal →
        ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 ∨
          Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M24)) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have he : D = F.Li L 2 := by
    by_contra hne
    have hlt : F.Li L 2 < D := lt_of_le_of_ne hd.2.1 (Ne.symm hne)
    obtain hm | hm := hmodels D hd.1 hlt hd.2.2
    · exact plane_component_not_linear h F D hd.1 hd.2.2 (Or.inl rfl) hm
    · exact plane_component_not_mathieu h F D hd.1 hd.2.2 hm
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- Apply the plane-index exclusion and the already proved point/hyperplane
construction to the unchanged source component record. The remaining premises
are the plane overgroup comparison and the dimension-three component; their
proof and the abelianity argument stay with qt-d-1291-natural-source. -/
theorem five_componentGeometry_of_plane_overgroups
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hmodels : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn (F.Gi 2) →
      F.Li L 2 < D → (D.subgroupOf (F.Gi 2)).Normal →
        ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 ∨
          Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M24))
    (hthree : ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal) : Nonempty (ComponentGeometry F L) := by
  apply five_componentGeometry_of_middle_components h earlier F
  intro i hi
  rcases hi with rfl | rfl
  · exact five_plane_component_of_enlargement_models h earlier F hmodels
  · exact hthree

/-- The literal point and plane components in degree five form the strict
nested pair used in the source Sylow-overgroup comparison. Their existence,
relative normality, placement, and three terminal model exclusions are all
conclusions here. -/
theorem exists_five_nested_components
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 ≤ J ∧
      (J.subgroupOf F.H).Normal ∧
      (J = F.Li L 1 ∨ LargePointModel (J ⧸ pCore 2 J)) ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 ≤ D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧
      ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 ∧
      ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 5 2 ∧
      ¬ Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M24) := by
  obtain ⟨J,hJ,hLJ,hJn,hJm⟩ := exists_five_point_component h earlier F
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  exact ⟨J,D,hJ,hLJ,hJn,hJm,hd.1,hd.2.1,hd.2.2,
    five_plane_component_lt_point h earlier F D hd.1 hd.2.1 J hJ.1 hLJ hJn,
    plane_component_not_linear h F D hd.1 hd.2.2 (Or.inl rfl),
    plane_component_not_linear h F D hd.1 hd.2.2 (Or.inr rfl),
    plane_component_not_mathieu h F D hd.1 hd.2.2⟩

omit [Finite G] in
/-- A perfect plane subgroup contained in L lies in the source's solvable
residual L₂. This uses the exceptional degree-five residual convention. -/
theorem five_perfect_plane_le_residual
    (F : InvariantFlag T V 5) (D : Subgroup G) [Group.IsPerfect D]
    (hDL : D ≤ L) (hDG : D ≤ F.Gi 2) : D ≤ F.Li L 2 := by
  have hDJ : D ≤ L ⊓ F.Gi 2 := le_inf hDL hDG
  let B := D.subgroupOf (L ⊓ F.Gi 2)
  let e := subgroupOfEquivOfLe hDJ
  let : Group.IsPerfect B :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hb := le_solvableResidual_of_isPerfect B
  have hm := map_mono (f := (L ⊓ F.Gi 2).subtype) hb
  rw [map_subgroupOf_eq_of_le hDJ] at hm
  have he : F.Li L 2 = (solvableResidual (L ⊓ F.Gi 2 : Subgroup G)).map
      (L ⊓ F.Gi 2).subtype := by
    unfold Li
    rw [if_pos (by decide)]
  rwa [he]

/-- The plane-index assertion of 12.9.3 is proved whenever L₁ is normal
in the point normalizer. No model catalogue is needed in this branch. -/
theorem five_plane_component_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hL1 : ((F.Li L 1).subgroupOf F.H).Normal) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have hlt := five_plane_component_lt_point h earlier F D hd.1 hd.2.1
    (F.Li L 1) ((F.Li_le L 1).trans inf_le_right) le_rfl hL1
  let := hd.1.2.perfect
  let e := subgroupOfEquivOfLe hd.1.1
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have he : D = F.Li L 2 := le_antisymm
    (five_perfect_plane_le_residual F D
      (hlt.le.trans ((F.Li_le L 1).trans inf_le_left)) hd.1.1) hd.2.1
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- Every remaining failure at the plane yields the actual strict nested
pair. The point component has one of the three larger models, whereas the
plane component cannot have either binary-linear large model or M₂₄. -/
theorem exists_five_strict_plane_components
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hfail : ¬ (((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal)) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < J ∧
      (J.subgroupOf F.H).Normal ∧ LargePointModel (J ⧸ pCore 2 J) ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 < D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧ ¬ D ≤ L ∧
      ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 ∧
      ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 5 2 ∧
      ¬ Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M24) := by
  obtain ⟨J,D,hJ,hLJ,hJn,hJm,hD,hLD,hDn,hDJ,hfour,hfive,hmathieu⟩ :=
    exists_five_nested_components h earlier F
  have hne : D ≠ F.Li L 2 := fun he => hfail (he ▸ ⟨hD.2,hDn⟩)
  have hlt : F.Li L 2 < D := lt_of_le_of_ne hLD (Ne.symm hne)
  have hDL : ¬ D ≤ L := by
    intro hDL
    let := hD.2.perfect
    let e := subgroupOfEquivOfLe hD.1
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact hlt.not_ge (five_perfect_plane_le_residual F D hDL hD.1)
  have hJne : J ≠ F.Li L 1 := by
    intro he
    exact hDL (hDJ.le.trans (he ▸ (F.Li_le L 1).trans inf_le_left))
  exact ⟨J,D,hJ,lt_of_le_of_ne hLJ (Ne.symm hJne),hJn,hJm.resolve_left hJne,
    hD,hlt,hDn,hDJ,hDL,hfour,hfive,hmathieu⟩

/-- The normal-point branch now supplies the abelian span and both end
components together with the plane component. Only the i=3 component remains
explicit; the natural-source assembly owner retains that source assertion. -/
theorem five_abelian_componentGeometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hL1 : ((F.Li L 1).subgroupOf F.H).Normal)
    (hthree : ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal) :
    IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L) := by
  refine ⟨point_span_abelian_of_point_residual_normal h (Or.inr rfl) earlier F hL1, ?_⟩
  apply five_componentGeometry_of_middle_components h earlier F
  intro i hi
  rcases hi with rfl | rfl
  · exact five_plane_component_of_point_normal h earlier F hL1
  · exact hthree


end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
