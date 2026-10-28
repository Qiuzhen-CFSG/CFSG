module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OuterFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.LongFixed
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The characteristic subgroup of the selected full outer centralizer

The marked graph actor supplies an order lower bound for a maximizing
outer T-centralizer; the actors are not identified. The exact q³ fixed
core and the original 2m field-index bound force the maximizer's inner
fixed Sylow outside O₂(L). Its full centralizer is therefore nonabelian.
A finite two-group's nontrivial derived group meets its center, yielding
a nontrivial elementary characteristic subgroup in O₂(L).

The same selected involution and escaping ambient two-normalizer retain
this subgroup and both full-endpoint Sylow conditions. The long-root
intersection and its invariance are still required to contradict LongFixed.
Source: Aschbacher–Smith F.4.37(4), printed p.293 of refs/quasithin.pdf.
Both degree-two orientations and q=4 are retained.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- If the fixed inner Sylow lies in the core, the full fixed Sylow is smaller than 2q⁴. -/
theorem Preparation.unitaryFour_outer_centralizer_card_of_inner_core
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hfix : ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G) ≤ L.pCoreIn 2) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({u.val} : Set G) : Subgroup G) < 2*(2^m)^4 := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  have hPT : P ≤ (T : Subgroup G) := inf_le_left
  let : (L.subgroupOf (T : Subgroup G)).Normal :=
    normal_subgroupOf_of_le_normalizer h.sylow_normalizes
  have hdiv : L.relIndex P ∣ L.relIndex (T : Subgroup G) := by
    rw [←relIndex_subgroupOf (H := L) hPT]
    exact relIndex_dvd_index_of_normal _ _
  have hindex : L.relIndex P ≤ 2*m := Nat.le_of_dvd (by omega)
    (hdiv.trans (d.unitaryFour_reduced_sylow_index_dvd h hH hp m hm hc))
  have hfixed : Nat.card (L.subgroupOf P) ≤ (2^m)^3 := by
    let j : L.subgroupOf P → (L.pCoreIn 2 ⊓ centralizer ({u.val} : Set G) : Subgroup G) :=
      fun x => ⟨x.val.val,⟨hfix ⟨⟨x.val.property.1,x.property⟩,x.val.property.2⟩,x.val.property.2⟩⟩
    have hj : Function.Injective j := by
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (L.pCoreIn 2 ⊓ centralizer ({u.val} : Set G) : Subgroup G) => z.val) hh
    exact (Nat.card_le_card_of_injective j hj).trans
      (d.unitaryFour_outer_core_fixed_card_eq h hH hp m hm hc u hu ho).le
  have hcard := (L.subgroupOf P).card_mul_index
  change Nat.card (L.subgroupOf P) * L.relIndex P = Nat.card P at hcard
  calc
    Nat.card P = Nat.card (L.subgroupOf P) * L.relIndex P := hcard.symm
    _ ≤ (2^m)^3 * (2*m) := Nat.mul_le_mul hfixed hindex
    _ < (2^m)^3 * (2*(2^m)) := Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_left m.lt_two_pow_self (by decide)) (by positivity)
    _ = 2*(2^m)^4 := by ring

omit hc in
/-- The maximizing outer involution fixes an inner-Sylow element outside the core. -/
theorem Preparation.unitaryFour_degreeTwo_maximal_outer_inner_not_le_core
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T))) :
    ¬ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G) ≤ L.pCoreIn 2 := by
  intro hfix
  have huC := d.unitaryFour_outer_centralizer_card_of_inner_core h hH hp m hm (.inr he) u hu ho hfix
  obtain ⟨_,_,g,_,hgT,hg2,hgo,_,hgc,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  let gT : T := ⟨g.val,hgT⟩
  have hgT2 : orderOf gT=2 := (Subgroup.orderOf_coe gT).symm.trans hg2
  have hcards (x : T) : Nat.card (centralizer ({x} : Set T)) =
      Nat.card ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G) : Subgroup G) := by
    rw [←map_subtype_centralizer_singleton,card_map_of_injective (T : Subgroup G).subtype_injective]
  have hmax' := hmax gT hgT2 hgo
  rw [hcards gT,hcards u] at hmax'
  have hgC : Nat.card (sourceS L H ⊓ centralizer ({g.val} : Set G) : Subgroup G) ≤
      Nat.card ((T : Subgroup G) ⊓ centralizer ({g.val} : Set G) : Subgroup G) :=
    card_le_of_le (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
  rw [hgc] at hgC
  exact (not_lt_of_ge (hgC.trans hmax')) huC
omit hc in
/-- The center–derived subgroup of the maximizing full centralizer is
nontrivial. The comparison with the graph actor only supplies its order bound. -/
theorem Preparation.unitaryFour_degreeTwo_maximal_derived_center_ne_bot
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T))) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    (center P ⊓ _root_.commutator P).map P.subtype ≠ ⊥ := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←d.unitary_thompson h hH hp m hm (.inr he)]
    exact sSup_le fun _ hA => hA.1
  have hder : _root_.commutator P ≠ ⊥ := by
    intro hh
    let : IsMulCommutative P := (_root_.commutator_eq_bot_iff P).mp hh
    apply d.unitaryFour_degreeTwo_maximal_outer_inner_not_le_core h hH hp m hm he u hu ho hmax
    intro x hx
    apply d.unitaryFour_outer_fixed_core_centralizer h hH hp m hm (.inr he) u hu ho
    refine ⟨hx.1,mem_centralizer_iff.mpr fun v hv => ?_⟩
    let xp : P := ⟨x,hx.1.1,hx.2⟩
    let vp : P := ⟨v,hQT hv.1,hv.2⟩
    exact congrArg Subtype.val (mul_comm vp xp)
  have hn := center_inf_ne_bot_of_normal (T.isPGroup'.to_le (show P ≤ (T : Subgroup G) from inf_le_left))
    (_root_.commutator P) hder
  change (center P ⊓ _root_.commutator P).map P.subtype ≠ ⊥
  intro hh
  apply hn
  exact (map_injective P.subtype_injective) (hh.trans (Subgroup.map_bot _).symm)

omit hc in
/-- The same selected involution and escaping normalizer retain a nontrivial elementary characteristic subgroup in the original core. -/
theorem Preparation.unitaryFour_degreeTwo_selected_center
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        Nat.card (L.pCoreIn 2 ⊓ centralizer ({f.val} : Set G) : Subgroup G) = (2^m)^3 ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Z ≤ L.pCoreIn 2 ∧
          V ≤ normalizer (Z : Set G) := by
  have hc : FourLocalComparison L (residual H) (sourceS L H) m hm := .inr he
  obtain ⟨_,_,g,_,hgT,hg,hgo,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  have hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L :=
    ⟨⟨g.val,hgT⟩,(Subgroup.orderOf_coe _).symm.trans hg,hgo⟩
  obtain ⟨f,hf,ho,hor,hselected,hmax⟩ := d.unitaryFour_maximal_outer_centralizer h hH hp m hm hc hex
  let C := centralizer ({f.val} : Set G)
  let P := (T : Subgroup G) ⊓ C
  have hlocal (i : Fin 2) : Chapter1.IsSylowIn 2 P
      (normalizer (![L,residual H] i : Set G) ⊓ C) := by
    have hTM : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
      fin_cases i
      · exact h.sylow_normalizes
      · exact hH.1.1.2.trans (le_normalizer_residual H)
    apply Chapter1.isSylowIn_iff.mpr
    exact ⟨T.isPGroup'.to_le inf_le_left,inf_le_inf_right C hTM,
      fun U hU hPU hUM => hmax i U hU hPU (hUM.trans inf_le_right) (hUM.trans inf_le_left)⟩
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let U := (R : Subgroup C).map C.subtype
  have hPU : P ≤ U := by
    intro x hx
    exact mem_map_of_mem C.subtype (hR (show (⟨x,hx.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from hx.1))
  have hlt : P < U := lt_of_le_of_ne hPU (by
    intro heq
    have hh : Chapter1.IsSylowIn 2 P C := ⟨R,heq.symm⟩
    exact d.unitaryFour_outer_centralizer_not_sylow h hH hp m hm hc f hf ho hh)
  have hUp : IsPGroup 2 U := R.isPGroup'.map C.subtype
  let V := U ⊓ normalizer (P : Set G)
  have hVp : IsPGroup 2 V := hUp.to_le inf_le_left
  have hPV : P < V := by
    have hproper : P.subgroupOf U < ⊤ := by
      rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
      exact not_le_of_gt hlt
    let : Group.IsNilpotent U := hUp.isNilpotent
    obtain ⟨v,hv,hvn⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (P.subgroupOf U) hproper)
    have hvN : v.val ∈ normalizer (P : Set G) := by
      rw [←subgroupOf_normalizer_eq hPU] at hv
      exact hv
    refine lt_of_le_of_ne (le_inf hPU le_normalizer) ?_
    intro hh
    exact hvn (hh.symm ▸ (show v.val ∈ V from ⟨v.property,hvN⟩))
  have hVC : V ≤ C := inf_le_left.trans (map_subtype_le _)
  have hout (i : Fin 2) : ¬ V ≤ normalizer (![L,residual H] i : Set G) := by
    intro hh
    exact hPV.ne (hmax i V hVp hPV.le hVC hh).symm
  have hZ := d.unitaryFour_outer_derived_center_le_core h hH hp m hm hc f hf ho
  have hZN := d.unitaryFour_centralizer_derived_center h hH hp m hm hc f
  refine ⟨f,hf,ho,hor,hlocal,V,hVp,hPV,hVC,inf_le_right,hout,
    d.unitaryFour_outer_core_fixed_card_eq h hH hp m hm hc f hf ho,?_,
    d.unitaryFour_degreeTwo_maximal_derived_center_ne_bot h hH hp m hm he f hf ho hselected,
    hZ.2,hZ.1,inf_le_right.trans hZN.2⟩
  intro B hB hN
  exact d.unitaryFour_escaping_two_group_long_root h hH hp m hm hc V B hVp hB hN (hout 1)


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
