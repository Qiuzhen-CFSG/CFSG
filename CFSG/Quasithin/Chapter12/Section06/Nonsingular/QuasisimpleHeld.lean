module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleFixedLine
public import Theory.SpecificGroups.Held.CentralCovers.OddCenter
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner

/-!
# Excluding Held through the original fixed involution

The odd center of every quasisimple Held cover preserves the original fixed
involution of V_v. Its actual centralizer contains the perfect L_v image.
The small Held centralizer has order prime to nine. In the other class,
perfectness puts that image in the index-two quasisimple cover of PSL₃(4),
and full movement puts V_v there as well. Projection through its center
preserves three-rank two and a nontrivial moved two-subgroup. The actual
PSL₃(4) parabolic normalizer cover excludes this configuration.

The literal original V, its fixed space and both central projections are
retained. The final application removes M₂₄ and Held from the preferred-point
catalogue; HS, Ru and J₄ remain, with only J₄ in the small-Thompson subcase.
Earlier invariance and TI retain producer qt-d-1222-source and final discharge
owner qt-d-12634-source. This does not prove 12.6.2 or 12.6.23.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826; the central
cover conventions of I.1.1--3, p.407; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

private theorem held_local_obstruction (P W : Subgroup Held.He) [Group.IsPerfect P]
    [IsElementaryAbelian 2 W] (hr : 2 ≤ primeRank 3 P) (h9 : 9 ∣ Nat.card P)
    (hW : W ≠ ⊥) (hm : W = ⁅W,P⁆)
    (t : Held.He) (ht : orderOf t = 2) (htW : t ∈ W)
    (hP : P ≤ centralizer ({t} : Set Held.He)) : False := by
  let A := (MulAut.conj t).fixedSubgroup
  have hPA : P ≤ A := by simpa only [A,MulAut.fixedSubgroup_conj] using hP
  have hWA : W ≤ A := by
    dsimp only [A]
    rw [MulAut.fixedSubgroup_conj]
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨w,hw⟩ : W) ⟨t,htW⟩))
  let P₀ := P.subgroupOf A
  let W₀ := W.subgroupOf A
  let : Group.IsPerfect P₀ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPA).symm.toMonoidHom) (subgroupOfEquivOfLe hPA).symm.surjective
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.subgroupOf hWA
  have hm₀ : W₀ = ⁅W₀,P₀⁆ := by
    apply map_injective A.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hPA,map_subgroupOf_eq_of_le hWA]
    exact hm
  rcases Held.InvolutionFixedData.innerRowsWithQuotient t
      ((Held.InvolutionFixedData.orderOf_conj t).trans ht) with h | hc
  · obtain ⟨D,hDn,hDq,hi,hz,⟨e⟩⟩ := h
    let : D.Normal := hDn
    let : IsQuasisimple D := hDq
    have hPD : P₀ ≤ D := le_of_isPerfect_of_index_eq_two P₀ D hi
    have hWD : W₀ ≤ D := by
      rw [hm₀]
      exact (commutator_mono le_top hPD).trans (commutator_le_right _ _)
    let B := P₀.subgroupOf D
    let U := W₀.subgroupOf D
    let b : B ≃* P := (subgroupOfEquivOfLe hPD).trans (subgroupOfEquivOfLe hPA)
    let u : U ≃* W := (subgroupOfEquivOfLe hWD).trans (subgroupOfEquivOfLe hWA)
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := b.symm.toMonoidHom) b.symm.surjective
    have hU : U ≠ ⊥ := by
      intro hh
      have hc : Nat.card W = 1 := by rw [←Nat.card_congr u.toEquiv,hh,card_bot]
      exact hW ((Subgroup.card_eq_one).mp hc)
    have heU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective u.toMonoidHom u.injective
    have hmove : U = ⁅U,B⁆ := by
      apply map_injective D.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hPD,map_subgroupOf_eq_of_le hWD]
      exact hm₀
    let q := QuotientGroup.mk' (center D)
    obtain ⟨hperfect,hne,hele,_,hn⟩ := CentralQuotientLocalMarking.moved_image B U hU heU hmove
    let : Group.IsPerfect (B.map q) := hperfect
    let f := q.subgroupMap B
    have hk : Nat.card f.ker ∣ 4 := by
      let j : f.ker →* center D := {
        toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      have hj : Function.Injective j := by
        intro x y hh
        exact Subtype.ext (Subtype.ext (congrArg (fun a : center D => (a : D)) hh))
      rw [←hz]
      exact card_dvd_of_injective j hj
    have hrB : 2 ≤ primeRank 3 (B.map q) := by
      have he := primeRank_eq_of_surjective_of_coprime 3 f (q.subgroupMap_surjective B)
        ((by decide : Nat.Coprime 3 4).of_dvd_right hk)
      rw [←he,primeRank_equiv 3 b]
      exact hr
    let E := (U.map q).map e.toMonoidHom
    let R := (B.map q).map e.toMonoidHom
    let r := (B.map q).equivMapOfInjective e.toMonoidHom e.injective
    let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := r.toMonoidHom) r.surjective
    have hE : E ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
    have hEp : IsPGroup 2 E := by
      let := hele
      exact (IsElementaryAbelian.isPGroup 2 (U.map q)).map e.toMonoidHom
    have hN : R ≤ normalizer (E : Set Matrix.PSL3Four.PSL) :=
      (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
    obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le
      Matrix.PSL3Four.F (by decide : 0 < 2) Matrix.PSL3Four.card_F
      (normalizer (E : Set Matrix.PSL3Four.PSL)) ⟨E,hE,hEp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp R.subtype
    have hj : j.range ≤ (normalizer (E : Set Matrix.PSL3Four.PSL)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hN b.property)
    apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
      Matrix.PSL3Four.F (by decide : Odd 3) (by rwa [←primeRank_equiv 3 r])
      (by rw [Matrix.PSL3Four.card_F]) j ((MulAut.conj g).injective.comp R.subtype_injective)
    cases point with
    | false => exact .inr (hj.trans hg)
    | true => exact .inl (hj.trans hg)
  · have hd : 9 ∣ Nat.card A := by
      have hd := card_dvd_of_le hPA
      exact h9.trans hd
    rw [hc] at hd
    exact (by decide : ¬9 ∣ 21504) hd

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Held is excluded using the original fixed line and the genuine centralizer cover. -/
theorem SourceHypothesis.nonsingular_not_held_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Held.He) := by
  let C := Kv (v : G)
  let := hK
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (center C)
  let f := e.toMonoidHom.comp q
  let P := ((Lv L (v : G)).subgroupOf C).map q
  let W := ((Vv L V (v : G)).subgroupOf C).map q
  obtain ⟨hperfect,⟨eA⟩,hr,hne,hele,hm,hn⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : Group.IsPerfect P := hperfect
  let : IsElementaryAbelian 2 W := hele
  let P' := P.map e.toMonoidHom
  let W' := W.map e.toMonoidHom
  let p := P.equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsPerfect P' := Group.IsPerfect.ofSurjective (f := p.toMonoidHom) p.surjective
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map e.toMonoidHom
  have hr' : 2 ≤ primeRank 3 P' := by rwa [←primeRank_equiv 3 p]
  have h9 : 9 ∣ Nat.card P' := by
    rw [card_map_of_injective e.injective]
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 P))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hW' : W' ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have hm' : W' = ⁅W',P'⁆ := by dsimp only [W',P']; rw [←map_commutator,←hm]
  obtain ⟨z,hzW,hzne,_,hzfix,_⟩ := D.nonsingular_moved_fixed_line H.chosen v hv
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  let zC : C := ⟨z,hWC hzW⟩
  have hzorder : orderOf zC = 2 := orderOf_eq_prime
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property))
    (fun hh => hzne (Subtype.ext (congrArg (fun a : C => (a : G)) hh)))
  have hodd := Held.CentralCovers.odd_center ⟨e⟩
  have htne : f zC ≠ 1 := by
    intro ht
    have hzc : zC ∈ center C := (QuotientGroup.eq_one_iff _).mp
      (e.injective (ht.trans e.map_one.symm))
    have hd := orderOf_dvd_natCard (⟨zC,hzc⟩ : center C)
    rw [←Subgroup.orderOf_coe,hzorder] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  have ht : orderOf (f zC) = 2 := orderOf_eq_prime
    (by rw [←map_pow, (orderOf_eq_prime_iff.mp hzorder).1, map_one]) htne
  have htW : f zC ∈ W' := mem_map_of_mem e.toMonoidHom (mem_map_of_mem q hzW)
  have hPc : P' ≤ centralizer ({f zC} : Set Held.He) := by
    rintro _ ⟨y,⟨b,hb,rfl⟩,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f b * f zC = f zC * f b
    rw [←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    have hz : (z : G) ∈ ZV (Lv L (v : G)) (Vv L V (v : G)) := hzfix ▸ mem_zpowers (z : G)
    exact mem_centralizer_iff.mp hz.2 (b : G) hb
  exact held_local_obstruction P' W' hr' h9 hW' hm' (f zC) ht htW hPc

/-- Only HS, Ru and J₄ remain after the fixed-line centralizer exclusions. -/
theorem SourceHypothesis.nonsingular_quasisimple_models_after_held
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ∃ name : ClassificationModels.SporadicName,
      (name = .hs ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier) := by
  obtain ⟨name,hn,he⟩ := H.nonsingular_quasisimple_models_after_linear D v hv hK
  refine ⟨name,?_,he⟩
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact (H.nonsingular_not_mathieu24_centralQuotient D v hv hK he).elim
  · exact .inl rfl
  · exact (H.nonsingular_not_held_centralQuotient D v hv hK he).elim
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- The original small-Thompson subcase has only the J₄ central quotient left. -/
theorem SourceHypothesis.nonsingular_quasisimple_small_thompson_jankoFour
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (hK : IsQuasisimple (Kv (v : G))) :
    Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) := by
  obtain ⟨name,hn,he⟩ :=
    H.nonsingular_quasisimple_models_small_thompson_after_linear D v hv hTV hTv hJ hK
  rcases hn with rfl | rfl | rfl
  · exact (H.nonsingular_not_mathieu24_centralQuotient D v hv hK he).elim
  · exact (H.nonsingular_not_held_centralQuotient D v hv hK he).elim
  · exact he

/-- Apply both exclusions and the Ru kernel calculation at the literal preferred
escaping point. Earlier invariance and TI retain producer qt-d-1222-source
and final discharge owner qt-d-12634-source. -/
theorem SourceHypothesis.exists_preferred_nonsingular_models_after_held
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) →
        let C := (Kv (w : G)) ⧸ center (Kv (w : G))
        (∃ name : ClassificationModels.SporadicName,
          (name = .hs ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier)) ∧
        (Stellmacher.elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
          Nonempty (C ≃* Janko4.Model)) ∧
        (Nonempty (C ≃* Rudvalis.Model) →
          Nat.card (((Vv L V (w : G)).subgroupOf (Kv (w : G))).map
            (QuotientGroup.mk' (center (Kv (w : G))))) = 16)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,fun hK =>
    ⟨H.nonsingular_quasisimple_models_after_held D w hw hK,
      fun hJ => H.nonsingular_quasisimple_small_thompson_jankoFour D w hw hTV hs hJ hK,
      H.nonsingular_ru_moved_image_card D w hw⟩⟩

end CFSG.Quasithin.Chapter12.Section06
