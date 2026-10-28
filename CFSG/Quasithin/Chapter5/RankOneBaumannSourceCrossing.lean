module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceAction
public import Theory.Frattini.Intersection
public import Theory.Frattini.CentralElementarySupplement
public import Theory.Representation.BinaryPermutation.FivePointCrossing
public import Theory.GroupTheory.CrossingPairCentralizer
import Mathlib.Tactic
/-!
# Crossing and elementary cores on the original rank-one input

Two disjoint moving actors on the five-point core contradict the point-centralizer
control from earlier uniqueness over L. Thus C_S(L) lies in the escaping conjugate
core. The product Q=[W,L] C_S(L) then makes the Frattini subgroup invariant under
the escaping conjugator; uniqueness over LT forces that subgroup to be trivial.
All subgroups and conjugations are those of the original Input.

The point-centralizer premise is still explicit. Its source 4.3.2 discharge
belongs to qt-d-1222-rankone-global-uniqueness, at the original Input scope.
Source: Aschbacher--Smith 5.1.7(1), p.633.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Input
open ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W₀ : Subgroup G} {n : ℕ}
  (d : Input KnownSimple.IsKnownSimple T L W₀ n)
local notation "V" => (⁅W₀,L⁆ : Subgroup G)
include d
theorem baumann_core_elementary_of_crossing
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : g ∉ normalizer (L : Set G))
    (hcross : baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom) :
    IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (L : Set G)
  let W := (frattini D).map D.subtype
  let e := MulAut.conj g⁻¹
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 _
  have hQD : Q = V ⊔ D := baumann_core_product_of_escape d hout
  have hVQ : V ≤ centralizer (Q : Set G) := by
    obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
      (inf_le_left.trans d.sylow_normalizes)
    apply le_centralizer_iff.mp
    rw [←hV]
    exact he.ge.trans inf_le_right
  have hphi : (frattini Q).map Q.subtype = W :=
    frattini_map_eq_of_central_elementary_supplement Q D V hQ d.commutator_reduced.2.1 hVQ hQD
  have hle : W ≤ W.map e.toMonoidHom := by
    have hi := frattini_image_le_of_le hcross (hQ.map e.toMonoidHom)
    rw [frattini_image_map _ e.toMonoidHom e.injective,hphi] at hi
    exact hi
  have he : W.map e.toMonoidHom = W := eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective e.injective]) |>.symm
  have hWD : W ≤ D := map_subtype_le _
  have hWT : W ≤ (T : Subgroup G) := hWD.trans (inf_le_left.trans inf_le_left)
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    have hS := (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
    exact (le_inf hS (d.sylow_normalizes.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLN : L ≤ normalizer (W : Set G) :=
    ((le_centralizer_iff.mp (hWD.trans inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hWN : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hLN
      (hTN.trans (normalizer_le_normalizer_characteristic_image D (frattini D))))
  have hW : W = ⊥ := by
    by_contra hne
    have hN := normalizer_of_local_normal d W hne hWT hWN
    have hgm : g⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    apply hg
    simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem (hN hgm)
  have hbot : frattini Q = ⊥ := (map_eq_bot_iff_of_injective _ Q.subtype_injective).mp
    (hphi.trans hW)
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (R := Q) (p := 2)).mp hbot
omit [Group G] [Finite G] d in
private theorem D_words (p : Equiv.Perm (Fin 5)) (hp : p ∈ Offenders.D 5) :
    p=1 ∨ p=Equiv.swap 0 1 ∨ p=Equiv.swap 2 3 ∨ p=Equiv.swap 0 1 * Equiv.swap 2 3 := by
  let F : Subgroup (Equiv.Perm (Fin 5)) := {
    carrier := {p | p=1 ∨ p=Equiv.swap 0 1 ∨ p=Equiv.swap 2 3 ∨ p=Equiv.swap 0 1 * Equiv.swap 2 3}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro a b ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
    inv_mem' := by
      intro a ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel }
  have hD : Offenders.D 5 ≤ F := by
    apply (closure_le _).mpr
    rintro p ⟨i,_,rfl⟩
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact hD hp

/-- The centralizing factor lies in the actual conjugate core. The only
independent source input is the 4.3.2 centralizer control over L. -/
theorem baumann_crossing_of_point_centralizers
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G))
    (hmove : ¬(V).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (L ⊔ baumann (T : Subgroup G)).pCoreIn 2) :
    baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let U := (V).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  have hVL : V ≤ L := hV ▸ map_subtype_le _
  have hVQ : V ≤ Q := by
    rw [show Q = V ⊔ C from baumann_core_product_of_escape d hout]
    exact le_sup_left
  have hVS : V ≤ S := hVQ.trans (baumann_core_le_of_escape d hout)
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans d.sylow_normalizes
  have hSV : S ≤ normalizer (V : Set G) := inf_le_left.trans d.moved_sylow_normalizes
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_inf S.le_normalizer (hSL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hUS : U ≤ S := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hVS
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp ((normalizer (S:Set G)).inv_mem hg))
  have hQ : Q = S ⊓ centralizer (V : Set G) := baumann_core_centralizer_of_escape d hout
  have hQg : S ⊓ centralizer (U : Set G) = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hQ]
    exact CrossingPair.sylow_centralizer_crossing V S g hg
  obtain ⟨N,hSN,q,m,hq,hm,hr,he,himage⟩ := exists_conjugate_baumann_action_marking d hout g hg
  have hVN : V ≤ N := hVS.trans hSN
  have hCN : C ≤ N := inf_le_left.trans hSN
  change m.range = U at hr
  have hfix (n : N) (hn : q n = 1) :
      (n:G) ∈ centralizer (U : Set G) := by
    intro x hx
    obtain ⟨y,rfl⟩ := hr.symm ▸ hx
    have hh := he n y.toAdd
    rw [hn,map_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hwords (n : N) (hn : (n:G) ∈ S) (hne : q n ≠ 1) :
      q n=Equiv.swap 0 1 ∨ q n=Equiv.swap 2 3 ∨ q n=Equiv.swap 0 1 * Equiv.swap 2 3 :=
    (D_words (q n) (himage ▸ mem_map_of_mem q hn)).resolve_left hne
  have hvMove : ¬V ≤ centralizer (U : Set G) := by
    intro hh
    apply hmove
    change U ≤ Q
    rw [hQ]
    exact le_inf hUS (le_centralizer_iff.mp hh)
  obtain ⟨b,hbV,hbn⟩ := Set.not_subset.mp hvMove
  let b' : N := ⟨b,hVN hbV⟩
  have hbq : q b' ≠ 1 := fun hh => hbn (hfix b' hh)
  apply le_trans ?_ hQg.le
  apply le_inf inf_le_left
  intro a ha
  by_contra han
  let a' : N := ⟨a,hCN ha⟩
  have haq : q a' ≠ 1 := fun hh => han (hfix a' hh)
  have hMC : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [←hV]
    exact normalizer_le_normalizer_characteristic_image L (blockU L)
  refine BinaryPermutation.FivePointCore.no_disjoint_moving_actors
    (N) q hq m hm he C V ?_ ?_
    (baumann_core_disjoint_of_escape d hout).symm
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hVL))) ?_ hVN
    (fun x hx hn => (hc x hx hn).trans hMC)
    a' b' ha hbV (hwords a' ha.1 haq) (hwords b' (hVS hbV) hbq)
  · rw [hr]
    exact le_normalizer_iff_commutator_le_left.mp (hUS.trans hSC)
  · rw [hr]
    exact le_normalizer_iff_commutator_le_left.mp (hUS.trans hSV)
  · let := d.commutator_reduced.2.1
    exact IsElementaryAbelian.isPGroup 2 V

/-- C.6.3 and the actual point-centralizer control supply both the escaping
conjugate and the elementary two-core needed by the next source paragraph. -/
theorem exists_baumann_elementary_conjugate_core
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬(V).map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ∧
      baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom ∧
      IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) := by
  obtain ⟨g,hg,hn,hm⟩ := exists_baumann_conjugate_core_escape d hout
  have hcross := baumann_crossing_of_point_centralizers d hout hc g hg hm
  exact ⟨g,hg,hn,hm,hcross,baumann_core_elementary_of_crossing d hout g hn hcross⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Input
