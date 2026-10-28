module
public import CFSG.Quasithin.Chapter5.A5Source.BaumannAction
public import CFSG.Quasithin.Chapter5.A5Source.Frattini
public import Theory.Representation.BinaryPermutation.FivePointCrossing
public import Theory.GroupTheory.CrossingPairCentralizer
public import Mathlib.Tactic
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

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

/-- The actual block module is disjoint from the centralizing factor. -/
theorem baumann_core_disjoint_of_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    Disjoint V (baumann (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  have hz : blockU L ⊓ center L = ⊥ := by
    rw [←blockFixed_map,hb.blockFixed_eq_bot,Subgroup.map_bot]
  rw [disjoint_def]
  intro x hx hc
  rw [←hV] at hx
  obtain ⟨u,hu,rfl⟩ := hx
  have huZ : u ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc.2 l l.property)
  exact congrArg Subtype.val (show u=1 from hz.le ⟨hu,huZ⟩)

/-- The source Q is the literal Baumann centralizer of V. -/
theorem baumann_core_centralizer_of_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 =
      baumann (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  have he := ReducedMarking.normal_short_extension_centralizer L (baumann (T : Subgroup G)) hb.2.1
    (T.isPGroup'.to_le (show baumann (T : Subgroup G) ≤ (T : Subgroup G) from inf_le_left))
    (inf_le_left.trans d.normalizes_L)
  change (L ⊔ baumann (T : Subgroup G)) ⊓ centralizer ((blockU L).map L.subtype : Set G) = _ at he
  rw [hV] at he
  exact le_antisymm
    (le_inf (baumann_core_le_of_escape d hout) (he.ge.trans inf_le_right))
    ((inf_le_inf le_sup_right le_rfl).trans he.le)

/-- The centralizing factor lies in the actual conjugate core. The only
independent source input is the 4.3.2 centralizer control over L. -/
theorem baumann_crossing_of_point_centralizers
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G))
    (hmove : ¬V.map (MulAut.conj g⁻¹).toMonoidHom ≤
      (L ⊔ baumann (T : Subgroup G)).pCoreIn 2) :
    baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let U := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
    fun hh => hout (baumann_normalizer_of_thompson_centralizes d hh)
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  have hVL : V ≤ L := hV ▸ map_subtype_le _
  have hVQ : V ≤ Q := by
    rw [show Q = V ⊔ C from baumann_core_product_of_escape d hout]
    exact le_sup_left
  have hVS : V ≤ S := hVQ.trans (baumann_core_le_of_escape d hout)
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans d.normalizes_L
  have hSV : S ≤ normalizer (V : Set G) := inf_le_left.trans d.flag.T_normalizes
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
  have hSN : S ≤ normalizer (U : Set G) := CrossingPair.sylow_normalizes_crossing V S g hSV hg
  have hVN : V ≤ normalizer (U : Set G) := hVS.trans hSN
  have hCN : C ≤ normalizer (U : Set G) := inf_le_left.trans hSN
  obtain ⟨q,m,hq,hm,hr,he,himage⟩ := exists_conjugate_baumann_action_marking d hJ g hg
  change m.range = U at hr
  have hfix (n : normalizer (U : Set G)) (hn : q n = 1) :
      (n:G) ∈ centralizer (U : Set G) := by
    intro x hx
    obtain ⟨y,rfl⟩ := hr.symm ▸ hx
    have hh := he n y.toAdd
    rw [hn,map_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hwords (n : normalizer (U : Set G)) (hn : (n:G) ∈ S) (hne : q n ≠ 1) :
      q n=Equiv.swap 0 1 ∨ q n=Equiv.swap 2 3 ∨ q n=Equiv.swap 0 1 * Equiv.swap 2 3 :=
    (D_words (q n) (himage ▸ mem_map_of_mem q hn)).resolve_left hne
  have hvMove : ¬V ≤ centralizer (U : Set G) := by
    intro hh
    apply hmove
    change U ≤ Q
    rw [hQ]
    exact le_inf hUS (le_centralizer_iff.mp hh)
  obtain ⟨b,hbV,hbn⟩ := Set.not_subset.mp hvMove
  let b' : normalizer (U : Set G) := ⟨b,hVN hbV⟩
  have hbq : q b' ≠ 1 := fun hh => hbn (hfix b' hh)
  apply le_trans ?_ hQg.le
  apply le_inf inf_le_left
  intro a ha
  by_contra han
  let a' : normalizer (U : Set G) := ⟨a,hCN ha⟩
  have haq : q a' ≠ 1 := fun hh => han (hfix a' hh)
  have hMC : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [←hV]
    exact normalizer_le_normalizer_characteristic_image L (blockU L)
  refine BinaryPermutation.FivePointCore.no_disjoint_moving_actors
    (normalizer (U : Set G)) q hq m hm he C V ?_ ?_
    (baumann_core_disjoint_of_escape d hout).symm
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hVL))) ?_ hVN
    (fun x hx hn => (hc x hx hn).trans hMC)
    a' b' ha hbV (hwords a' ha.1 haq) (hwords b' (hVS hbV) hbq)
  · rw [hr]
    exact le_normalizer_iff_commutator_le_left.mp (hUS.trans hSC)
  · rw [hr]
    exact le_normalizer_iff_commutator_le_left.mp (hUS.trans hSV)
  · let := d.elementary
    exact IsElementaryAbelian.isPGroup 2 V

/-- C.6.3 and the actual point-centralizer control supply both the escaping
conjugate and the elementary two-core needed by the next source paragraph. -/
theorem exists_baumann_elementary_conjugate_core
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬V.map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ∧
      baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom ∧
      IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) := by
  obtain ⟨g,hg,hn,hm⟩ := exists_baumann_conjugate_core_escape d hout
  have hcross := baumann_crossing_of_point_centralizers d hout hc g hg hm
  exact ⟨g,hg,hn,hm,hcross,baumann_core_elementary_of_crossing d hout g hn hcross⟩
end CFSG.Quasithin.Chapter5.A5Source
