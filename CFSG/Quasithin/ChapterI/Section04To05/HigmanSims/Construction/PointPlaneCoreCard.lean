module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# Exact point-core centralizers of another seed point

A distinct seed involution is noncentral in the original point core,
whose center is cyclic of order four. Its commutator homomorphism has
nontrivial image in the marked involution line. The image has order two,
so its literal centralizer in the point core has order thirty-two.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The original point core meets the full centralizer of a distinct seed
point in order thirty-two. -/
theorem TypeAt.point_core_other_point_centralizer_card (h : TypeAt z V)
    (v : G) (hv : v ∈ V) (hv1 : v ≠ 1) (hvz : v ≠ z) :
    Nat.card ((involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer v :
      Subgroup G) = 32 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 H).map H.subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  let zQ : Q := ⟨z, hVQ h.involution_mem_seed⟩
  let vQ : Q := ⟨v, hVQ hv⟩
  have hzC : zQ ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (map_subtype_le (pCore 2 H) q.property))
  have hline : (zpowers z).subgroupOf Q ≤ center Q := by
    intro q hq
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hq
    have he : q = zQ ^ n := Subtype.ext hn.symm
    rw [he]
    exact (center Q).zpow_mem hzC n
  have hclass : _root_.commutator Q ≤ center Q := by
    apply commutator_le.mpr
    intro a _ b _
    apply hline
    exact h.point_core_commutator_mem a b a.property b.property
  have hshape : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  have hvC : vQ ∉ center Q := by
    intro hh
    obtain ⟨e⟩ := hshape.center_model
    let : IsCyclic (center Q) := e.isCyclic.mpr inferInstance
    have he := IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨vQ, hh⟩ : center Q)) (y := (⟨zQ, hzC⟩ : center Q))
      (by simpa only [← orderOf_coe] using (h.at_seed_point v hv hv1).involution)
      (by simpa only [← orderOf_coe] using h.involution)
    exact hvz (congrArg (fun x : center Q => (x.val : G)) he)
  let f := ClassTwo.commutatorHom hclass vQ
  have hr : f.range.map Q.subtype ≤ zpowers z := by
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact h.point_core_commutator_mem v q (hVQ hv) q.property
  have hrle : Nat.card f.range ≤ 2 := by
    have hh := card_le_of_le hr
    rw [card_map_of_injective Q.subtype_injective, Nat.card_zpowers, h.involution] at hh
    exact hh
  have hrne : Nat.card f.range ≠ 1 := by
    intro hh
    have hf : f.range = ⊥ := card_eq_one.mp hh
    have he : f.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr
      (MonoidHom.range_eq_bot_iff.mp hf)
    rw [ClassTwo.commutatorHom_ker] at he
    apply hvC
    apply mem_center_iff.mpr
    intro q
    have hq : q ∈ centralizer ({vQ} : Set Q) := he.symm ▸ mem_top q
    exact mem_centralizer_singleton_iff.mp hq
  have hrc : Nat.card f.range = 2 := by
    have hp := Nat.card_pos (α := f.range)
    omega
  have hkc : Nat.card (centralizer ({vQ} : Set Q)) = 32 := by
    have hh := f.ker.card_mul_index
    rw [index_ker, hrc, ClassTwo.commutatorHom_ker, hshape.card] at hh
    omega
  have hmap : (centralizer ({vQ} : Set Q)).map Q.subtype = Q ⊓ involutionCentralizer v := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hq))⟩
    · rintro ⟨hx, hvx⟩
      exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hvx)), rfl⟩
  rw [← hmap, card_map_of_injective Q.subtype_injective]
  exact hkc

end CFSG.Quasithin.HigmanSims
