module

public import Stellmacher.Recognition.NormalEightSeparatedCentralizerData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightData
public import Theory.GroupTheory.PGroup.IndexTwoElementarySixteen
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightActionCore
public import Stellmacher.MainDefs
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.SolvableSixteenFixedPointAction

/-!
# Excluding the order-sixteen separated closure

The local normal closure is transported from the chosen supplement to the
original Sylow subgroup. It is elementary, has unchanged order, and is
normalized by the involution centralizer, which has index two in the Sylow.
The elementary bound and a centralizer action bound then produce a normal
elementary eight, contrary to the supplied normal-eight obstruction.

The supplement acts with trivial two-core on the closure and fixes the
noncentral involution. Solvability and the fixed-point automizer bound make
the Sylow action have order at most two. Its kernel is precisely the
centralizer used in the normal-core obstruction, completing the exclusion.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, pp.387–388,
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.NormalEightSeparatedCentralizers
open NormalEightSeparatedClosureEight
variable {G : Type*} [Group G] [Finite G]

/-- A centralizer action of order at most two rules out the elementary-sixteen
closure. The action bound remains an explicit premise to be discharged. -/
public theorem CentralizerSetup.closure_card_ne_sixteen_of_centralizer_index_le_two
    {S : Sylow 2 G} {W : Subgroup S} [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) {i : S} (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (d : CentralizerSetup S W i)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hbound : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16)
    (hindex : Nat.card d.closure = 16 →
      (centralizer (closureInSylow d : Set S)).relIndex (centralizer ({i} : Set S)) ≤ 2) :
    Nat.card d.closure ≠ 16 := by
  intro hc
  let : IsElementaryAbelian 2 (closureInSylow d) := closureInSylow_elementary d
  exact hno (exists_normal_elementary_eight_of_sixteen_of_centralizer_index_le_two
    (centralizer ({i} : Set S)) (closureInSylow d)
    (centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC)
    (closureInSylow_le_centralizer d) (centralizer_le_normalizer_closureInSylow d)
    ((card_closureInSylow d).trans hc) hbound (hindex hc))

/-- In the order-sixteen case, the involution centralizer acts on the closure
with image of order at most two. -/
public theorem CentralizerSetup.closure_centralizer_index_le_two_of_card_sixteen (hN : IsNTwoGroup G)
    {S : Sylow 2 G} {W : Subgroup S} [IsElementaryAbelian 2 W]
    {i : S} (hiW : i ∈ W) (hi : orderOf i = 2)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 16) :
    (centralizer (closureInSylow d : Set S)).relIndex
      (centralizer ({i} : Set S)) ≤ 2 := by
  let C := centralizer ({(i : G)} : Set G)
  let U := (W.map (S : Subgroup G).subtype).subgroupOf C
  let iC : C := ⟨i, mem_centralizer_singleton_iff.mpr rfl⟩
  have hiU : iC ∈ U := mem_map_of_mem _ hiW
  let iH : d.H := ⟨iC, d.four_le hiU⟩
  let v : d.closure := ⟨iH, le_normalClosure hiU⟩
  have hv : v ≠ 1 := by
    intro he
    have hi1 : i = 1 := Subtype.ext (congrArg (fun x : d.closure => (x : G)) he)
    simp [hi1] at hi
  let : Group.IsSolvable C :=
    hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer ((orderOf_coe i).trans hi))
  let : Group.IsSolvable d.H := inferInstance
  let : IsElementaryAbelian 2 d.closure := d.elementary
  let f : d.H →* MulAut d.closure := MulAut.conjNormal
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hfix : ∀ a : f.range, (a : MulAut d.closure) v = v := by
    rintro ⟨_, h, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (h : G) * (i : G) * (h : G)⁻¹ = (i : G)
    rw [mem_centralizer_singleton_iff.mp h.val.property, mul_inv_cancel_right]
  let P := d.T.subtype d.sylow_le
  let Q := P.mapSurjective f.rangeRestrict_surjective
  have hQ : Nat.card Q ≤ 2 :=
    sylow_card_le_two_of_solvable_sixteen_fixed_point d.closure hc f.range
      (closure_action_twoCore_eq_bot d) v hv hfix Q
  let T := centralizer ({i} : Set S)
  let g : T →* d.H :=
    { toFun := fun t =>
        ⟨⟨(t : S), mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp t.property))⟩, by
          apply d.sylow_le
          rw [d.sylow_eq]
          exact t.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let a := f.rangeRestrict.comp g
  have ha : a.range ≤ (Q : Subgroup f.range) := by
    rintro _ ⟨t, rfl⟩
    apply mem_map_of_mem
    change (g t : C) ∈ (d.T : Subgroup C)
    rw [d.sylow_eq]
    exact t.val.property
  have hk : a.ker = (centralizer (closureInSylow d : Set S)).subgroupOf T := by
    ext t
    change a t = 1 ↔ ∀ x ∈ closureInSylow d, x * (t : S) = (t : S) * x
    constructor
    · intro ht x hx
      obtain ⟨xC, ⟨xH, hxH, rfl⟩, he⟩ := hx
      have hh := congrArg (fun b : f.range => ((b : MulAut d.closure) ⟨xH, hxH⟩ : G)) ht
      change (t : G) * (xH : G) * (t : G)⁻¹ = (xH : G) at hh
      apply Subtype.ext
      change (x : G) * (t : G) = (t : G) * (x : G)
      change (xH : G) = (x : G) at he
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro ht
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hxS : (x : G) ∈ (S : Subgroup G) :=
        closureImage_le_sylow d (mem_map_of_mem _ (mem_map_of_mem _ x.property))
      have hx : (⟨(x : G), hxS⟩ : S) ∈ closureInSylow d :=
        mem_map_of_mem _ (mem_map_of_mem _ x.property)
      have hh := congrArg Subtype.val (ht ⟨(x : G), hxS⟩ hx)
      change (x : G) * (t : G) = (t : G) * (x : G) at hh
      change (t : G) * (x : G) * (t : G)⁻¹ = (x : G)
      rw [← hh, mul_inv_cancel_right]
  calc
    _ = a.ker.index := congrArg Subgroup.index hk.symm
    _ = Nat.card a.range := index_ker a
    _ ≤ Nat.card Q := card_le_of_le ha
    _ ≤ 2 := hQ

/-- The elementary normal closure in a separated centralizer setup cannot
have order sixteen. The elementary-order bound and absence of normal
elementary eights are retained explicitly for the final factorization. -/
public theorem CentralizerSetup.closure_card_ne_sixteen
    (hN : IsNTwoGroup G)
    {S : Sylow 2 G} {W : Subgroup S} [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) {i : S} (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S) (d : CentralizerSetup S W i)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hbound : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16) :
    Nat.card d.closure ≠ 16 := by
  exact d.closure_card_ne_sixteen_of_centralizer_index_le_two
    hW z hzW hzC hz hiW hi hiC hno hbound
    (fun hc => d.closure_centralizer_index_le_two_of_card_sixteen hN hiW hi hc)

end Stellmacher.Recognition.NormalEightSeparatedCentralizers
