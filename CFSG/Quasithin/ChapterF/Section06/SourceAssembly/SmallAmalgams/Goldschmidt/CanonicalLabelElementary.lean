module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelNeighborhood
public import Mathlib.GroupTheory.Schreier

/-!
# The radius-two canonical label group

Labels in these balls commute and have order two. The three-branch product
relation expresses each second forward label using the center and the first
forward label. Thus four labels generate, and the group has order at most
sixteen. These are the literal label groups in the commutator argument
preceding Goldschmidt (6.12.3), printed pp.403–404.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem CanonicalLabelSetup.labelBall_elementary (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (v : RankTwo.Vertex F) (r : ℕ)
    (hr : 2*r ≤ d.radius + 1) (hs : 2*r ≤ s) :
    IsElementaryAbelian 2 (d.labelBall v r) := by
  let : IsMulCommutative (Subgroup.closure
      (d.label '' {w | w.type = d.side ∧ (RankTwo.graph F).dist v w ≤ r})) := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨a, ⟨ha, hva⟩, rfl⟩ _ ⟨b, ⟨hb, hvb⟩, rfl⟩
    have hd : (RankTwo.graph F).dist a b ≤ 2*r := by
      calc
        (RankTwo.graph F).dist a b ≤
            (RankTwo.graph F).dist a v + (RankTwo.graph F).dist v b :=
          h.tree.connected.dist_triangle
        _ ≤ r+r := add_le_add (by simpa only [SimpleGraph.dist_comm] using hva) hvb
        _ = 2*r := by omega
    exact (d.labels_commute_of_dist_le ha hb (hd.trans hr) (hd.trans hs)).eq)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨a, ⟨ha, _⟩, rfl⟩
  simpa only [d.order_two a ha] using pow_orderOf_eq_one (d.label a)

namespace BranchFrame
variable {a : RankTwo.Vertex F} (f : BranchFrame F a)

theorem c_type (h : CubicTreeAction F) (i : Fin 3) : (f.c i).type = a.type := by
  apply ((RankTwo.even_dist_iff F h.generated a (f.c i)).mp ?_).symm
  rw [f.c_dist h i]
  decide

theorem d_type (h : CubicTreeAction F) (i : Fin 3) : (f.d i).type = a.type := by
  apply ((RankTwo.even_dist_iff F h.generated a (f.d i)).mp ?_).symm
  rw [f.d_dist h i]
  decide

/-- The center and one forward label in each branch generate the radius-two group. -/
theorem radiusTwo_generators (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (ha : a.type = d.side) :
    d.labelBall a 2 = Subgroup.closure
      (Set.range (Fin.cases (d.label a) (fun i : Fin 3 => d.label (f.c i)))) := by
  let u : Fin 4 → G := Fin.cases (d.label a) (fun i : Fin 3 => d.label (f.c i))
  change d.labelBall a 2 = Subgroup.closure (Set.range u)
  have hcenter : d.label a ∈ Subgroup.closure (Set.range u) := subset_closure ⟨0, rfl⟩
  have hc (i : Fin 3) : d.label (f.c i) ∈ Subgroup.closure (Set.range u) :=
    subset_closure ⟨i.succ, rfl⟩
  have hd (i : Fin 3) : d.label (f.d i) ∈ Subgroup.closure (Set.range u) := by
    have hp := d.neighbor_product (f.e i).val a (f.c i) (f.d i)
      (show (RankTwo.graph F).Adj a (f.e i).val from (f.e i).property).symm
      (f.c_adj i) (f.d_adj i) (f.c_ne_center i).symm (f.d_ne_center i).symm
      (f.c_ne_d i) ha
    have he : d.label (f.d i) = (d.label a * d.label (f.c i))⁻¹ :=
      (inv_eq_of_mul_eq_one_right hp).symm
    rw [he]
    exact inv_mem (mul_mem hcenter (hc i))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨w, ⟨hw, hw2⟩, rfl⟩
    rcases f.radiusTwo_cases h (hw.trans ha.symm) hw2 with rfl | ⟨i, rfl | rfl⟩
    · exact hcenter
    · exact hc i
    · exact hd i
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact d.label_mem_labelBall ha (by simp)
    | succ i =>
      exact d.label_mem_labelBall ((f.c_type h i).trans ha) (le_of_eq (f.c_dist h i))

end BranchFrame

/-- The bound used in the commutator argument preceding Goldschmidt (6.12.3). -/
theorem CanonicalLabelSetup.radiusTwo_card_le (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hr : 3 ≤ d.radius) (hs : 4 ≤ s)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    IsElementaryAbelian 2 (d.labelBall a 2) ∧ Nat.card (d.labelBall a 2) ≤ 16 := by
  classical
  let : IsElementaryAbelian 2 (d.labelBall a 2) :=
    d.labelBall_elementary h a 2 (by omega) hs
  refine ⟨inferInstance, ?_⟩
  let : Finite (RankTwo.stabilizer F a) := h.finite_stabilizer a
  let : Finite (d.labelBall a 2) := Finite.of_injective
    (Subgroup.inclusion (d.labelBall_le_stabilizer a 2 (by omega) (by omega)))
    (Subgroup.inclusion_injective _)
  obtain ⟨f⟩ := h.exists_branchFrame a
  let u : Fin 4 → G := Fin.cases (d.label a) (fun i : Fin 3 => d.label (f.c i))
  have hgen : d.labelBall a 2 = Subgroup.closure (Set.range u) := f.radiusTwo_generators d h ha
  have hrank : Group.rank (d.labelBall a 2) ≤ 4 := by
    calc
      Group.rank (d.labelBall a 2) = Group.rank (Subgroup.closure (Set.range u)) :=
        Subgroup.rank_congr hgen
      _ ≤ Nat.card (Set.range u) := Subgroup.rank_closure_finite_le_nat_card _
      _ ≤ Nat.card (Fin 4) := Finite.card_range_le u
      _ = 4 := Nat.card_fin 4
  have hcard : Nat.card (d.labelBall a 2) ∣ 2 ^ Group.rank (d.labelBall a 2) :=
    card_dvd_exponent_pow_rank' _
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (d.labelBall a 2)))
  exact (Nat.le_of_dvd (by positivity) hcard).trans (pow_le_pow_right' (by decide) hrank)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
