module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsAction

/-!
# Endpoint labels in the nearby commutator

A single-pair flip and an element moving that branch have a commutator
which exchanges a sibling pair. The three-neighbor label product identifies
the next commutator with the center label. The actual track label four steps
from the center supplies the moving element at every distance-two pair.
An odd local six-point image supplies all the single-pair flips.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the commutator argument preceding (6.12.3), printed p.404.
-/

@[expose] public section
noncomputable section
open scoped commutatorElement
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
set_option maxRecDepth 4096 in
private theorem flip_comm : ∀ (z : Model) (j : Fin 3) (b : ZMod 2), z.right j ≠ j →
    coordinateHom ⁅singleFlip j, z⁆ (z.right j, b) = (z.right j, b+1) := by
  decide +kernel

namespace BranchFrame
variable {a : RankTwo.Vertex F} (f : BranchFrame F a)
theorem center_label_mem_commutator_of_singleFlip
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (ha : a.type = d.side) (r j : Fin 3) (bit : ZMod 2)
    (z : RankTwo.stabilizer F a)
    (hz : z.val ∈ d.labelBall (f.point (r,bit)) 2)
    (hmove : f.branchAction z j ≠ j) (hrj : r ≠ j)
    (hx : ∃ x : RankTwo.stabilizer F a, f.blockAction h x = singleFlip j) :
    d.label a ∈ ⁅d.labelBall a 2, d.labelBall (f.point (r,bit)) 2⁆ := by
  obtain ⟨x, hx⟩ := hx
  have hxsphere : f.sphereAction h x = coordinateHom (singleFlip j) := by
    rw [← f.blockAction_coordinates, hx]
  have hxb : x.val ∈ RankTwo.stabilizer F (f.point (r,bit)) := by
    change x.val • f.point (r,bit) = f.point (r,bit)
    rw [← f.sphereAction_eval h x, hxsphere]
    congr 1
    simp [coordinateHom, singleFlip, hrj]
  let k : RankTwo.stabilizer F a := ⁅x,z⁆
  have hk : k.val ∈ d.labelBall (f.point (r,bit)) 2 :=
    (le_normalizer_iff_commutator_le_right.mp
      (d.labelBall_normalized (f.point (r,bit)) 2))
      (commutator_mem_commutator hxb hz)
  let i := f.branchAction z j
  have he : f.sphereAction h k (i,0) = (i,1) := by
    rw [← f.blockAction_coordinates, show f.blockAction h k =
      ⁅singleFlip j, f.blockAction h z⁆ by dsimp [k]; rw [map_commutatorElement, hx]]
    exact flip_comm (f.blockAction h z) j 0 hmove
  have hkc : k.val • f.c i = f.d i := by
    have hh := f.sphereAction_eval h k (i,0)
    rw [he] at hh
    simpa [point] using hh.symm
  have hp := d.neighbor_product (f.e i).val a (f.c i) (f.d i)
    (f.e i).property.symm (f.c_adj i) (f.d_adj i)
    (f.c_ne_center i).symm (f.d_ne_center i).symm (f.c_ne_d i) ha
  have hc := (f.c_type h i).trans ha
  have hcomm : ⁅d.label (f.c i), k.val⁆ = d.label a := by
    have hconj := d.conjugate k.val (f.c i) hc
    rw [hkc] at hconj
    calc
      ⁅d.label (f.c i), k.val⁆ = d.label (f.c i) * d.label (f.d i) := by
        rw [commutatorElement_def, d.label_inv hc, hconj]
        group
      _ = d.label a := by
        have hh := congrArg (fun y => d.label a * y) hp
        simpa only [← mul_assoc, d.label_mul_self ha, one_mul, mul_one] using hh
  rw [← hcomm]
  exact commutator_mem_commutator (d.label_mem_labelBall hc (le_of_eq (f.c_dist h i))) hk
end BranchFrame

namespace CanonicalLabelSetup
/-- A single flip in each branch forces the endpoint label into the nearby
commutator. The element moving a branch is the actual track label four steps
from the transported center. -/
theorem label_mem_nearby_commutator_of_singleFlips
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side)
    (hab : (RankTwo.graph F).dist a b = 2) (f : BranchFrame F a)
    (hflip : ∀ j : Fin 3, ∃ x : RankTwo.stabilizer F a,
      f.blockAction h.action.toCubicTreeAction x = singleFlip j) :
    d.label a ∈ ⁅d.labelBall a 2, d.labelBall b 2⁆ := by
  obtain ⟨g, hga, hgb⟩ := h.exists_track_pair d (a := a) (b := b) ha (by have := h.five_le; omega)
  rw [hab] at hgb
  let v := g • d.track.vertex (d.center+4)
  have hv : v.type = d.side := by
    simpa only [v, CosetGeometry.smul_type, show (2:ℤ)*2=4 by norm_num] using d.shifted_type 2
  have hfixed (i : ℤ) (hi : d.center ≤ i ∧ i ≤ d.center+8) :
      d.label v • (g • d.track.vertex i) = g • d.track.vertex i := by
    have hh : d.label (d.track.vertex (d.center+4)) • d.track.vertex i = d.track.vertex i :=
      (d.shifted_fixed_iff 2 i).mpr (by rw [hr]; omega)
    rw [show d.label v = g * d.label (d.track.vertex (d.center+4)) * g⁻¹ from
      d.conjugate g _ (d.shifted_type 2)]
    simp only [mul_smul, inv_smul_smul, hh]
  let z : RankTwo.stabilizer F a := ⟨d.label v, by
    change d.label v • a = a
    rw [← hga]
    exact hfixed _ (by omega)⟩
  have hdbv : (RankTwo.graph F).dist b v = 2 := by
    rw [← hgb, RankTwo.dist_smul]
    apply (DistanceTwoGeometry.dist_eq_two_iff h.action.tree).mpr
    refine ⟨?_, d.track.vertex (d.center+3), ?_, ?_⟩
    · intro he
      have hh := d.track.injective he
      omega
    · simpa only [Nat.cast_ofNat, show d.center+2+1=d.center+3 by omega] using d.track.adjacent (d.center+2)
    · simpa only [show d.center+3+1=d.center+4 by omega] using d.track.adjacent (d.center+3)
  have hz : z.val ∈ d.labelBall b 2 :=
    d.label_mem_labelBall hv (le_of_eq hdbv)
  have hadj : (RankTwo.graph F).Adj a (g • d.track.vertex (d.center-1)) := by
    rw [← hga]
    apply (translationGraphIso F g).toHom.map_adj
    simpa only [sub_add_cancel] using (d.track.adjacent (d.center-1)).symm
  obtain ⟨j, hj⟩ := f.e.surjective ⟨_, hadj⟩
  have hj' : (f.e j).val = g • d.track.vertex (d.center-1) := congrArg Subtype.val hj
  have hmove : f.branchAction z j ≠ j := by
    intro he
    have hh := f.branchAction_eval z j
    rw [he, hj'] at hh
    have hfix : d.label (d.track.vertex (d.center+4)) • d.track.vertex (d.center-1) =
        d.track.vertex (d.center-1) := by
      apply (MulAction.toPerm g).injective
      have hconj := d.conjugate g (d.track.vertex (d.center+4)) (d.shifted_type 2)
      change g • (d.label (d.track.vertex (d.center+4)) • d.track.vertex (d.center-1)) =
        g • d.track.vertex (d.center-1)
      simpa only [z, v, hconj, mul_smul, inv_smul_smul] using hh.symm
    have hh' := (d.shifted_fixed_iff 2 (d.center-1)).mp hfix
    rw [hr] at hh'
    omega
  obtain ⟨p, hp⟩ := (f.sphereEquiv h.action.toCubicTreeAction).surjective ⟨b, hab⟩
  have hp' : f.point p = b := congrArg Subtype.val hp
  have hzp : f.sphereAction h.action.toCubicTreeAction z p = p := by
    apply f.point_injective h.action.toCubicTreeAction
    rw [f.sphereAction_eval, hp']
    change d.label v • b = b
    rw [← hgb]
    exact hfixed _ (by omega)
  have hfixbranch : f.branchAction z p.1 = p.1 := by
    rw [← f.sphereAction_block h.action.toCubicTreeAction z p, hzp]
  have hrj : p.1 ≠ j := by
    intro he
    rw [he] at hfixbranch
    exact hmove hfixbranch
  have hh := f.center_label_mem_commutator_of_singleFlip d h.action.toCubicTreeAction
    ha p.1 j p.2 z (by simpa only [hp'] using hz) hmove hrj (hflip j)
  simpa only [hp'] using hh
end CanonicalLabelSetup


namespace CanonicalLabelSetup
/-- The literal odd six-point action supplies the single-pair flips needed
for the endpoint-label commutator calculation. -/
theorem label_mem_nearby_commutator_of_not_even
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side)
    (hab : (RankTwo.graph F).dist a b = 2) (f : BranchFrame F a)
    (hne : ¬ (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel) :
    d.label a ∈ ⁅d.labelBall a 2, d.labelBall b 2⁆ := by
  apply d.label_mem_nearby_commutator_of_singleFlips h hr ha hab f
  exact f.exists_singleFlip_of_not_even h d hr ha hne
end CanonicalLabelSetup

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
