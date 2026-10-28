module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreTransitivity

/-!
# Line kernels and the original point-pair stabilizers

All point-core kernels on incident lines have the same order, by actual
conjugation in G₀. Distinct lines give distinct kernels, hence neither
kernel is contained in the other. Thus the kernel on one line exchanges
the two other points of every different incident line.

The point core also adjusts any element of G₀₁ to fix a chosen second
point of the base line. These are precisely the action and stabilizer
factorization used in I.5.9's four-step geodesic argument (pp.421–422).
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def pointLineKernel (l : S.Line) : Subgroup G :=
  S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l}

theorem pointLineKernel_card {l : S.Line} (hl : S.Inc S.basePoint l) :
    Nat.card (S.pointLineKernel l) = Nat.card (S.Q 0 ⊓ S.Q 1 : Subgroup G) := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hh : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hc := S.point_line_kernel_conjugate S.baseLine ha
  rw [hh, S.point_core_line_kernel] at hc
  change Nat.card (S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l} : Subgroup G) = _
  rw [← hc]
  exact card_map_of_injective (MulAut.conj a).injective

theorem pointLineKernel_not_le {l m : S.Line}
    (hl : S.Inc S.basePoint l) (hm : S.Inc S.basePoint m) (hne : l ≠ m) :
    ¬ S.pointLineKernel l ≤ S.pointLineKernel m := by
  intro hle
  let : Finite (S.Q 0) := Finite.of_injective
    (inclusion ((S.family 0).pCoreIn_le 2)) (inclusion_injective _)
  let : Finite (S.pointLineKernel m) := Finite.of_injective
    (inclusion (show S.pointLineKernel m ≤ S.Q 0 from inf_le_left)) (inclusion_injective _)
  have he := eq_of_le_of_card_ge hle ((S.pointLineKernel_card hm).trans
    (S.pointLineKernel_card hl).symm).le
  exact hne (S.point_line_kernel_separation l m hl hm he)

theorem pointLineKernel_otherLine_transitive {l m : S.Line}
    (hl : S.Inc S.basePoint l) (hm : S.Inc S.basePoint m) (hne : l ≠ m)
    {y z : S.Point} (hy : S.Inc y m) (hz : S.Inc z m)
    (hxy : S.basePoint ≠ y) (hxz : S.basePoint ≠ z) :
    ∃ g ∈ S.pointLineKernel l, g • y = z := by
  apply MulAction.transitive_other_two_of_nontrivial {y : S.Point | S.Inc y m}
    (S.line_points_card m) (S.pointLineKernel l) hm
    (fun _ hg => S.point_core_fixes_basePoint hg.1) ?_ ?_ hy hz hxy hxz
  · intro g hg w
    change S.Inc w m ↔ S.Inc (g • w) m
    have hf := S.core_fixes_incident_coset 0 1 (by decide) hg.1 hm
    constructor
    · intro h
      simpa only [hf] using h.smul S g
    · intro h
      have hf' := S.core_fixes_incident_coset 0 1 (by decide) ((S.Q 0).inv_mem hg.1) hm
      simpa only [hf', inv_smul_smul] using h.smul S g⁻¹
  · intro h
    exact S.pointLineKernel_not_le hl hm hne (le_inf inf_le_left h)

theorem pair_element_adjusted_by_point_core {y : S.Point}
    (hy : S.Inc y S.baseLine) (hxy : S.basePoint ≠ y)
    {a : G} (ha : a ∈ S.pair 0 1) :
    ∃ q ∈ S.Q 0, q * a ∈ S.pair 0 1 ∧ (q * a) • y = y := by
  have hfx : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_basePoint]
    exact ha.1
  have hfl : a • S.baseLine = S.baseLine := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_baseLine]
    exact ha.2
  have hay : S.Inc (a • y) S.baseLine := by simpa only [hfl] using hy.smul S a
  have hne : S.basePoint ≠ a • y := fun h => hxy
    ((MulAction.injective a) (hfx.trans h))
  obtain ⟨q, hq, he⟩ := S.point_core_baseLine_transitive hay hy hne hxy
  refine ⟨q, hq, (S.pair 0 1).mul_mem ?_ ha, ?_⟩
  · exact ⟨(S.family 0).pCoreIn_le 2 hq, S.T_le 1 (S.Q_le_T 0 hq)⟩
  · simpa only [mul_smul] using he

end Quasithin.I5.DSystem
