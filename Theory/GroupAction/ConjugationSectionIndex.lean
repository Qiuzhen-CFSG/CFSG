module
public import Theory.GroupAction.QuotientFixedIndex
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Fixed index from a conjugation bound on a literal quotient

If [A,D] lies in N and N <= D, the image of D in W/N is fixed by
A intersect L under the specified conjugation action. Its index bounds the
fixed-subgroup index; quotienting by N preserves the index of D intersect W.
Normality is required only for N inside W. The action formula retains the
original ambient conjugation and both subgroup inclusions.

Source application: DGS, *Groups and Graphs* (1985), 8.4, p.138, for
W = V_beta^(3), N = V_beta, D = (W intersect Q_alpha') V_beta.
-/

public noncomputable section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- A literal commutator bound supplies an upper bound on fixed index in
the quotient, without a faithfulness or elementary-group hypothesis. -/
theorem quotient_conjugation_fixedIndex_le
    (L W N D A : Subgroup G) [Finite W] [(N.subgroupOf W).Normal]
    (hnW : L ≤ normalizer (W : Set G))
    (α : L →* MulAut (W ⧸ N.subgroupOf W))
    (hα : ∀ l : L, ∀ x : W,
      α l (QuotientGroup.mk' (N.subgroupOf W) x) =
        QuotientGroup.mk' (N.subgroupOf W)
          ⟨(l : G) * (x : G) * (l : G)⁻¹,
            (mem_normalizer_iff.mp (hnW l.property) x).mp x.property⟩)
    (hND : N ≤ D) (hcomm : ⁅A,D⁆ ≤ N) :
    let _ := MulDistribMulAction.compHom (W ⧸ N.subgroupOf W)
      (α.comp (A.subgroupOf L).subtype)
    (FixedPoints.subgroup (A.subgroupOf L) (W ⧸ N.subgroupOf W)).index ≤ D.relIndex W := by
  let _ := MulDistribMulAction.compHom (W ⧸ N.subgroupOf W)
    (α.comp (A.subgroupOf L).subtype)
  let q := QuotientGroup.mk' (N.subgroupOf W)
  have hfix : (D.subgroupOf W).map q ≤
      FixedPoints.subgroup (A.subgroupOf L) (W ⧸ N.subgroupOf W) := by
    rintro _ ⟨x,hx,rfl⟩ a
    change α a.val (q x) = q x
    rw [hα]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a.val : G) * (x : G) * (a.val : G)⁻¹ / (x : G) ∈ N
    simpa only [commutatorElement_def,div_eq_mul_inv,subtype_apply] using
      hcomm (commutator_mem_commutator a.property hx)
  have hi := Subgroup.index_antitone hfix
  have hk : q.ker ≤ D.subgroupOf W := by
    intro x hx
    exact hND ((QuotientGroup.eq_one_iff x).mp hx)
  rwa [(D.subgroupOf W).index_map_eq (QuotientGroup.mk'_surjective _) hk] at hi
end Subgroup
