module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.ScalarQuotient
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# Comparing the native Mathieu actions on 22 points

Compose the two faithful conjugation equivalences with Aut(M22). The resulting
comparison agrees with restriction from degree 24 to the complement of {0,9}.
Indeed the conjugation equations intertwine the two natural actions, and
two-transitivity implies that a point stabilizer fixes no other moving point.
This proves the coordinate equation for every element of the full outer group.

Source: Aschbacher--Smith, H.13.1 and the H.14 setup, printed pp.395--396
(1 March 2004 manuscript), used in 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

/-- Identify the deleted-pair group and the degree-22 design group through
their actual conjugation actions on native M22. -/
def pairQuintetDesignEquiv : MathieuCode.m22PairStabilizer ≃* m22DesignAut :=
  m22PairStabilizerEquivAut.trans referenceDesignEquiv.symm

private theorem design_conjugation (g : MathieuCode.m22PairStabilizer) (k : M22) (i : Fin 22) :
    m22PairStabilizerEquivAut g k • (pairQuintetDesignEquiv g • i) =
      pairQuintetDesignEquiv g • (k • i) := by
  have h : m22DesignAutToAut (pairQuintetDesignEquiv g) = m22PairStabilizerEquivAut g :=
    referenceDesignEquiv.apply_symm_apply _
  rw [← h]
  change ((m22DesignAutToAut (pairQuintetDesignEquiv g) k : M22) : Equiv.Perm (Fin 22))
    ((pairQuintetDesignEquiv g).val i) = _
  rw [m22DesignAutToAut_apply_perm]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  rfl

private theorem coordinate_conjugation (g : MathieuCode.m22PairStabilizer) (k : M22) (i : Fin 22) :
    m22Embedding (m22PairStabilizerEquivAut g k) • (g.val • m22Coordinates i) =
      g.val • m22Coordinates (k • i) := by
  rw [m22PairStabilizerEquivAut_apply]
  simp only [mul_smul, inv_smul_smul]
  exact congrArg (fun x : Fin 24 => g.val • x) (m22Embedding_apply k i)

private theorem coordinate_outside (i : Fin 22) : m22Coordinates i ∉ m22Pair := by
  revert i
  decide +kernel

private theorem coordinate_cover (a : Fin 24) :
    a = 0 ∨ a = 9 ∨ ∃ i : Fin 22, m22Coordinates i = a := by
  revert a
  decide +kernel

private theorem coordinates_moved (g : MathieuCode.m22PairStabilizer) (i : Fin 22) :
    ∃ j : Fin 22, m22Coordinates j = g.val • m22Coordinates i := by
  have ho : g.val • m22Coordinates i ∉ m22Pair := fun h =>
    coordinate_outside i ((MulAction.mem_stabilizer_finset.mp g.property _).mp h)
  obtain h | h | h := coordinate_cover (g.val • m22Coordinates i)
  · exact (ho (by simp [m22Pair, h])).elim
  · exact (ho (by simp [m22Pair, h])).elim
  · exact h

/-- The conjugation comparison is the actual restriction to the 22 moving
coordinates, including the outer extension. -/
theorem pairQuintetDesignEquiv_coordinates (g : MathieuCode.m22PairStabilizer) (i : Fin 22) :
    m22Coordinates (pairQuintetDesignEquiv g • i) = g.val • m22Coordinates i := by
  obtain ⟨j, hj⟩ := coordinates_moved g i
  suffices h : j = pairQuintetDesignEquiv g • i by rw [← h]; exact hj
  by_contra hne
  obtain ⟨z, hzx, hzj⟩ := Fin.exists_ne_and_ne_of_two_lt
    (pairQuintetDesignEquiv g • i) j (by decide)
  obtain ⟨k, hkx, hkj⟩ :=
    (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
      (Ne.symm hne) hzx.symm
  let l := (m22PairStabilizerEquivAut g).symm k
  have hl : MathieuCode.m22PairStabilizerEquivAut g l = k := MulEquiv.apply_symm_apply _ _
  have hli : l • i = i := by
    apply (MulAction.injective (pairQuintetDesignEquiv g))
    change pairQuintetDesignEquiv g • (l • i) = pairQuintetDesignEquiv g • i
    rw [← design_conjugation g l i, hl]
    exact hkx
  have hc := coordinate_conjugation g l i
  rw [hl, hli, ← hj] at hc
  change (m22Embedding k).val (m22Coordinates j) = m22Coordinates j at hc
  rw [m22Embedding_apply] at hc
  have hjfix := m22Coordinates.injective hc
  exact hzj (hkj.symm.trans hjfix)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
