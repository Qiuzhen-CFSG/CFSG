module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.PCoreCommutatorCentralizer
public import Theory.GroupTheory.PCoreSurjective

/-!
# The faithful-layer kernel in E.2.13

Pass to the original central quotient by Z=V∩V^g. Characteristic two
descends through this central kernel. The established two-conjugate
identity [O₂(X),X]≤P then places the centralizer of P/Z inside the quotient
two-core. Pulling back along the actual quotient map gives C_X(P/Z)≤O₂(X).
No degree estimate or quotient-family recognition is needed for this step.

Source: Aschbacher–Smith E.2.13(7), combined manuscript (1 March 2004),
printed p.225. Equality of the independent maximal core with O₂(X) belongs
to E.2.11; this statement retains the literal action kernel and two-core.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- E.2.13(7), with the actual quotient map and the actual two-core. -/
theorem quotient_core_centralizer_le (h : Hypotheses T V M g)
    (hfit : generalizedFitting X = pCore 2 X) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    (centralizer ((P V M g).map q : Set (X ⧸ Z V g))).comap q ≤ pCore 2 X := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hZ : Z V g ≤ center X := h.core_geometry.2.2.trans inf_le_right
  have hZQ : Z V g ≤ pCore 2 X :=
    (h.core_geometry.2.2.trans inf_le_left).trans h.P_le_twoCore
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.to_le hZQ
  have hpre := q.comap_pCore_of_ker_isPGroup hsurj hker
  have hmap : (pCore 2 X).map q = pCore 2 (X ⧸ Z V g) := by
    rw [← hpre, map_comap_eq_self_of_surjective hsurj]
  have htop : (⊤ : Subgroup X).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj]
  have hcomm : ⁅pCore 2 (X ⧸ Z V g), (⊤ : Subgroup (X ⧸ Z V g))⁆ ≤
      (P V M g).map q := by
    rw [← hmap, ← htop, ← map_commutator]
    exact map_mono h.commutator_twoCore_le_P
  have hself := q.centralizer_pCore_le_of_surjective_centralKernel hsurj
    (show q.ker ≤ center X by rwa [QuotientGroup.ker_mk'])
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  have hb := centralizer_le_pCore_of_core_commutator ((P V M g).map q) hself hcomm
  exact (comap_mono hb).trans hpre.le
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
