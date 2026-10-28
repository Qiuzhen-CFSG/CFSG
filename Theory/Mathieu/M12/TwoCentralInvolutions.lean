module

public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# The two-central involution class of M₁₂

The checked Sylow subgroup has center {1,z}. Sylow conjugacy therefore
identifies every two-central involution with the conjugacy class of z;
conversely that class is two-central. This uses the actual Witt-design
carrier and Sylow subgroup, without an assumed involution table.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
The model and Sylow-center calculation come from SmallParabolicPair.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace Sporadic.Mathieu.M12Involutions

theorem z_twoCentral : TwoCentral z := by
  refine ⟨commonSylow, core_le_sylowCandidate z_mem_core, ?_⟩
  exact (sylowCandidate_center_mem _).mpr (Or.inr rfl)

theorem isConj_z_of_twoCentral (x : M12) (hx : orderOf x = 2) (hc : TwoCentral x) : IsConj z x := by
  obtain ⟨P, hp, hc⟩ := hc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P commonSylow
  have hP : ((g • P : Sylow 2 M12) : Subgroup M12) = sylowCandidate :=
    (congrArg (fun S : Sylow 2 M12 => (S : Subgroup M12)) hg).trans commonSylow_coe
  let eP : P ≃* sylowCandidate :=
    (P.equivSMul g).trans (MulEquiv.subgroupCongr hP)
  have hyc : eP ⟨x, hp⟩ ∈ center sylowCandidate := by
    apply mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := eP.surjective t
    rw [← eP.map_mul, ← eP.map_mul, mem_center_iff.mp hc s]
  rcases (sylowCandidate_center_mem _).mp hyc with ho | hz
  · have he : x = 1 := (MulAut.conj g).map_eq_one_iff.mp ho
    simp [he] at hx
  · exact (isConj_iff.mpr ⟨g, hz⟩).symm

theorem twoCentral_iff_isConj_z (x : M12) (hx : orderOf x = 2) :
    TwoCentral x ↔ IsConj z x := by
  refine ⟨isConj_z_of_twoCentral x hx, ?_⟩
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact hg ▸ z_twoCentral.map (MulAut.conj g)

end Sporadic.Mathieu.M12Involutions
