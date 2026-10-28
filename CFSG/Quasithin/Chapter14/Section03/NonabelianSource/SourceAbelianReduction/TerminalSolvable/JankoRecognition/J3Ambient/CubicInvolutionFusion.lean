module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicOverlapSource
public import Theory.GroupTheory.PrimeOrderCentralizerSylow

/-!
# Fusion of actual cubics centralizing involutions

Transport each commuting involution to the original one. Its full centralizer
has order1920, hence Sylow-three subgroups of order three. Sylow conjugacy
aligns the cyclic groups, and the original involutory inverter aligns their
generators. Thus the two actual cubics are conjugate in the original group.
This is the source fusion used to split the cubic normalizer in Baumeister2.4.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem local_cubic_fusion (P : ReturningPair D)
    (x y : Janko23.involutionCentralizer D.z) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    IsConj x y := by
  classical
  have hSyl (S : Sylow 3 (Janko23.involutionCentralizer D.z)) : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity,D.localType.centralizer_card]
    decide +kernel
  obtain ⟨g,hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers y) y (mem_zpowers y) hy hSyl x hx
  have hxc : g*x*g⁻¹ ≠ 1 := by
    intro h
    have ho := (MulAut.conj g).orderOf_eq x
    change orderOf (g*x*g⁻¹) = orderOf x at ho
    rw [h,orderOf_one,hx] at ho
    contradiction
  rw [mem_zpowers_iff_mem_range_orderOf,hy] at hg
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hg
  have hn3 : n<3 := Finset.mem_range.mp hn
  interval_cases n
  · exact (hxc (by simpa only [pow_zero] using he.symm)).elim
  · exact isConj_iff.mpr ⟨g,by simpa only [pow_one] using he.symm⟩
  · have hyi : y^2=y⁻¹ := by
      apply mul_right_cancel (b := y)
      have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
      rw [←pow_succ,hy3,inv_mul_cancel]
    have hxy : IsConj x y⁻¹ := isConj_iff.mpr ⟨g,by simpa only [hyi] using he.symm⟩
    obtain ⟨r,_hr,hri⟩ := cubic_local_involutory_inverter P y hy
    exact hxy.trans (isConj_iff.mpr ⟨r,hri⟩).symm

private theorem cubic_in_original_centralizer (hc : Janko23.OneInvolutionClass G)
    (x t : G) (hx : orderOf x = 3) (ht : orderOf t = 2) (hxt : Commute x t) :
    ∃ u : Janko23.involutionCentralizer D.z, orderOf u = 3 ∧ IsConj x (u : G) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution ht)
  let a := MulAut.conj g
  have hat : a t = D.z := hg
  let u : Janko23.involutionCentralizer D.z := ⟨a x,mem_centralizer_singleton_iff.mpr (by
    rw [←hat,←map_mul,←map_mul,hxt.eq])⟩
  refine ⟨u,(orderOf_coe u).symm.trans ((a.orderOf_eq x).trans hx),?_⟩
  exact isConj_iff.mpr ⟨g,rfl⟩

/-- Cubics centralizing actual involutions form one ambient conjugacy class
in the original single-involution-class source. -/
theorem literal_cubic_fusion_of_commuting_involutions
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (x y t u : G) (hx : orderOf x = 3) (hy : orderOf y = 3)
    (ht : orderOf t = 2) (hu : orderOf u = 2)
    (hxt : Commute x t) (hyu : Commute y u) : IsConj x y := by
  obtain ⟨x',hx',hxx⟩ := cubic_in_original_centralizer (D := D) hc x t hx ht hxt
  obtain ⟨y',hy',hyy⟩ := cubic_in_original_centralizer (D := D) hc y u hy hu hyu
  exact hxx.trans (((Janko23.involutionCentralizer D.z).subtype.map_isConj
    (local_cubic_fusion P x' y' hx' hy')).trans hyy.symm)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
