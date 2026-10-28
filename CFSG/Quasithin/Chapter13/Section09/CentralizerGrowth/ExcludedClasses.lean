module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.NormalizerOrbit
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.InvolutionClasses

/-!
# Excluding the axis and swapping classes

An axis element centralizes the opposite S₄. Together with the swapping centralizer this excludes three classes from the z-class under C_G(z)=T.

Source: Aschbacher–Smith 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem not_isConj_z_axis_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (a:S4) :
    ¬IsConj m.z (m.embedding (SymmetricFourWreath.factor 1 a)) := by
  apply Theory.GroupTheory.not_isConj_of_non_pGroup_centralized (p:=2) (m.factor turn)
  · rw [hC]
    exact d.T.isPGroup'
  · intro hp
    have hs := hp.of_equiv (m.factorEquiv turn)
    have hd := hs.dvd_orderOf SymmetricFourConjugacy.threeCycle_ne_one
    rw [SymmetricFourConjugacy.orderOf_threeCycle] at hd
    norm_num at hd
  · rintro x ⟨w,⟨b,rfl⟩,rfl⟩
    rw [mem_centralizer_singleton_iff]
    change m.embedding (SymmetricFourWreath.factor turn b)*m.embedding (SymmetricFourWreath.factor 1 a)=_
    rw [←map_mul,←map_mul]
    exact congrArg m.embedding (factor_commute turn_ne_one b a).eq

theorem not_isConj_z_representative_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (i:Fin 6)
    (hi:i=1 ∨ i=2 ∨ i=5) : ¬IsConj m.z (m.embedding (representative i)) := by
  rcases hi with rfl|rfl|rfl
  · exact m.not_isConj_z_axis_of_centralizer_eq hC (square (DihedralGroup.r 2))
  · exact m.not_isConj_z_axis_of_centralizer_eq hC (square (DihedralGroup.sr 0))
  · exact m.not_isConj_z_s_of_centralizer_eq hC

theorem conjugate_z_local_classes_of_centralizer_eq [Finite G]
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (x:G) (hx:x∈d.M) (hconj:IsConj m.z x) :
    x∈m.localInvolutionClass 0 ∨ x∈m.localInvolutionClass 3 ∨ x∈m.localInvolutionClass 4 := by
  have ho : orderOf x=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    rw [←hg,←MulAut.conj_apply]
    exact ((MulAut.conj g).orderOf_eq m.z).trans m.z_order
  obtain ⟨i,hi,_⟩ := m.local_involution_classes x hx ho
  have hn : i≠1 ∧ i≠2 ∧ i≠5 := by
    have hc : IsConj (m.embedding (representative i)) x := by
      obtain ⟨g,_,he⟩ := hi
      exact isConj_iff.mpr ⟨g,he⟩
    exact ⟨fun he=>m.not_isConj_z_representative_of_centralizer_eq hC i (Or.inl he) (hconj.trans hc.symm),
      fun he=>m.not_isConj_z_representative_of_centralizer_eq hC i (Or.inr (Or.inl he)) (hconj.trans hc.symm),
      fun he=>m.not_isConj_z_representative_of_centralizer_eq hC i (Or.inr (Or.inr he)) (hconj.trans hc.symm)⟩
  have he : i=0 ∨ i=3 ∨ i=4 := by omega
  rcases he with rfl|rfl|rfl
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
end CFSG.Quasithin.Chapter13.Section09.Marking
