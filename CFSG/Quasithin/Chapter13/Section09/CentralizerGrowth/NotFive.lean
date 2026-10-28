module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ExcludedClasses

/-!
# Excluding the five-point alternative

A distinct conjugate in B contains an entire four-point Sylow orbit. Its pointwise centralizer identifies the actual orbit kernel with B, excluding five points without a module-classification premise.

Source: Aschbacher–Smith 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

theorem conjugate_z_pointwise_centralizer_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    (d.T:Subgroup G)⊓centralizer {x:G | x∈m.B ∧ IsConj m.z x}=m.B := by
  obtain ⟨x,hx,hzx,hne⟩ := m.exists_conjugate_z_in_B_of_centralizer_eq hG hC
  have hxM := d.sylow_le (m.elementaryGroup_le_sylow false false hx)
  obtain ⟨i,hi,hxc⟩ : ∃i:Fin 6,(i=3 ∨ i=4) ∧ x∈m.localInvolutionClass i := by
    rcases m.conjugate_z_local_classes_of_centralizer_eq hC x hxM hzx with hz|h3|h4
    · have he : x∈{x:G | x∈m.B ∧ x∈m.localInvolutionClass 0} := ⟨hx,hz⟩
      rw [m.B_local_class_zero] at he
      exact (hne he).elim
    · exact ⟨3,Or.inl rfl,h3⟩
    · exact ⟨4,Or.inr rfl,h4⟩
  apply le_antisymm
  · have hc : centralizer {x:G | x∈m.B ∧ IsConj m.z x}≤
        centralizer {x:G | x∈m.B ∧ x∈m.localInvolutionClass i} := by
      apply centralizer_le
      rintro y ⟨hy,hyc⟩
      obtain ⟨g,_,he⟩ := m.B_local_class_transitive i x y hx hy hxc hyc
      exact ⟨hy,hzx.trans (isConj_iff.mpr ⟨g,he⟩)⟩
    exact (inf_le_inf_left _ hc).trans_eq (m.B_local_class_pointwise_centralizer i hi)
  · intro b hb
    refine ⟨m.elementaryGroup_le_sylow false false hb,?_⟩
    rintro y ⟨hy,_⟩
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.B)).is_comm.comm
        (⟨y,hy⟩:m.B) ⟨b,hb⟩)

theorem normalizerOrbit_card_ne_five_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    m.normalizerOrbit.ncard≠5 :=
  m.normalizerOrbit_card_ne_five_of_centralizer hC
    (m.conjugate_z_pointwise_centralizer_of_centralizer_eq hG hC)

theorem normalizerOrbit_card_ne_one_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    m.normalizerOrbit.ncard≠1 := by
  obtain ⟨x,hx,hn⟩ := m.normalizerOrbit_nontrivial_of_centralizer_eq hG hC
  have hgt : 1<m.normalizerOrbit.ncard :=
    Set.one_lt_ncard_iff_nontrivial.mpr
      ⟨x,hx,m.normalizerPoint,MulAction.mem_orbit_self _,hn⟩
  omega
end CFSG.Quasithin.Chapter13.Section09.Marking
