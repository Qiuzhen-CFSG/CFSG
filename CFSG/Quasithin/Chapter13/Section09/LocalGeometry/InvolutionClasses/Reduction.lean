module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Reduction
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.Transfer

/-!
# The original local-class inputs to the transfer argument

The actual marking transports the native involution cover and the local
swap-class exclusion. Applying the checked transfer theorem removes both
class premises from the weak-closure branch of 13.9.5. The assumed equality
C_G(z)=T and the resulting z/s nonfusion remain with the growth argument.

Source: Aschbacher–Smith 13.9.3–5, printed p.970.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem local_involution_cover (x : G) (hx : x∈d.M) (ho : orderOf x=2) :
    IsConj m.s x ∨ ∃g∈d.M,g*x*g⁻¹∈m.B := by
  obtain ⟨w,rfl⟩ := show x∈m.embedding.range by rwa [m.range_embedding]
  have hw : w*w=1 := by
    apply m.embedding_injective
    rw [map_mul,map_one]
    simpa only [pow_two,ho] using pow_orderOf_eq_one (m.embedding w)
  rcases InvolutionClasses.involution_cover w hw with hc|⟨g,hg⟩
  · exact Or.inl (m.embedding.map_isConj hc)
  · refine Or.inr ⟨m.embedding g,(m.equiv.symm g).property,?_⟩
    change m.embedding g*m.embedding w*(m.embedding g)⁻¹∈SymmetricFourWreath.B.map m.embedding
    have h := mem_map_of_mem m.embedding hg
    simpa only [map_mul,map_inv] using h

theorem local_swap_class_avoids_dihedralBase (g : G) (hg : g∈d.M) :
    g*m.s*g⁻¹∉m.dihedralBase := by
  obtain ⟨w,rfl⟩ := show g∈m.embedding.range by rwa [m.range_embedding]
  change m.embedding w*m.embedding swap*(m.embedding w)⁻¹∉SymmetricFourWreath.J.map m.embedding
  rw [←map_inv,←map_mul,←map_mul]
  exact fun h=>InvolutionClasses.swap_conjugate_not_mem_J w
    ((mem_map_iff_mem m.embedding_injective).mp h)

theorem dihedralBase_le_sylow : m.dihedralBase≤(d.T:Subgroup G) := by
  rw [←m.elementary_thompson]
  exact sSup_le (fun _ h=>h.1)

variable [Finite G]

theorem dihedralBase_index : (m.dihedralBase.subgroupOf (d.T:Subgroup G)).index=2 := by
  have hc : Nat.card (m.dihedralBase.subgroupOf (d.T:Subgroup G))=64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe m.dihedralBase_le_sylow).toEquiv,
      Marking.dihedralBase,m.card_image,card_J]
  have h := (m.dihedralBase.subgroupOf (d.T:Subgroup G)).card_mul_index
  rw [hc,d.card_sylow] at h
  omega

theorem not_weakly_closed_z_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (hsz : ¬IsConj m.z m.s) :
    ¬(∀x∈m.B,IsConj m.z x→x=m.z) := by
  apply CentralizerGrowth.not_weakly_closed_of_centralizer_eq hG d
    m.dihedralBase m.B m.dihedralBase_le_sylow m.dihedralBase_index
    m.z_mem_sylow m.z_order _ m.s_mem_sylow _ hC hsz
    m.local_swap_class_avoids_dihedralBase m.local_involution_cover
  · intro a ha
    exact (mem_centralizer_singleton_iff.mp (m.z_central_sylow ha)).symm
  · exact orderOf_eq_prime (by simpa only [pow_two] using m.s_sq) m.s_ne_one

end CFSG.Quasithin.Chapter13.Section09.Marking
