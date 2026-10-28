module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion.Transport
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.TwoCore
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Planes

/-!
# Ambient weak closure and involution nonfusion

The native two-core and base normalizer calculations discharge the actual
square-action stabilizer. Burnside fusion first makes A and B weakly closed
in the original Sylow, then controls fusion of A inside the original M.
The native distinction between t and z therefore persists in G.

Source: Aschbacher–Smith 13.9.2(2–5), printed pp.969–970.
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

include m in
theorem thompson_normalizer :
    normalizer (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) : Set G) =
      (d.T : Subgroup G) :=
  m.thompson_normalizer_of_native A_eq_twoCore normalizer_J

theorem normalizer_A : normalizer (m.elementaryGroup true true : Set G) = d.M :=
  m.normalizer_elementary_of_native_core A_eq_twoCore

include m in
theorem maximum_elementary_normalized (E : Subgroup G)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups (d.T : Subgroup G)) :
    Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) ≤ normalizer (E : Set G) :=
  m.maximum_elementary_normalized_of_native J_le_normalizer_elementary E hE

variable [Finite G]

theorem diagonal_weakly_closed (b : Bool) (g : G)
    (hg : (m.elementaryGroup b b).map (MulAut.conj g).toMonoidHom ≤ (d.T : Subgroup G)) :
    (m.elementaryGroup b b).map (MulAut.conj g).toMonoidHom = m.elementaryGroup b b := by
  apply Stellmacher.maxFamily_weakly_closed_of_normalizer_eq d.T m.thompson_normalizer
    m.maximum_elementary_normalized (m.elementaryGroup b b)
    ((m.maximum_elementary _).mpr ⟨b,b,rfl⟩) _ g hg
  rw [← m.image_standardSylow]
  exact m.image_le_normalizer_image (standardSylow_le_normalizer_diagonal b)

theorem diagonal_controls_fusion (b : Bool) {x y : G}
    (hx : x ∈ m.elementaryGroup b b) (hy : y ∈ m.elementaryGroup b b)
    (hxy : IsConj x y) :
    ∃ n ∈ normalizer (m.elementaryGroup b b : Set G), n * x * n⁻¹ = y :=
  Stellmacher.maxFamily_element_fusion_of_weakly_closed d.T
    (m.elementaryGroup b b) ((m.maximum_elementary _).mpr ⟨b,b,rfl⟩)
    (m.diagonal_weakly_closed b) hx hy hxy

theorem A_controls_fusion {x y : G} (hx : x ∈ m.elementaryGroup true true)
    (hy : y ∈ m.elementaryGroup true true) (hxy : IsConj x y) :
    ∃ n ∈ d.M, n * x * n⁻¹ = y := by
  obtain ⟨n,hn,hconj⟩ := m.diagonal_controls_fusion true hx hy hxy
  exact ⟨n,m.normalizer_A ▸ hn,hconj⟩

theorem not_isConj_t_z : ¬ IsConj m.t m.z := by
  intro hc
  have ht : m.t ∈ m.elementaryGroup true true := mem_map_of_mem m.embedding t_mem_A
  have hz : m.z ∈ m.elementaryGroup true true := mem_map_of_mem m.embedding z_mem_A
  obtain ⟨g,hg,he⟩ := m.A_controls_fusion ht hz hc
  obtain ⟨w,rfl⟩ := show g ∈ m.embedding.range by rwa [m.range_embedding]
  apply SymmetricFourWreath.not_isConj_t_z
  apply isConj_iff.mpr
  refine ⟨w,?_⟩
  apply m.embedding_injective
  change m.embedding w * m.embedding SymmetricFourWreath.t * (m.embedding w)⁻¹ =
    m.embedding SymmetricFourWreath.z at he
  simpa only [map_mul,map_inv] using he

end CFSG.Quasithin.Chapter13.Section09.Marking
