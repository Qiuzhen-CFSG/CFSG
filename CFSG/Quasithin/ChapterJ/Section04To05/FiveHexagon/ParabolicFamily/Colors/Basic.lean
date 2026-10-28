module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Inverted
public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.Data.Set.Card

/-!
# The three original involution colors of the parabolic family

A colored member is a literal ambient conjugate of F₁ whose original
central generator is carried to the specified involution, and which contains
⟨z,u⟩. The actual center of F₁ is ⟨z⟩: Q₅ lies in F₁ and C_G(Q₅)=⟨z⟩,
while F₁≤C_G(z). Hence different colors are disjoint. The four-group's
nonidentity elements are exactly z,u,zu. No five-subgroup closure is used.
Source: Aschbacher--Smith J.4.7, printed p.443.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The literal original four-group span. -/
def pairSpan (z u : G) : Subgroup G := zpowers z ⊔ zpowers u

/-- The three nonidentity involution labels. -/
def colors (z u : G) : Set G := {z,u,z*u}

/-- Original conjugates with a specified transported central generator. -/
def colorFamily (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) (z u v : G) : Set (Subgroup G) :=
  {E | ∃ g : G, E=(p.F₁ B5).conjBy g ∧ g*z*g⁻¹=v ∧ pairSpan z u ≤ E}

/-- The original union of the three involution-colored families. -/
def globalFamily (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) (z u : G) : Set (Subgroup G) :=
  {E | ∃ v ∈ colors z u, E ∈ colorFamily p B5 z u v}

variable (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (c : Choices d) (e : first ≃* p.F₁ B5) (hz : (e modelZ : G)=c.z)
include hz

/-- The actual first endpoint has precisely the original central involution as its center. -/
theorem first_embedded_center : (center (p.F₁ B5)).map (p.F₁ B5).subtype = zpowers c.z := by
  apply le_antisymm
  · rintro x ⟨x,hx,rfl⟩
    have hc : (x : G) ∈ centralizer (Q₅ d B5 : Set G) := by
      intro a ha
      let aF : p.F₁ B5 := ⟨a,(show Q₅ d B5 ≤ p.F₁ B5 from le_sup_right.trans le_sup_left) ha⟩
      exact congrArg Subtype.val (mem_center_iff.mp hx aF)
    rwa [centralizer_Q₅ d B5,c.z_generator] at hc
  · apply zpowers_le.mpr
    have hzF : c.z ∈ p.F₁ B5 := hz ▸ (e modelZ).property
    refine ⟨⟨c.z,hzF⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    apply Subtype.ext
    apply mem_centralizer_singleton_iff.mp
    rw [← c.H_eq_centralizer_z]
    exact p.F₁_le_H B5 a.property

/-- Conjugate centers retain the very same source central generator. -/
theorem conjugate_embedded_center (g : G) :
    (center ((p.F₁ B5).conjBy g)).map ((p.F₁ B5).conjBy g).subtype =
      zpowers (g*c.z*g⁻¹) := by
  unfold Subgroup.conjBy
  rw [← map_embeddedCenter (p.F₁ B5) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    first_embedded_center p B5 c e hz,MonoidHom.map_zpowers]
  rfl

omit hz in
private theorem two_zpowers_cases {z x : G} (hz : orderOf z=2) :
    x ∈ zpowers z ↔ x=1 ∨ x=z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,hz]
  constructor
  · intro hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    have hn := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩
    · exact Finset.mem_image.mpr ⟨1,by simp,by simp⟩

/-- The specified color is the unique nonidentity element of the actual center. -/
theorem colorFamily_center {v : G} {E : Subgroup G}
    (hE : E ∈ colorFamily p B5 c.z (sourceU e) v) :
    (center E).map E.subtype=zpowers v ∧ orderOf v=2 := by
  obtain ⟨g,rfl,hgv,_⟩ := hE
  refine ⟨?_,?_⟩
  · rw [conjugate_embedded_center p B5 c e hz,hgv]
  · rw [← hgv]
    exact ((MulAut.conj g).orderOf_eq c.z).trans (SourceCompletion.z_order c)

/-- Different original central labels give disjoint parabolic families. -/
theorem colorFamily_disjoint {v w : G} (hne : v≠w) :
    Disjoint (colorFamily p B5 c.z (sourceU e) v) (colorFamily p B5 c.z (sourceU e) w) := by
  apply Set.disjoint_left.mpr
  intro E hv hw
  obtain ⟨hvc,hvo⟩ := colorFamily_center p B5 c e hz hv
  obtain ⟨hwc,hwo⟩ := colorFamily_center p B5 c e hz hw
  have he : zpowers v=zpowers w := hvc.symm.trans hwc
  have hvw : v ∈ zpowers w := he ▸ mem_zpowers v
  rcases (two_zpowers_cases hwo).mp hvw with hh | hh
  · rw [hh,orderOf_one] at hvo
    omega
  · exact hne hh

/-- The original z-colored family is precisely the already counted H-family. -/
theorem colorFamily_z : colorFamily p B5 c.z (sourceU e) c.z = family p B5 (sourceU e) := by
  ext E
  constructor
  · rintro ⟨g,rfl,hg,hV⟩
    have hgH : g ∈ d.toTypeRuSetup.H := by
      rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp hg
    exact (source_family_iff_pair p B5 c e hz _).mpr ⟨⟨⟨g,hgH⟩,rfl⟩,hV⟩
  · intro hE
    obtain ⟨⟨g,rfl⟩,hV⟩ := (source_family_iff_pair p B5 c e hz E).mp hE
    refine ⟨g,rfl,?_,hV⟩
    apply mul_inv_eq_iff_eq_mul.mpr
    apply mem_centralizer_singleton_iff.mp
    rw [← c.H_eq_centralizer_z]
    exact g.property

/-- The source involutions commute, have order two and are distinct. -/
theorem source_pair_marks : orderOf c.z=2 ∧ orderOf (sourceU e)=2 ∧ c.z≠sourceU e ∧
    Commute c.z (sourceU e) := by
  obtain ⟨hu2,hu1,huz⟩ := source_involution_marks c e hz
  refine ⟨SourceCompletion.z_order c,orderOf_eq_prime_iff.mpr ⟨hu2,hu1⟩,Ne.symm huz,?_⟩
  have huH : sourceU e ∈ d.toTypeRuSetup.H := p.F₁_le_H B5 (e modelU).property
  rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff] at huH
  exact huH.symm

/-- The original pair span has just the identity and the three specified colors. -/
theorem pairSpan_cases (x : G) : x ∈ pairSpan c.z (sourceU e) ↔
    x=1 ∨ x=c.z ∨ x=sourceU e ∨ x=c.z*sourceU e := by
  obtain ⟨hzo,huo,_,hcomm⟩ := source_pair_marks p B5 c e hz
  have hn : zpowers (sourceU e) ≤ normalizer (zpowers c.z : Set G) := by
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (sourceU e*c.z*(sourceU e)⁻¹)=zpowers c.z
    rw [mul_inv_eq_of_eq_mul hcomm.eq.symm]
  constructor
  · intro hx
    have hm : x ∈ (zpowers c.z : Set G) * (zpowers (sourceU e) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    rcases (two_zpowers_cases hzo).mp ha with rfl | rfl <;>
      rcases (two_zpowers_cases huo).mp hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact (pairSpan c.z (sourceU e)).one_mem
    · exact mem_sup_left (mem_zpowers c.z)
    · exact mem_sup_right (mem_zpowers (sourceU e))
    · exact mul_mem_sup (mem_zpowers c.z) (mem_zpowers (sourceU e))

/-- Colors are intrinsically the nonidentity elements of the original four-group. -/
theorem colors_iff (x : G) : x ∈ colors c.z (sourceU e) ↔
    x ∈ pairSpan c.z (sourceU e) ∧ x≠1 := by
  obtain ⟨hzo,huo,hne,_⟩ := source_pair_marks p B5 c e hz
  have hz1 : c.z≠1 := by intro h;rw [h,orderOf_one] at hzo;omega
  have hu1 : sourceU e≠1 := by intro h;rw [h,orderOf_one] at huo;omega
  have hzu1 : c.z*sourceU e≠1 := by
    intro hh
    have hu2 := (orderOf_eq_prime_iff.mp huo).1
    have huinv : (sourceU e)⁻¹=sourceU e := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
    exact hne ((eq_inv_of_mul_eq_one_left hh).trans huinv)
  rw [pairSpan_cases p B5 c e hz]
  simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl),hz1⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)),hu1⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)),hzu1⟩
  · rintro ⟨hh,hx⟩
    exact hh.resolve_left hx

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
