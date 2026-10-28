module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.Assembly

/-!
# The full Singer centralizer and its Sylow subgroup

The exact stabilizer of a nonzero Singer-fixed Steinberg vector is the Singer
group itself. Consequently each element of C_L(s) differs from a Singer
element by an element of C_S(s). The original quotient map restricted to the
full centralizer has kernel C_S(s) and image of order seven. Its kernel is
therefore a Sylow two-subgroup, with the original ambient embedding retained.

Source: Aschbacher–Smith, Lemma J.2.3(3), printed pp.433–434
(PDF pp.444–445, combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]
noncomputable section

lemma SingerChoice.model_mem_singer_of_centralizes (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1)
    (l : d.L) (hl : (l : G) ∈ centralizer ({s} : Set G)) :
    d.ru1.quotientMap l ∈ singerImage d B c := by
  apply (c.steinberg_stabilizer_fixedCore d B s hs hs1 l).mp
  have hc : (l : G) * s * (l : G)⁻¹ = s :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hl)
  have he := d.ru1.steinberg.equivariant l ⟨s,hs.1⟩
  exact he.symm.trans (congrArg (fun x : d.S => (d.ru1.steinberg.coordinates x).toAdd)
    (Subtype.ext hc))

/-- The full centralizer factors pointwise as C_S(s) B₇. -/
theorem SingerChoice.fullCentralizer_factor (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    ∀ l ∈ d.L ⊓ centralizer ({s} : Set G),
      ∃ x ∈ d.S ⊓ centralizer ({s} : Set G), ∃ b ∈ c.B7, l = x * b := by
  intro l hl
  obtain ⟨b,hb⟩ := c.model_mem_singer_of_centralizes d B s hs hs1 ⟨l,hl.1⟩ hl.2
  have hker : (⟨l,hl.1⟩ : d.L) * (inclusion c.le_L b)⁻¹ ∈ d.ru1.quotientMap.ker := by
    change d.ru1.quotientMap _ = 1
    rw [map_mul, map_inv]
    change d.ru1.quotientMap ⟨l,hl.1⟩ * (modelMap d c.B7 c.le_L b)⁻¹ = 1
    rw [hb]
    exact mul_inv_cancel _
  rw [d.ru1.quotient_kernel] at hker
  have hbC : (b : G) ∈ centralizer ({s} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hs.2 b b.property)
  exact ⟨l * (b : G)⁻¹, ⟨hker,(centralizer ({s} : Set G)).mul_mem hl.2
    ((centralizer ({s} : Set G)).inv_mem hbC)⟩, b,b.property,by simp⟩

/-- The actual two-centralizer is Sylow in the full centralizer, with its
original ambient embedding. -/
theorem SingerChoice.coreCentralizer_sylow (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    ∃ P : Sylow 2 (d.L ⊓ centralizer ({s} : Set G) : Subgroup G),
      (P : Subgroup (d.L ⊓ centralizer ({s} : Set G) : Subgroup G)).map
        (d.L ⊓ centralizer ({s} : Set G) : Subgroup G).subtype =
          d.S ⊓ centralizer ({s} : Set G) := by
  let D := d.L ⊓ centralizer ({s} : Set G)
  let C := d.S ⊓ centralizer ({s} : Set G)
  have hCD : C ≤ D := inf_le_inf d.ru1.steinberg.section_le le_rfl
  let f : D →* BinaryLinearThree.Group := d.ru1.quotientMap.comp (inclusion (show D ≤ d.L from inf_le_left))
  have hk : f.ker = C.subgroupOf D := by
    ext l
    change d.ru1.quotientMap (inclusion (show D ≤ d.L from inf_le_left) l) = 1 ↔ _
    change inclusion (show D ≤ d.L from inf_le_left) l ∈ d.ru1.quotientMap.ker ↔ _
    rw [d.ru1.quotient_kernel]
    exact ⟨fun h => ⟨h,l.property.2⟩,fun h => h.1⟩
  have hr : f.range = singerImage d B c := by
    apply le_antisymm
    · rintro _ ⟨l,rfl⟩
      exact c.model_mem_singer_of_centralizes d B s hs hs1
        (inclusion (show D ≤ d.L from inf_le_left) l) l.property.2
    · rintro _ ⟨b,rfl⟩
      exact ⟨⟨b,c.le_L b.property,mem_centralizer_singleton_iff.mpr (hs.2 b b.property)⟩,rfl⟩
  have hi : (C.subgroupOf D).index = 7 := by
    rw [← hk, index_ker, hr, singerImage_card d B c]
  have hp : IsPGroup 2 (C.subgroupOf D) :=
    ((isPGroup_pCoreIn 2 d.L).to_le (show C ≤ d.S from inf_le_left)).of_equiv
      (subgroupOfEquivOfLe hCD).symm
  refine ⟨hp.toSylow (by rw [hi]; decide), ?_⟩
  exact map_subgroupOf_eq_of_le hCD
end
end CFSG.Quasithin.ChapterJ.SpecialCore
