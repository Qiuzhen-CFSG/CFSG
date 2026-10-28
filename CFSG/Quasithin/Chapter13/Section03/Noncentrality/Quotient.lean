module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Basic

/-!
# Nontriviality of the parabolic two-core in the star quotient

A normal two-subgroup maps into the two-core of its actual image. If the
image of L₊ had trivial two-core, O₂(L₊) would lie in Q₁. Reduction (a)
then makes it centralize V₃, contrary to the earlier parabolic action.

The star map below is literally L₊ → G₁ → G₁/O₂(G₁). No identification of
two-core images, injectivity, or replacement quotient is assumed.
Source: Aschbacher–Smith, Lemma 13.3.14(c), printed pp.891–892.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Subgroup
variable {G : Type*} [Group G]

/-- The literal star quotient of the point group. -/
abbrev Star (H : Subgroup G) := H ⧸ pCore 2 H

/-- Restrict the star projection to a subgroup that lies in H. -/
def starMap (H A : Subgroup G) (hAH : A ≤ H) : A →* Star H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)

/-- The actual star image; the inclusion witness is used by the projection. -/
def star (H A : Subgroup G) (hAH : A ≤ H) : Subgroup (Star H) :=
  (starMap H A hAH).range

/-- A trivial two-core in the actual image forces the original two-core
into the kernel. The assertion uses a surjection onto the range, not onto
an arbitrary supplied quotient. -/
theorem core_le_kernel_of_image_core_eq_bot {D E : Type*} [Group D] [Group E]
    (f : D →* E) (he : pCore 2 f.range = ⊥) : pCore 2 D ≤ f.ker := by
  let r := f.rangeRestrict
  have hn : ((pCore 2 D).map r).Normal :=
    Subgroup.Normal.map inferInstance r f.rangeRestrict_surjective
  have hm : (pCore 2 D).map r ≤ pCore 2 f.range :=
    le_sSup ⟨hn, pCore_isPGroup.map r⟩
  intro d hd
  have hh : r d ∈ (⊥ : Subgroup f.range) := he ▸ hm (mem_map_of_mem r hd)
  exact congrArg Subtype.val (mem_bot.mp hh)

/-- Reduction (c). The movement premise is the original O₂(L₊)-action on
V₃, supplied by the preceding parabolic geometry; the quotient conclusion
is proved here. -/
theorem reduction_c (H Lplus V₃ : Subgroup G) (hLplus : Lplus ≤ H)
    (hcentral : H.pCoreIn 2 ≤ centralizer (V₃ : Set G))
    (hmoves : ¬ Lplus.pCoreIn 2 ≤ centralizer (V₃ : Set G)) :
    pCore 2 (star H Lplus hLplus) ≠ ⊥ := by
  intro he
  have hk := core_le_kernel_of_image_core_eq_bot (starMap H Lplus hLplus) he
  apply hmoves
  rintro x ⟨l, hl, rfl⟩
  apply hcentral
  have hq : inclusion hLplus l ∈ pCore 2 H :=
    (QuotientGroup.eq_one_iff _).mp (hk hl)
  exact mem_map.mpr ⟨inclusion hLplus l, hq, rfl⟩

/-- Direct application of (c) to the omega-center conclusion of (a). -/
theorem reduction_c_of_reduction_a (H Lplus V₃ : Subgroup G) (hLplus : Lplus ≤ H)
    (ha : conjugateSpanBy V₃ H ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hmoves : ¬ Lplus.pCoreIn 2 ≤ centralizer (V₃ : Set G)) :
    pCore 2 (star H Lplus hLplus) ≠ ⊥ := by
  apply reduction_c H Lplus V₃ hLplus _ hmoves
  apply le_centralizer_iff.mp
  intro v hv q hq
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp
    (ha (le_conjugateSpanBy V₃ H hv))).2.2 q hq

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
