module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The actual component section action

The normalizer of `L` acts by conjugation on `L/O₂(L)`. Its kernel is
identified with the existing Chapter 4 section centralizer, and its
restriction to `L` is the inner automorphism defined by the quotient map.
These identities connect the group-theoretic image comparison to the
literal residual subgroups in the proof of 15.3.12(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed p.1125 (PDF p.1142).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting
variable {G : Type*} [Group G]

/-- Conjugation by the normalizer on the actual two-core quotient. -/
def sectionAction (L : Subgroup G) : normalizer (L : Set G) →* MulAut (TwoCoreQuotient L) :=
  (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom

@[simp] theorem sectionAction_apply (L : Subgroup G) (g : normalizer (L : Set G)) (l : L) :
    sectionAction L g (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom g l) :=
  quotientAut_apply_mk _ _ _

/-- The kernel agrees with the existing Chapter 4 section centralizer. -/
theorem sectionAction_ker (L : Subgroup G) :
    (sectionAction L).ker.map (normalizer (L : Set G)).subtype =
      Chapter4.sectionCentralizer L := by
  apply le_antisymm
  · apply (Chapter4.le_sectionCentralizer_iff _ L).mpr
    refine ⟨map_subtype_le _, commutator_le.mpr ?_⟩
    rintro g ⟨n, hn, rfl⟩ l hl
    have he := DFunLike.congr_fun (show sectionAction L n = 1 from hn)
      (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)
    rw [sectionAction_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    refine mem_map.mpr ⟨_, hm, ?_⟩
    simp only [subtype_apply, normalizerMonoidHom, div_eq_mul_inv, commutatorElement_def]
    rfl
  · intro g hg
    have hc := (Chapter4.le_sectionCentralizer_iff (Chapter4.sectionCentralizer L) L).mp le_rfl
    refine mem_map.mpr ⟨⟨g, hc.1 hg⟩, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [sectionAction_apply]
    change QuotientGroup.mk' (pCore 2 L) _ = QuotientGroup.mk' (pCore 2 L) l
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh := hc.2 (commutator_mem_commutator hg l.property)
    obtain ⟨c, hcm, hce⟩ := hh
    have he : c = L.normalizerMonoidHom ⟨g, hc.1 hg⟩ l / l := by
      apply Subtype.ext
      calc
        (c : G) = ⁅g, (l : G)⁆ := hce
        _ = _ := by
          simp only [normalizerMonoidHom, div_eq_mul_inv, commutatorElement_def]
          rfl
    exact he ▸ hcm

/-- A normalizing element acts trivially precisely when it belongs to the
existing section centralizer. -/
theorem sectionAction_eq_one_iff (L : Subgroup G) (g : normalizer (L : Set G)) :
    sectionAction L g = 1 ↔ (g : G) ∈ Chapter4.sectionCentralizer L := by
  rw [← sectionAction_ker]
  exact ⟨fun h => mem_map_of_mem _ h, fun ⟨n, hn, he⟩ =>
    (Subtype.ext he : n = g) ▸ hn⟩

/-- On `L` itself this is the ordinary inner automorphism of its quotient. -/
theorem sectionAction_on_component (L : Subgroup G) (l : L) :
    sectionAction L (inclusion L.le_normalizer l) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  rw [sectionAction_apply]
  change QuotientGroup.mk' (pCore 2 L) (l * a * l⁻¹) =
    QuotientGroup.mk' (pCore 2 L) l * QuotientGroup.mk' (pCore 2 L) a *
      (QuotientGroup.mk' (pCore 2 L) l)⁻¹
  simp only [map_mul, map_inv]

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

end
