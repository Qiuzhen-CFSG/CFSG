module
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient

/-!
# Faithful maximal quotients from an irreducible moved plane

For a simple perfect normal component generating the whole module, an
irreducible moved plane makes the component-fixed space the unique maximal
submodule. Every maximal quotient is therefore faithful. The top-section
comparison retains literal quotient representatives for chief catalogues.
Source application: Aschbacher–Smith13.5.21, printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) E W)

private theorem coatom_eq_fixed (L A : Subgroup E) [L.Normal]
    (t : E) (p : MovedPlane ρ A t) (hc : ⁅L,zpowers t⁆ = L)
    (hg : subspaceCommutator ρ ⊤ L = ⊤) (hn : ¬ L ≤ ρ.ker)
    (N : Subrepresentation ρ) (hN : IsCoatom N) :
    N = fixedSubrepresentation ρ L := by
  have hfixed := p.central_isCoatom ρ L A t hc hg hn
  have hle : N ≤ fixedSubrepresentation ρ L := by
    rcases p.eq_top_or_central ρ L A t hc hg N with ht | hh
    · exact (hN.ne_top ht).elim
    · exact hh
  apply le_antisymm hle
  by_contra hh
  exact hfixed.ne_top (hN.2 _ (lt_of_le_not_ge hle hh))

/-- Every maximal section is faithful once the moved plane makes the fixed
space the unique maximal submodule and the simple component generates the module. -/
theorem MovedPlane.coatom_quotient_faithful (L A : Subgroup E) [L.Normal]
    [IsSimpleGroup L] [Group.IsPerfect L] (t : E) (p : MovedPlane ρ A t)
    (hc : ⁅L,zpowers t⁆ = L) (hg : subspaceCommutator ρ ⊤ L = ⊤)
    (hρ : Function.Injective ρ) (hn : ¬ L ≤ ρ.ker)
    (N : Subrepresentation ρ) (hN : IsCoatom N) :
    Function.Injective N.quotientRepresentation := by
  have he := coatom_eq_fixed ρ L A t p hc hg hn N hN
  subst N
  exact simple_fixedQuotient_faithful ρ L hρ hn hg

/-- The top section and the usual quotient use the same representatives. -/
def topSectionEquiv (N : Subrepresentation ρ) :
    ((⊤ : Subrepresentation ρ).toSubmodule ⧸ (sectionLower ρ N ⊤).toSubmodule) ≃ₗ[ZMod 2]
      (W ⧸ N.toSubmodule) :=
  Submodule.Quotient.equiv _ _ (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) W) ≃ₗ[ZMod 2] W)
    (by ext w; constructor
        · rintro ⟨v,hv,rfl⟩; exact hv
        · intro hw; exact ⟨⟨w,Submodule.mem_top⟩,hw,rfl⟩)

theorem topSectionEquiv_intertwines (N : Subrepresentation ρ) (g : E) (w) :
    topSectionEquiv ρ N (sectionRepresentation ρ N ⊤ g w) =
      N.quotientRepresentation g (topSectionEquiv ρ N w) := by
  obtain ⟨w,rfl⟩ := (sectionLower ρ N ⊤).toSubmodule.mkQ_surjective w
  rfl

theorem top_section_faithful (N : Subrepresentation ρ)
    (hf : Function.Injective N.quotientRepresentation) :
    Function.Injective (sectionRepresentation ρ N ⊤) := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro w
  obtain ⟨w,rfl⟩ := (topSectionEquiv ρ N).surjective w
  rw [← topSectionEquiv_intertwines,← topSectionEquiv_intertwines,he]

end Representation.BinaryOffender
