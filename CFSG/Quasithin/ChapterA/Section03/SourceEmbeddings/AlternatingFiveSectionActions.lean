module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSection
public import Theory.Representation.AlternatingSevenFiveSeed.Natural

/-!
# The original local A₅ section in a four-dimensional A₇ action

The actual image of the original local component is a Sylow-normalized A₅.
Restricting a faithful binary four-dimensional A₇ action to that same image
gives the natural SL₂(4) module. Pull the coordinates back through the literal
image map; the quotient marking remains the original map from L/O₂(L).

This is the four-dimensional action consumer of the alternating-seven row
of Aschbacher–Smith 10.2.9, printed pp.751–752, using C.1.24 and C.5.13.
The theorem takes the actual ambient representation, rather than merely
an abstract isomorphism type of its acting group.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

/-- A faithful ambient four-space restricts naturally through the original
local quotient, retaining the actual actor and the supplied A₅ marking. -/
theorem alternatingSeven_five_section_natural_four
    {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) M)
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) M = 4) :
    ∃ α : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL,
    ∃ l : M ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ (a : L) x,
        l (ρ (f a.val) x) =
          specialLinearNatural 2 (α (e (QuotientGroup.mk' (pCore 2 L) a))) (l x) := by
  let d := alternatingGroup.SevenFiveSection.imageFiveEquiv f L hk e
  obtain ⟨eB,l,hl⟩ := AlternatingSevenFiveSeed.natural_restriction ρ hρ hd
    (L.map f) d (S.mapSurjective hf)
    (alternatingSeven_five_section_image_normalized f hf hks S L hL hk e)
  refine ⟨d.symm.trans eB,l,?_⟩
  intro a x
  change l (ρ (f a.val) x) =
    specialLinearNatural 2 (eB (d.symm (e (QuotientGroup.mk' (pCore 2 L) a)))) (l x)
  rw [← alternatingGroup.SevenFiveSection.imageFiveEquiv_apply f L hk e a]
  have hh := hl ((f.subgroupMap L) a) x
  have he : ((f.subgroupMap L) a).val = f a.val := rfl
  rw [he] at hh
  simpa only [d, MulEquiv.symm_apply_apply] using hh

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
