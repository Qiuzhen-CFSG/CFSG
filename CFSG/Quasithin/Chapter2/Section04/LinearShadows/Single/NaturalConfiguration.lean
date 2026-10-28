module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.NaturalCoordinates

/-!
# The actual natural shadow retains its internal Sylow marking

Construct the original C.5 configuration and escaping conjugate, then exclude
the cubic alternative using the specified natural block. The returned marking
therefore supplies the literal internal-action identity used in 2.4.8(5).

Source: Aschbacher--Smith 2.4.5 and 2.4.8, printed pp.528--530.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_natural_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ}
    (hK : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    ∃ _c : OriginalHypotheses d.H M₀ (d.block.map d.H.subtype)
        ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype),
      ∃ (F : Type) (_ : Field F),
        ∃ h : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
            (d.block.map d.H.subtype) F,
          h.coordinates.IsInternal ∧ ∃ x ∈ M₀,
            ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
              centralizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST hsingle
    (Or.inl ⟨n,hK⟩) M₀ hSM hMT hi
  exact ⟨c,F,hF,h,h.internal_of_linear hK,x,hx,hnc⟩

end CFSG.Quasithin.Chapter2
