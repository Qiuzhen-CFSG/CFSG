module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.FivePairSource
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NaturalSource

/-!
# The paired-five alternative on the literal chief image

Pass the original irreducible chief action to its faithful image. The reduced
image inherits minimal parabolicity, and the original marked B.6.9 pair gives
the full natural S₅ wreath action with the offender subgroup exactly its base.
Bundling the marking avoids expanding its nested quotient construction inside
the original qrc chief-factor consumer.

Source: Aschbacher–Smith, 3.1.9(5) and15.1.12(3), pp.577–578,1090.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource BinaryPermutation
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The actual paired-five marking supplied by B.6.9. -/
def ChiefFivePairMarkedSection (ρ : Representation (ZMod 2) D W) : Prop :=
  ∃ d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
    Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5)))

/-- The literal original chief image has its complete wreath action and marked base. -/
theorem minimalParabolic_chief_five_pair_of_marked
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hmark : ChiefFivePairMarkedSection (imageRepresentation ρ)) :
    ∃ e : ActionEquiv (imageRepresentation ρ) FivePair.wreathRepresentation,
      (offenderSubgroup (imageRepresentation ρ)).map e.groupEquiv.toMonoidHom =
        FivePair.baseSubgroup := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let := imageRepresentation_irreducible ρ (inferInstance : IsIrreducible ρ)
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨A,hA⟩ := hff
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  obtain ⟨d,⟨c⟩⟩ := hmark
  obtain ⟨e,hbase,_⟩ := source_two_factor_five_whole_action _ (imageRepresentation_injective ρ)
    (S.mapSurjective hq) (minimalParabolic_reduced_image S hS q hq hc hn).2
    hff hc d c
  exact ⟨e,hbase⟩

end CFSG.Quasithin.ChapterB
