module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors

/-!
# Applying the intrinsic actor calculation to the source centralizers

The intrinsic permitted-actor hypotheses now discharge `ActorWitness` in
`ExceptionalActors.centralizer_eq_of_actorWitness`. The plane and actor are
the literal `quotientPlane` and `actorImage` attached to the given conjugation
quotient model. The checked conclusion is transported through C_G(v)/⟨v⟩.

The earlier source construction of the permitted actor remains with the
exceptional-branch assembly owner; it is not assumed to follow merely from
the existence of the plane model.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed pp.932–933.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {L V K U : Subgroup G} (s : Marking L V)

/-- The permitted source actor suffices for the ambient centralizer equality. -/
theorem centralizer_eq_of_permittedActor
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L (markedV s) ≤ K)
    (hlU : ⁅V, Lv L (markedV s)⁆ ≤ U) (S : Sylow 2 A7)
    (h : PermittedActor ρ (quotientPlane s m hlU) S (actorImage s m hLK)) :
    U ⊓ centralizer (Lv L (markedV s) : Set G) = U ⊓ centralizer (K : Set G) :=
  centralizer_eq_of_actorWitness s ρ hρ hdim m hLK hlU
    (h.actorWitness (quotientPlane_finrank s m hlU hLK))

/-- The same deduction on the actual checked quotient centralizers. -/
theorem checked_centralizer_eq_of_permittedActor
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L (markedV s) ≤ K)
    (hlU : ⁅V, Lv L (markedV s)⁆ ≤ U) (hv : markedV s ^ 2 = 1)
    (S : Sylow 2 A7)
    (h : PermittedActor ρ (quotientPlane s m hlU) S (actorImage s m hLK)) :
    checkedImage (markedV s) U ⊓
      centralizer (checkedImage (markedV s) (Lv L (markedV s)) : Set (Gcheck (markedV s))) =
    checkedImage (markedV s) U ⊓
      centralizer (checkedImage (markedV s) K : Set (Gcheck (markedV s))) :=
  checked_centralizer_eq_of_actorWitness s ρ hρ hdim m hLK hlU hv
    (h.actorWitness (quotientPlane_finrank s m hlU hLK))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
