module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Intrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalApplications
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.SourceMarking

/-!
# Exceptional A₇ actors: quotient-plane construction and centralizer transport

The exceptional-block predicate supplies the faithful binary four-space and
its actual conjugation quotient. The A₅ marking then supplies the plane from
l=[V,Lᵥ], with proved dimension, commutator and restricted fixed space.
A single three-cycle or an involution fixing that plane pointwise completes
the whole-actor fixed-space calculation. The resulting centralizer comparison
is transported through the literal quotient C_G(v)/⟨v⟩.

This is a conditional source reduction. The three-actor catalogue and the
source construction of `PermittedActor`, including the seed commutator bound,
remain prerequisites. In particular `ActorWitness` is not yet derived for
every source actor. Final exceptional-branch assembly belongs to this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed pp.932–933.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {L V K U : Subgroup G} (s : Marking L V)

/-- The full actor calculation feeds the actual ambient quotient centralizer. -/
theorem centralizer_eq_of_actorWitness
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L (markedV s) ≤ K)
    (hlU : ⁅V, Lv L (markedV s)⁆ ≤ U)
    (hwitness : ActorWitness ρ (quotientPlane s m hlU) (actorImage s m hLK)) :
    U ⊓ centralizer (Lv L (markedV s) : Set G) = U ⊓ centralizer (K : Set G) := by
  apply m.centralizer_eq _ hLK
  intro w hw
  refine fixed_eq_zero_of_actorWitness ρ hρ hdim (quotientPlane s m hlU)
    (quotientPlane_finrank s m hlU hLK) (actorImage s m hLK) ?_ hwitness w ?_
  · intro x hx hfixed
    exact quotientPlane_fixed_eq_zero s m hlU hLK x hx
      (fun d => hfixed ⟨m.actor (inclusion hLK d), ⟨d, rfl⟩⟩)
  · rintro ⟨_, d, rfl⟩
    exact hw d

/-- Pass the same actor calculation to the literal checked quotient. -/
theorem checked_centralizer_eq_of_actorWitness
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L (markedV s) ≤ K)
    (hlU : ⁅V, Lv L (markedV s)⁆ ≤ U) (hv : markedV s ^ 2 = 1)
    (hwitness : ActorWitness ρ (quotientPlane s m hlU) (actorImage s m hLK)) :
    checkedImage (markedV s) U ⊓
      centralizer (checkedImage (markedV s) (Lv L (markedV s)) : Set (Gcheck (markedV s))) =
    checkedImage (markedV s) U ⊓
      centralizer (checkedImage (markedV s) K : Set (Gcheck (markedV s))) :=
  checked_centralizer_eq_of_ambient L K U (markedV s) hLK hv
    (centralizer_eq_of_actorWitness s ρ hρ hdim m hLK hlU hwitness)

/-- Construct the actual exceptional block representation and its marked plane.
Only the earlier seed commutator bound remains as a placement input; the
plane's injectivity, dimension, full commutator and local fixedness are proved. -/
theorem exceptionalSeven_planeModel
    (h : IsExceptionalA7Block K) (e : (K ⧸ pCore 2 K) ≃* A7)
    (hLK : Lv L (markedV s) ≤ K)
    (hz : ⁅zpowers (markedZ s), K⁆ ≤ (blockU K).map K.subtype) :
    letI := h.1.module_elementary
    ∃ ρ : Representation (ZMod 2) A7 (Additive (BlockModule K)),
      Function.Injective ρ ∧ Module.finrank (ZMod 2) (Additive (BlockModule K)) = 4 ∧
      ∃ m : ConjugationQuotientModel K ((blockU K).map K.subtype) ρ,
        m.actor = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) ∧
        ∃ P : Submodule (ZMod 2) (Additive (BlockModule K)),
          Module.finrank (ZMod 2) P = 2 ∧
          (∀ w, w ∈ P ↔ ∃ u : (blockU K).map K.subtype,
            (u : G) ∈ ⁅V, Lv L (markedV s)⁆ ∧ (m.quotient u).toAdd = w) ∧
          BinaryOffender.subspaceCommutator ρ P (actorImage s m hLK) = P ∧
          ∀ w ∈ P, (∀ d : Lv L (markedV s),
            ρ (m.actor (inclusion hLK d)) w = w) → w = 0 := by
  let := h.1.module_elementary
  obtain ⟨ρ, hρ, hdim, m, he⟩ := exceptionalSeven_quotientModel K h e
  have hlU := moved_le_of_seed s hLK hz
  exact ⟨ρ, hρ, hdim, m, he, quotientPlane s m hlU,
    quotientPlane_finrank s m hlU hLK, mem_quotientPlane_iff_ambient s m hlU,
    quotientPlane_commutator s m hlU hLK, quotientPlane_fixed_eq_zero s m hlU hLK⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
