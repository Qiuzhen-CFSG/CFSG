module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers

/-!
# Alternating covers for the component selected in B.1.13

The local commutator hypothesis K = [K,J_P(T)] and normalization of the
selected component L by J_P(G) supply a best offender A with [L,A] = L.
The alternating-cover theorem then identifies L with the actual alternating
group or the hexacode triple cover of A₆. The only recognition premise is
the given isomorphism from L/Z(L) to Aₘ; the separate general recognition
branch supplies it in the full B.1.13 assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
printed pp. 73–74 (PDF pp. 84–85).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition
open Subgroup Theory.GroupTheory Representation.BinaryOffender

/-- The alternating branch for the actual component selected by the local
offender commutator in B.1.13. No section or FF-exclusion witness is assumed. -/
theorem alternating_cover_of_local_commutator
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (K L T : Subgroup G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆)
    (hN : offenderSubgroup ρ ≤ normalizer (L : Set G))
    (m : ℕ) (hm : 5 ≤ m) (e : L ⧸ center L ≃* alternatingGroup (Fin m)) :
    Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      (m = 6 ∧ Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms)) := by
  obtain ⟨A, hA, _, hLA⟩ := exists_bestOffender_commutator ρ K L T hL hLK hK hN
  exact AlternatingCovers.alternating_cover_alternatives
    ρ hfaith hcore L A hL hA hLA m hm e

end CFSG.Quasithin.ChapterB.ComponentRecognition
