module

public import Theory.Alternating.OddCentralCovers
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.CenterSections
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion

/-!
# Alternating covers in the noncentral branch of B.1.13

The imported covering theorem proves that a component with alternating central
quotient and trivial ambient two-core is Aₘ, the concrete hexacode 3.A₆, or the
constructed universal-cover quotient 3.A₇. It derives oddness of the center
from ambient subnormality and uses the actual Schur-cover calculations.

The section adapter below composes the representation results through the
literal inclusion L ↪ H and action on I/C_I(L). For a best offender A with
[L,A] = L, the center-detecting section construction supplies a faithful
irreducible FF section in the cubic-center case. The intrinsic triple-seven
exclusion eliminates 3.A₇. Thus the final theorems give actual isomorphisms
to Aₘ or the hexacode 3.A₆, with no additional representation premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
printed pp. 73–74 (PDF pp. 84–85).
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
universe u v

/-- Application of the intrinsic exclusion to an actual central section.
The embedding is L ↪ H; normality follows from H normalizing L. -/
theorem not_triple_seven_of_faithful_section
    (hexclude : SevenFFExclusion.{u, u, v})
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7)) (hc : Nat.card (center L) = 3)
    (hs : HasFaithfulIrreducibleFFSection ρ L) : False := by
  obtain ⟨H, I, hLH, hI, hHI, hHN, hff, hf⟩ := hs
  let σ := centralSectionRepresentation ρ L H I hHI hHN
  have hn : (inclusion hLH).range.Normal := by
    rw [inclusion_range]
    exact (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have he := centralSection_comp_inclusion ρ L H hLH I hI.choose hHI hHN
  apply hexclude (inclusion hLH) (inclusion_injective hLH) hn σ ⟨e⟩ hc _ _ hff
  · rwa [he]
  · rw [he]
    exact hI.choose_spec.2

/-- The alternating-cover conclusion conditional on its two explicit
representation inputs. The unconditional source assembly must construct the
faithful section and prove the intrinsic exclusion before applying this result. -/
theorem alternating_or_hexacode_of_faithful_sections
    (hexclude : SevenFFExclusion.{u, u, v})
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hcore : pCore 2 G = ⊥)
    (L : Subgroup G) (hL : IsComponent G L) (m : ℕ) (hm : 5 ≤ m)
    (e : L ⧸ center L ≃* alternatingGroup (Fin m))
    (hsections : Nat.card (center L) = 3 → HasFaithfulIrreducibleFFSection ρ L) :
    Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let := hL.2
  rcases GLS3.Chapter5.OddCentralCovers.component_alternating_cover_alternatives
      hcore L hL m hm e with ha | ⟨_, hs⟩ | ⟨rfl, hc, _⟩
  · exact Or.inl ha
  · exact Or.inr hs
  · exact (not_triple_seven_of_faithful_section hexclude ρ L e hc (hsections hc)).elim

/-- The alternating-cover step of B.1.13. The cubic-center section and the
triple-seven exclusion are both constructed from the stated hypotheses.
The exceptional isomorphism is to the genuine perfect triple cover of A₆,
and can occur only when the given alternating quotient has degree six. -/
theorem alternating_cover_alternatives
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (L A : Subgroup G) (hL : IsComponent G L)
    (hA : IsBestOffender ρ A) (hLA : ⁅L, A⁆ = L)
    (m : ℕ) (hm : 5 ≤ m) (e : L ⧸ center L ≃* alternatingGroup (Fin m)) :
    Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      (m = 6 ∧ Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms)) := by
  let := hL.2
  rcases GLS3.Chapter5.OddCentralCovers.component_alternating_cover_alternatives
      hcore L hL m hm e with ha | hs | ⟨rfl, hc, _⟩
  · exact Or.inl ha
  · exact Or.inr hs
  · have hsection := hasFaithfulIrreducibleFFSection_of_cubic_center
      ρ hfaith L A hc hLA hA
    exact (not_triple_seven_of_faithful_section
      SevenExclusion.sevenFFExclusion ρ L e hc hsection).elim

/-- A component with alternating central quotient, moved by a best offender,
is an alternating group or the concrete hexacode triple cover of A₆. -/
theorem alternating_or_hexacode
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (L A : Subgroup G) (hL : IsComponent G L)
    (hA : IsBestOffender ρ A) (hLA : ⁅L, A⁆ = L)
    (m : ℕ) (hm : 5 ≤ m) (e : L ⧸ center L ≃* alternatingGroup (Fin m)) :
    Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) :=
  (alternating_cover_alternatives ρ hfaith hcore L A hL hA hLA m hm e).imp_right And.right

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
