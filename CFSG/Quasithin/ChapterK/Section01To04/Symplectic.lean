module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Cover
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalOuter
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalRatios
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalSource
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorReduction

/-!
# The symplectic branch of Chapter K

The central cover, representation recognition, natural offender calculation,
and descended tensor geometry are assembled here. The two alternatives are
obtained from the actual central quotient and the source cubic-ratio bound;
the tensor branch retains the scalar-extension identification and its marked
Sylow equality actor. No model label is used in place of an action
intertwiner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
K.3.4, printed pp.456–457.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open scoped ENNReal

namespace CFSG.Quasithin.ChapterK.Symplectic

universe u v
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F]
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-! The source theorem is split into two small assembly lemmas so that the
central-cover facts are shared by both representation alternatives. -/

theorem source_natural_complete {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (hnat : letI := h.irreducible
      NaturalIdentification (F := F) (ρ.comp L.subtype)) :
    letI := h.irreducible
    center L = ⊥ ∧ IsSimpleGroup L ∧ Nonempty (L ≃* Sp F) ∧
      Module.finrank (ZMod 2) V = 4 * r ∧
      quadraticRatio ρ = (2 : ℝ≥0∞) / 3 ∧ offenderSubgroup ρ = L ∧
      (letI : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
       Function.Injective (extensionAction L hnat.groupEquiv.symm) ∧
         (∀ g : G, PreservesDiagram
           (extensionAction L hnat.groupEquiv.symm g)) ∧
         ∀ g : G, ∃ (x : Sp F) (σ : F ≃+* F),
           extensionAction L hnat.groupEquiv.symm g =
             MulAut.conj x * fieldAutomorphism σ) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
  obtain ⟨hc, hsimp, he⟩ := source_cover_isSimple h e
  obtain ⟨heq⟩ := he
  obtain ⟨hq, hgen, _⟩ := natural_conclusions h hF hr hnat
  have hdim := NaturalIdentification.finrank hF hnat
  have haut := natural_ambient_automorphisms h hF hr hnat
  exact ⟨hc, hsimp, ⟨heq⟩, hdim, hq, hgen, haut⟩

omit [Algebra (ZMod 2) F] in
theorem source_tensor_complete {K : GroupClass} (h : SourceHypothesis K ρ L)
    [IsIrreducible (ρ.comp L.subtype)]
    {s : ℕ} (hs : 0 < s) (e : L ⧸ center L ≃* Sp F)
    (a : Algebra (SchurField (ρ.comp L.subtype)) F)
    (ht : letI := h.irreducible
      letI := a
      TensorIdentification (ρ.comp L.subtype) F s) :
    letI := h.irreducible
    letI := a
    letI : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
    center L = ⊥ ∧ IsSimpleGroup L ∧ Nonempty (L ≃* Sp F) ∧
      Module.finrank (ZMod 2) V = 16 * s ∧
      2 < quadraticRatio ρ ∧ cubicRatio ρ = 2 ∧
      (∀ g : G, PreservesDiagram (extensionAction L ht.groupEquiv.symm g)) ∧
      ∀ (T : Sylow 2 G),
    ((T : Subgroup G).subgroupOf L).map ht.groupEquiv.toMonoidHom =
          unipotent →
        tensorPlaneActor ρ L ht ≤ T ∧
          IsElementaryTwo (tensorPlaneActor ρ L ht) ∧
          IsCubic ρ (tensorPlaneActor ρ L ht) ∧
          rank (tensorPlaneActor ρ L ht) = 6 * s ∧
          Module.finrank (ZMod 2) (fixedSpace ρ (tensorPlaneActor ρ L ht)) = 4 * s ∧
          fixedCodim ρ (tensorPlaneActor ρ L ht) = 12 * s ∧
          actionRatio ρ (tensorPlaneActor ρ L ht) = 2 ∧
          ∀ A : Subgroup G, IsElementaryTwo A → A ≤ T →
            actionRatio ρ A ≤ 2 → A = tensorPlaneActor ρ L ht := by
  let : Algebra (SchurField (ρ.comp L.subtype)) F := a
  let : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
  obtain ⟨hc, hsimp, he⟩ := source_cover_isSimple h e
  obtain ⟨heq⟩ := he
  have hg := tensor_source_geometry h hs ht
  have hdiag : ∀ g : G, PreservesDiagram (extensionAction L ht.groupEquiv.symm g) :=
    fun g => ht.preservesDiagram ρ L hs g
  exact ⟨hc, hsimp, ⟨heq⟩, hg.1, hg.2.1, hg.2.2.1, hdiag, hg.2.2.2⟩

/-! Complete K.3.4. The disjunction is the recognition conclusion itself;
the numerical and offender statements are attached to the corresponding
actual identification. -/

theorem source_complete {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F) :
    letI := h.irreducible
    center L = ⊥ ∧ IsSimpleGroup L ∧ Nonempty (L ≃* Sp F) ∧
      ((∃ hnat : NaturalIdentification (F := F) (ρ.comp L.subtype),
          Module.finrank (ZMod 2) V = 4 * r ∧
          quadraticRatio ρ = (2 : ℝ≥0∞) / 3 ∧ offenderSubgroup ρ = L ∧
          (letI : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
           Function.Injective (extensionAction L hnat.groupEquiv.symm) ∧
             (∀ g : G, PreservesDiagram (extensionAction L hnat.groupEquiv.symm g)) ∧
             ∀ g : G, ∃ (x : Sp F) (σ : F ≃+* F),
               extensionAction L hnat.groupEquiv.symm g =
                 MulAut.conj x * fieldAutomorphism σ)) ∨
       ∃ s : ℕ, 0 < s ∧ r = 2 * s ∧
         ∃ a : Algebra (SchurField (ρ.comp L.subtype)) F,
           ∃ ht : letI := a; TensorIdentification (ρ.comp L.subtype) F s,
             (letI : L.Normal := h.fitting ▸ (generalizedFitting_normal (G := G))
              Module.finrank (ZMod 2) V = 16 * s ∧
             2 < quadraticRatio ρ ∧ cubicRatio ρ = 2 ∧
             (∀ g : G, PreservesDiagram (extensionAction L ht.groupEquiv.symm g)) ∧
             ∀ (T : Sylow 2 G),
               ((T : Subgroup G).subgroupOf L).map ht.groupEquiv.toMonoidHom = unipotent →
               tensorPlaneActor ρ L ht ≤ T ∧
                 IsElementaryTwo (tensorPlaneActor ρ L ht) ∧
                 IsCubic ρ (tensorPlaneActor ρ L ht) ∧
                 rank (tensorPlaneActor ρ L ht) = 6 * s ∧
                 Module.finrank (ZMod 2) (fixedSpace ρ (tensorPlaneActor ρ L ht)) = 4 * s ∧
                 fixedCodim ρ (tensorPlaneActor ρ L ht) = 12 * s ∧
                 actionRatio ρ (tensorPlaneActor ρ L ht) = 2 ∧
                 ∀ A : Subgroup G, IsElementaryTwo A → A ≤ T →
                   actionRatio ρ A ≤ 2 → A = tensorPlaneActor ρ L ht)) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  rcases source_cover_isSimple h e with ⟨hc, hsimp, ⟨heq⟩⟩
  rcases Recognition.source_natural_or_tensor h hr hF e with hnat | htensor
  · obtain ⟨hnat⟩ := hnat
    have hn := source_natural_complete h hr hF e hnat
    rcases hn with ⟨hc, hsimp, heq, hdim, hq, hgen, haut⟩
    exact ⟨hc, hsimp, heq, Or.inl ⟨hnat, hdim, hq, hgen, haut⟩⟩
  · obtain ⟨s, hs, hrs, a, ht⟩ := htensor
    let : Algebra (SchurField (ρ.comp L.subtype)) F := a
    obtain ⟨ht⟩ := ht
    have hgeom := source_tensor_complete h hs e a ht
    rcases hgeom with ⟨hc, hsimp, heq, hdim, hq, hcube, hdiag, hmarked⟩
    exact ⟨hc, hsimp, heq,
      Or.inr ⟨s, hs, hrs, a, ht, hdim, hq, hcube, hdiag, hmarked⟩⟩

end CFSG.Quasithin.ChapterK.Symplectic
