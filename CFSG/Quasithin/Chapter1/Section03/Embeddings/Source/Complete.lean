module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Three
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.ClassicalReduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.Three

/-!
# The complete adequate intrinsic embedding theorem

For an invariant component, the complete large-prime source sieve leaves the
odd degree-three case, whose original pair action gives the linear plane.
The central-quotient lifting theorem returns the model of the whole component.
Component detection and the exchanged-component theorem then assemble this
with the complete three-complement theorem. Every earlier A/C input is
instantiated for the full known-simple catalogue. The adequate conclusion
retains the Held case allowed by the original intrinsic hypotheses.

Source: Aschbacher–Smith Proposition 1.3.4, pp.509–511, with the Held
correction recorded in docs/quasithin-proof-basis.md.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u

private theorem large_alternatives {G : Type u} [Group G] [Finite G]
    {p : ℕ} {T X P H L : Subgroup G}
    (h : InvariantLarge.SylowInput KnownSimple.IsKnownSimple p T X P H L)
    (hp : 3 < p) : Alternatives p T P L := by
  let hA := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases h.alternatives_or_odd_three hA hC hp with ha | ⟨q,hq,ho,unitary,hm⟩
  · exact ha
  · obtain ⟨hplane,hm⟩ := InvariantLarge.A315Source.OddSource.alternative_of_odd_three
      (h.a315Input hA hC hp)
      (InvariantLarge.SourceTransport.complement_pairAction h hA hC hp) hq ho unitary hm
    let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
    have hlinear : LinearThreeModel p (XiQuotient L) := by
      apply InvariantLarge.linearThreeModel_of_central_quotient h.prime hp
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact ⟨F,inferInstance,inferInstance,hF,
        ⟨(InvariantLarge.SourceTransport.simpleComponentEquiv h).trans e⟩⟩
    let hf := InvariantLarge.SourceTransport.complementMap_injective h hA hC hp
    let e := InvariantLarge.SourceTransport.complementEquiv
      (InvariantLarge.SourceTransport.ambientMap h)
      (h.complement_le_component.trans le_sup_left) hf
    exact ⟨hplane.map (fun j => e.trans j),
      Or.inr ⟨h.component_invariant, Or.inl hlinear⟩⟩

/-- The full adequate intrinsic conclusion follows from the original local,
SQTK and Sylow hypotheses; no earlier classification theorem is assumed. -/
theorem LocalInput.adequate_knownSimple {G : Type u} [Group G] [Finite G]
    {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) : AdequateConclusion p T X P H := by
  by_cases hp : p = 3
  · subst p
    exact h.adequate_three_knownSimple hH hT
  have hpgt : 3 < p := by
    have hge := h.prime.two_le
    obtain ⟨k,hk⟩ := h.odd
    omega
  let hA := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases h.normal_or_detected_containment hA hC hH hT with
    hn | ⟨L,hL,hn,hcomm,hP,hX⟩
  · exact Or.inl hn
  · refine Or.inr ⟨L,hL.mem,hL.quasisimple,hX,?_⟩
    by_cases hi : T ≤ normalizer L
    · have horbit : componentOrbit L T = L :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl hi)
          (le_componentOrbit L T)
      rw [horbit] at hn hcomm hP
      exact Or.inl (large_alternatives
        ⟨h,hH,hT,hL.mem,hn,hL.quasisimple,hi,hP,hcomm⟩ hpgt)
    · let hs : SwappedSylowInput KnownSimple.IsKnownSimple p T X P H L :=
        { toLocalInput := h
          sqtk := hH
          component := hL.mem
          quasisimple := hL.quasisimple
          orbit_normal := hn
          complement_le_orbit := hP
          orbit_commutator := hcomm
          noncentral := hL.noncentral_component_core
          not_invariant := hi
          sylow_two := hT }
      obtain ⟨he,hf,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
      exact Or.inl ⟨he,Or.inl ⟨hf,hm⟩⟩

/-- The complete source implication used by the actual Held-preserving
Chapter 15 assembly, specialized to the full known-simple catalogue. -/
theorem adequateLocalEmbeddingTheorem_knownSimple :
    AdequateLocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ p T X P H h hH hT
  exact h.adequate_knownSimple hH hT

end CFSG.Quasithin.Chapter1.XiEmbedding
