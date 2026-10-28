module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.CaseConclusion
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Ambient
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceContainment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceCommutator

/-!
# The original invariant p > 3 source branch of Proposition 1.3.4

The actual LocalInput, SQTK overgroup, Sylow subgroup and detected normal
component supply the strengthened invariant input. Genuine A/C give P,X ≤ L;
the detected orbit commutator gives [L,P] = L. The marked faithful section
then satisfies every hypothesis of the earlier A.3.15 prime-subgroup theorem.
Its full case split has been proved to leave only the linear and symplectic
rows. Transport returns the actual original P ≃ E_(p²), whole L/O₂(L) model,
field restrictions and cyclicity of the actual Aut_T(P).

The final consumer reaches the original `Conclusion` on G and its original
subgroups. No placement, action, cover, plane or model-output hypothesis is
retained. The universal A/C and `A315PrimeSubgroupTheorem` remain explicitly
earlier-source inputs; this module does not prove A.3.15 case existence.
The p = 3 and exchanged-component branches are separate source arguments.

Source: Aschbacher–Smith Proposition 1.3.4, printed pp.510–511, invariant
p > 3 case, using A.3.6, A.3.15 and I.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u
variable
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {T X P H L : Subgroup G}
include hA hC

/-- Every earlier A.3.15 hypothesis holds in the literal faithful section. -/
theorem SylowInput.a315Input (h : SylowInput KnownSimple.IsKnownSimple p T X P H L)
    (hp : 3 < p) : OddCartan.AmbientInput KnownSimple.IsKnownSimple
      (SourceTransport.component h) (SourceTransport.complement h) (SourceTransport.sylow h) p := by
  let : Fact p.Prime := ⟨h.prime⟩
  have hb := (SourceTransport.complement_pairAction h hA hC hp).oddComplement
  have hres : pResidual 3 (SourceTransport.complement h) = ⊤ := by
    apply (pResidual_eq_top_iff 3 _).mpr
    intro N hN hQ
    let _ := hN
    have hc : Nat.Coprime p 3 := (Nat.coprime_primes h.prime (by decide)).mpr (by omega)
    have hd := (hb.isPGroup.to_quotient N).to_subgroup ⊤ |>.disjoint_of_coprime
      (hQ.to_subgroup ⊤) hc
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (hd.le_bot ⟨mem_top _, mem_top _⟩)
  refine ⟨SourceTransport.ambient_sqtk h hA, SourceTransport.component_fitting h,
    SourceTransport.component_simple h, h.prime, h.odd, hp, hb.isPGroup,
    SourceTransport.complement_le_component h, SourceTransport.complement_permute_sylow h, ?_⟩
  let : Nontrivial (SourceTransport.complement h) :=
    not_subsingleton_iff_nontrivial.mp (fun hs => by
      let _ := hs
      exact hb.not_isCyclic inferInstance)
  rw [hres]
  exact top_ne_bot

/-- The complete invariant p > 3 alternative, retaining only the genuine
universal earlier A/C and A.3.15 source implications. -/
theorem SylowInput.alternatives_of_sources (h315 : A315PrimeSubgroupTheorem.{u})
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p) :
    Alternatives p T P L := by
  let hi := h.a315Input hA hC hp
  let : (SourceTransport.component h).Normal := SourceTransport.component_normal h
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  have hc := h315 (SourceTransport.Ambient h) (SourceTransport.component h)
    (SourceTransport.complement h) (SourceTransport.sylow h) p hi
  obtain ⟨hplane, hmodel⟩ := alternatives_of_A315_cases
    (SourceTransport.simpleComponentEquiv h) hi
    (SourceTransport.complement_pairAction h hA hC hp)
    (SourceTransport.component_centralizer h) hc
  let hf := SourceTransport.complementMap_injective h hA hC hp
  let e := SourceTransport.complementEquiv (SourceTransport.ambientMap h)
    (h.complement_le_component.trans le_sup_left) hf
  refine ⟨hplane.map (fun j => e.trans j), Or.inr ⟨h.component_invariant, ?_⟩⟩
  rcases hmodel with hl | ⟨hs, ha⟩
  · exact Or.inl hl
  · refine Or.inr (Or.inl ⟨hs, ?_⟩)
    rw [SourceTransport.sylow_eq_image] at ha
    exact SourceTransport.automizer_cyclic_of_image (SourceTransport.ambientMap h)
      (h.complement_le_component.trans le_sup_left) le_sup_right hf ha

/-- The literal original detected normal component supplies every strengthened
input field; containment is proved by the earlier source branch. -/
theorem sourceInput_of_detected_normal
    (h : LocalInput p T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) (hL : ComponentDetection P H L)
    (hn : (L.subgroupOf H).Normal) :
    SylowInput KnownSimple.IsKnownSimple p T X P H L := by
  have hi : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hL.mem.1).mp hn)
  have horbit : componentOrbit L T = L := by
    apply le_antisymm _ (le_componentOrbit L T)
    exact iSup_conjugates_le_of_le_normalizer L T L le_rfl hi
  have hcomm := h.detected_component_orbit_commutator_source hH hT hL
  rw [horbit] at hcomm
  exact ⟨h, hH, hT, hL.mem, hn, hL.quasisimple, hi,
    (h.complement_and_X_le_normal_component hA hC hH hL hn).1, hcomm⟩

/-- Original-source consumer for the invariant large-prime branch of 1.3.4. -/
theorem alternatives_of_detected_normal (h315 : A315PrimeSubgroupTheorem.{u})
    (h : LocalInput p T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) (hL : ComponentDetection P H L)
    (hn : (L.subgroupOf H).Normal) (hp : 3 < p) : Alternatives p T P L :=
  (sourceInput_of_detected_normal hA hC h hH hT hL hn).alternatives_of_sources hA hC h315 hp

/-- The surviving invariant branch reaches the original proposition's full
conclusion on the original ambient subgroups, not merely a quotient model. -/
theorem conclusion_of_detected_normal (h315 : A315PrimeSubgroupTheorem.{u})
    (h : LocalInput p T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) (hL : ComponentDetection P H L)
    (hn : (L.subgroupOf H).Normal) (hp : 3 < p) : Conclusion p T X P H := by
  refine Or.inr ⟨L, hL.mem, hL.quasisimple, ?_,
    alternatives_of_detected_normal hA hC h315 h hH hT hL hn hp⟩
  exact (h.complement_and_X_le_normal_component hA hC hH hL hn).2.trans (le_componentOrbit L T)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
