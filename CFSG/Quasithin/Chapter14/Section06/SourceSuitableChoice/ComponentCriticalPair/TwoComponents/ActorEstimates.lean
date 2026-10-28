module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Selection
public import Theory.Representation.BinaryOffender.QuadraticPairPermutation.Stability

/-!
# A terminal quadratic actor cannot interchange the two components

The literal quotient action is faithful by F.9.2. The two disjoint component
supports and the fixed supplement therefore satisfy the quadratic pair
permutation theorem. An exchanging actor would have rank one and move at least
six dimensions, contrary to its quadratic budget. The support-stabilizer
markings then give normalization of the actual ambient components.

This proves the normalization step of 14.6.24(3) from the genuine support
decomposition. Point placement and the subsequent Sylow contradiction remain
with qt-e-suitable-component-marking. The support decomposition is supplied by
qt-e-suitable-component-supports; no component exclusion is asserted here.
Source: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1039.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]

/-- Faithfulness on the actual quotient and the two support markings force
the selected actor to normalize both original component subgroups. -/
theorem QuadraticEndpoint.normalizes_of_large_support_pair
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (p : QuadraticEndpoint h ρ) (hb : 3 ≤ h.b)
    (s : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hspan : I ⊔ J ⊔ fixedSpace ρ ⊤ = ⊤)
    (hlarge : 2 < Module.finrank (ZMod 2) I)
    (hperm : ∀ a : Source.Hstar D.H,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I))
    (K Kplus : Subgroup G)
    (hK : (normalizer (K : Set G)).subgroupOf D.H =
      (subspaceStabilizer ρ I).comap (QuotientGroup.mk' (pCore 2 D.H)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf D.H =
      (subspaceStabilizer ρ J).comap (QuotientGroup.mk' (pCore 2 D.H))) :
    p.endpoint.conjugate D.UH ≤ normalizer (K : Set G) ∧
      p.endpoint.conjugate D.UH ≤ normalizer (Kplus : Set G) := by
  let A := Source.starImage D.H (p.endpoint.conjugate D.UH)
  let : IsElementaryAbelian 2 A := p.member.1.2
  have hp := quadratic_preserves_large_pair ρ
    (f9_section_faithful D h (criticalSection h s)) I J hd hspan hlarge A
    p.member.2.1 p.member.2.2 (fun a _ => hperm a)
  have hAH : p.endpoint.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (p.endpoint.large_le hb)
  have hm (a : G) (ha : a ∈ p.endpoint.conjugate D.UH) :=
    hp (QuotientGroup.mk' (pCore 2 D.H) ⟨a,hAH ha⟩)
      (mem_map_of_mem (QuotientGroup.mk' (pCore 2 D.H)) ha)
  constructor
  · intro a ha
    have he : (⟨a,hAH ha⟩ : D.H) ∈ (subspaceStabilizer ρ I).comap
        (QuotientGroup.mk' (pCore 2 D.H)) :=
      (subspace_map_eq_iff ρ I _).mp (hm a ha).1
    rwa [←hK] at he
  · intro a ha
    have he : (⟨a,hAH ha⟩ : D.H) ∈ (subspaceStabilizer ρ J).comap
        (QuotientGroup.mk' (pCore 2 D.H)) :=
      (subspace_map_eq_iff ρ J _).mp (hm a ha).2
    rwa [←hKplus] at he

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original H=Mc application to the two six-dimensional component supports.
The source two-core map and the selected endpoint are unchanged. -/
theorem source_quadratic_actor_normalizes_components
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (p : QuadraticEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ)
    (s : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hspan : I ⊔ J ⊔ fixedSpace ρ ⊤ = ⊤) (hdim : Module.finrank (ZMod 2) I = 6)
    (hperm : ∀ a : Source.Hstar Mc,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I))
    (K Kplus : Subgroup G)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ I).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ J).comap (QuotientGroup.mk' (pCore 2 Mc))) :
    p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (K : Set G) ∧
      p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (Kplus : Set G) := by
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact p.normalizes_of_large_support_pair hb s I J hd hspan (by omega) hperm K Kplus hK hKplus

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
