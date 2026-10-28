module

public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteCenters
public import Theory.GroupTheory.EmbeddedCoreCentralizer
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.CoreCandidates

/-!
# Transporting the source centralizer chain to the literal core preimage

The coordinate mark is the intrinsic core center in both models. Its exact
image makes the source central quotient embed faithfully; self-centralization
then pulls back to the quotient used by CoreCandidates. The full-Ree omega
exclusion and the Tits lattice give precisely the two surviving alternatives.
Source: Aschbacher--Smith 14.2.21, chain (*), printed pp.988--989.
-/

@[expose] public section
open Subgroup ReeTwo.ParabolicConcrete ReeTwo.Centralizer
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction

/-- Self-centralization modulo a specified normal subgroup, with the normality
proof bundled solely to make the quotient group available. -/
def QuotientCentralizerBound {M : Type*} [Group M] (Q Z : Subgroup M) : Prop :=
  ∃ (_ : Z.Normal), centralizer (Q.map (QuotientGroup.mk' Z) : Set (M ⧸ Z)) ≤
    Q.map (QuotientGroup.mk' Z)

abbrev reeZ {M : Type*} [Group M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) : Subgroup M :=
  zpowers (i (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)))

abbrev titsZ {M : Type*} [Group M]
    (i : Tits.ExceptionalParabolics.first →* M) : Subgroup M :=
  zpowers (i (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)))

private theorem pullback {A M : Type*} [Group A] [Group M]
    (i : A →* M) (hi : Function.Injective i) (P : Subgroup A)
    (Q Z : Subgroup M) (hC : ((center P).map P.subtype).map i = Z)
    (hQ : Q ≤ P.map i) (hZQ : Z ≤ Q) (hs : QuotientCentralizerBound Q Z) :
    center P ≤ (Q.comap i).subgroupOf P ∧
      centralizer (((Q.comap i).subgroupOf P).map (QuotientGroup.mk' (center P)) :
        Set (P ⧸ center P)) ≤
      ((Q.comap i).subgroupOf P).map (QuotientGroup.mk' (center P)) := by
  let f := i.comp P.subtype
  have hCf : (center P).map f = Z := by rw [← map_map]; exact hC
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hZQ (hCf ▸ mem_map_of_mem f hx)
  · obtain ⟨hZn, hs⟩ := hs
    exact ambient_quotient_centralizer_pullback f (hi.comp P.subtype_injective)
      Z (center P) hCf Q (by
        change Q ≤ (i.comp P.subtype).range
        rw [MonoidHom.range_comp, range_subtype]
        exact hQ) hs

/-- The actual source quotient chain produces the two full-Ree core alternatives. -/
theorem ree_core_cases {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (hQ : pCore 2 M ≤ reeQ.map i) (hZQ : reeZ i ≤ pCore 2 M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hs : QuotientCentralizerBound (pCore 2 M) (reeZ i)) :
    pCore 2 M = reeF.map i ∨ pCore 2 M = reeQ.map i := by
  have hC : ((center reeQ).map reeQ.subtype).map i = reeZ i := by
    rw [ree_center_mark, MonoidHom.map_zpowers]
  obtain ⟨hz, hs⟩ := pullback i hi reeQ (pCore 2 M) (reeZ i) hC hQ hZQ hs
  exact ree_ambient_core_cases i hi hc hQ hz hs

/-- The same literal quotient transport for the actual Tits core. -/
theorem tits_core_cases {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (hQ : pCore 2 M ≤ titsQ.map i) (hZQ : titsZ i ≤ pCore 2 M)
    (hs : QuotientCentralizerBound (pCore 2 M) (titsZ i)) :
    pCore 2 M = titsF.map i ∨ pCore 2 M = titsQ.map i := by
  have hC : ((center titsQ).map titsQ.subtype).map i = titsZ i := by
    rw [tits_center_mark, MonoidHom.map_zpowers]
  obtain ⟨hz, hs⟩ := pullback i hi titsQ (pCore 2 M) (titsZ i) hC hQ hZQ hs
  exact tits_ambient_core_cases i hi hQ hz hs
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction
