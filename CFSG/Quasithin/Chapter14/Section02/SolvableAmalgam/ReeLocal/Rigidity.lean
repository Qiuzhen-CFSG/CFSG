module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
public import Theory.GroupTheory.PCoreCentralQuotientImage

/-!
# Rigidity of the actual Ree and Tits first parabolics

An injectively embedded actual first parabolic equals a finite overgroup
when it contains a Sylow two-subgroup, the overgroup has self-centralizing
two-core, and its marked involution is central in the overgroup.

Sylow containment puts the ambient core in the embedded local core.
Characteristic-two descent through the marked central subgroup supplies
chain (*). The corrected concrete core classification and derived action
then make the local core normal. The residual and involution-orbit argument
excludes a proper overgroup. In particular no extended representation,
core equality, quotient centralizer bound, or solvability assumption remains.

Source: Aschbacher--Smith, Lemma 14.2.21, printed pp.988--989. The core
classification retains and excludes the extra full-Ree omega case, and
the residual calculation uses images under quotient maps. It does not use
the incompatible quotient-center or residual-denominator formulas in the
printed proof. The parent source proof retains recognition and the earlier
Hypothesis 14.2.1 inputs.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal

open Subgroup ReeTwo.ParabolicConcrete AmbientDerivedAction

private theorem core_le_embedded_core {A M : Type*} [Group A] [Group M]
    (i : A →* M) (hi : Function.Injective i)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range) :
    pCore 2 M ≤ (pCore 2 A).map i := by
  have hQr : pCore 2 M ≤ i.range := (pCore_isPGroup.le_sylow_of_normal S).trans hS
  have hpre : (pCore 2 M).comap i ≤ pCore 2 A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  simpa only [map_comap_eq_self hQr] using map_mono (f := i) hpre

private theorem central_chain {M : Type*} [Group M] [Finite M]
    (Z : Subgroup M) (hZ : Z ≤ center M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    Z ≤ pCore 2 M ∧ QuotientCentralizerBound (pCore 2 M) Z := by
  let : Z.Normal := ⟨fun a ha b => by
    simpa only [mem_center_iff.mp (hZ ha) b, mul_inv_cancel_right] using ha⟩
  exact ⟨(hZ.trans (center_le_centralizer _)).trans hc,
    inferInstance, centralizer_image_pCore_le_of_central_quotient Z hZ hc⟩

/-- The full-Ree parabolic fills every characteristic-two, Sylow-preserving
overgroup centralizing its actual marked involution. -/
public theorem ree_rigidity {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    (hZ : reeZ i ≤ center M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    i.range = ⊤ ∧
      (pResidual 2 Tits.ExceptionalParabolics.FullRee.first).map i = pResidual 2 M := by
  obtain ⟨hZQ, hs⟩ := central_chain (reeZ i) hZ hc
  obtain ⟨_, _, _, hQ, hFN, ρ, hρ, _, hres⟩ :=
    AmbientDerivedAction.ree_local i hi (core_le_embedded_core i hi S hS) hZQ hZ hc hs
  let : (reeF.map i).Normal := hFN
  exact ResidualRigidity.ree_rigidity i hi hQ hc S hS ρ hρ hres

/-- The same rigidity for the actual Tits parabolic with its mixed-character
core of order 512 and the published marked embedding. -/
public theorem tits_rigidity {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    (hZ : titsZ i ≤ center M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    i.range = ⊤ ∧
      (pResidual 2 Tits.ExceptionalParabolics.first).map i = pResidual 2 M := by
  obtain ⟨hZQ, hs⟩ := central_chain (titsZ i) hZ hc
  obtain ⟨_, _, _, hQ, hFN, ρ, hρ, _, hres⟩ :=
    AmbientDerivedAction.tits_local i hi (core_le_embedded_core i hi S hS) hZQ hZ hc hs
  let : (titsF.map i).Normal := hFN
  exact ResidualRigidity.tits_rigidity i hi hQ hc S hS ρ hρ hres

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
