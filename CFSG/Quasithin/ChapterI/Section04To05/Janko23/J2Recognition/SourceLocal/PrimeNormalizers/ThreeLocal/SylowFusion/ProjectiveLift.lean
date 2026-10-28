module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.ActionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.ProjectiveLift.Coordinates
public import Theory.GroupTheory.CoprimeComplementLift
public import Theory.GroupTheory.NormalizerComplementAction
public import Theory.SpecificGroups.PGL2.NineSylowNormalizer

/-!
# Lifting the marked projective Sylow-normalizer action

The quotient coordinates identify the actual Sylow Frattini quotient with
its Sylow image in PGL₂(9), equivariantly for the actual normalizer maps.
The kernel of the normalizer projection has order three. Schur–Zassenhaus
therefore lifts a projective cyclic eight-complement isomorphically; the
pointwise projection identity transports both faithfulness and transitivity.

`sylowNormalizerAction` discharges the concrete PGL₂(9) calculation using
the upper-root and diagonal-torus model. It constructs the internal cyclic
eight-complement with its faithful, transitive Frattini action from the
centralizer calculation, extraspeciality and the embedded-center orbit.
The source fusion assembly supplies these earlier local hypotheses; no
additional projective calculation or splitting premise remains here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(3), printed p.262.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.ProjectiveLift
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem action_of_model {P : Sylow 3 G} (c : Coordinates P) (hP : IsExtraspecial 3 P)
    (a : NormalizerComplementAction (c.imageSylow : Subgroup PG) 8) :
    Nonempty (SylowNormalizerAction P) := by
  let := hP
  have hk : Nat.card c.onNormalizer.ker = 3 := by
    calc
      Nat.card c.onNormalizer.ker =
          Nat.card ((Z P).subgroupOf (normalizer (P : Set G))) := by rw [c.onNormalizer_ker]
      _ = Nat.card (Z P) := Nat.card_congr (subgroupOfEquivOfLe
        ((map_subtype_le (center P)).trans (P : Subgroup G).le_normalizer)).toEquiv
      _ = 3 := by
        rw [card_map_of_injective (P : Subgroup G).subtype_injective,
          IsExtraspecial.center_order_p 3 P]
  obtain ⟨E, hE, e, he⟩ := c.onNormalizer.exists_complement_lift_of_coprime_kernel
    c.onNormalizer_surjective
    ((c.imageSylow : Subgroup PG).subgroupOf (normalizer (c.imageSylow : Set PG)))
    a.complement a.split (by
      rw [hk]
      change Nat.Coprime 3 (Nat.card a.complement)
      rw [a.card]
      decide)
  rw [c.onNormalizer_comap] at hE
  have hcyc : IsCyclic E := e.isCyclic.mpr a.cyclic
  have hcard : Nat.card E = 8 := (Nat.card_congr e.toEquiv).trans a.card
  have hc (b : E) (x : P ⧸ frattini P) :
      c.frattiniEquiv hP (sylowFrattiniAction P b x) =
        (c.imageSylow : Subgroup PG).normalizerMonoidHom (e b)
          (c.frattiniEquiv hP x) := by
    rw [he]
    exact c.frattiniEquiv_conjugation hP b x
  refine ⟨⟨E, hcyc, hcard, hE, ?_, ?_⟩⟩
  · intro b d hbd
    apply e.injective
    apply a.faithful
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := (c.frattiniEquiv hP).surjective x
    change (c.imageSylow : Subgroup PG).normalizerMonoidHom (e b)
        (c.frattiniEquiv hP u) =
      (c.imageSylow : Subgroup PG).normalizerMonoidHom (e d)
        (c.frattiniEquiv hP u)
    rw [← hc, ← hc]
    exact congrArg (c.frattiniEquiv hP) (congrArg (fun t : MulAut (P ⧸ frattini P) => t u) hbd)
  · intro u v hu hv
    obtain ⟨b, hb⟩ := a.transitive (c.frattiniEquiv hP u) (c.frattiniEquiv hP v)
      (fun h => hu ((c.frattiniEquiv hP).map_eq_one_iff.mp h))
      (fun h => hv ((c.frattiniEquiv hP).map_eq_one_iff.mp h))
    refine ⟨e.symm b, (c.frattiniEquiv hP).injective ?_⟩
    rw [hc, e.apply_symm_apply]
    exact hb

theorem sylowNormalizerAction_of_projective_calculation
    (H : CentralizerCalculation D) (P : Sylow 3 G) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X)
    (hmodel : ∀ Q : Sylow 3 PG, Nonempty (NormalizerComplementAction (Q : Subgroup PG) 8)) :
    Nonempty (SylowNormalizerAction P) := by
  obtain ⟨c⟩ := coordinates H P hV
  exact action_of_model c hP (hmodel c.imageSylow).some

/-- The marked Sylow-normalizer action of 47.3(3), with the concrete
projective calculation discharged. Once extraspeciality and the center
orbit are known, neither the global order nor simplicity is needed for
this lift. The action uses the literal normalizer and Frattini quotient. -/
theorem sylowNormalizerAction
    (H : CentralizerCalculation D) (P : Sylow 3 G) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X) :
    Nonempty (SylowNormalizerAction P) :=
  sylowNormalizerAction_of_projective_calculation H P hP hV
    GorensteinWalter.PGL2NineSylowNormalizer.sylowNormalizerAction

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.ProjectiveLift
