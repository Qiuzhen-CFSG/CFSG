module

public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# Canonical multiplier comparison across universes

An actual isomorphism to a finite quasisimple model transports any explicit
universal cover to the source group. Universal lifts in both directions are
surjective, so finiteness makes either lift bijective. Restricting this
compatible isomorphism to the kernels preserves the full multiplier group,
including noncyclic multipliers. The source and model may inhabit different
universes.

Source: the universal-cover comparison in GLS3, Theorem 5.1.2, applied to
the canonical perfect cover of Aschbacher--Smith I.1.1.
-/

public section
noncomputable section
namespace PerfectCentralCovering
open Theory.GroupTheory
universe u v w

/-- Compare the literal canonical kernel with an explicit universal cover of
an isomorphic model. No equality of the source and model universes is needed. -/
def schurMultiplierEquivOfUniversal
    {S : Type u} {G : Type v} {L : Type w}
    [Group S] [Finite S] [Group.IsPerfect S]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group L] [Finite L] [IsQuasisimple L]
    (e : S ≃* G) (f : Covering L G)
    (hf : Covering.IsUniversal.{v, w, u} f) :
    schurMultiplier S ≃* f.toMonoidHom.ker := by
  letI : IsQuasisimple S := IsQuasisimple.of_mulEquiv e.symm
  let f' : Covering L S := (Covering.ofMulEquiv e.symm).comp f
  have hf' : Covering.IsUniversal.{u, w, u} f' := hf.comp_ofMulEquiv e.symm
  let c := universalQuasisimpleCover S
  have hc : Covering.IsUniversal.{u, u, w} c := universalQuasisimpleCover_isUniversal S
  let a := hc.lift f'
  let b := hf'.lift c
  have ha := hc.lift_fac f'
  let k : UniversalGroup S ≃* L := MulEquiv.ofBijective a.toMonoidHom
    (a.surjective.bijective_of_nat_card_le
      (Nat.card_le_card_of_surjective b b.surjective))
  exact Covering.kerMulEquivOfSquare c.toMonoidHom f.toMonoidHom k e (by
    intro x
    have h := congrArg (fun d : Covering (UniversalGroup S) S => d x) ha
    have h' : e.symm (f (a x)) = c x := h
    exact (e.apply_symm_apply (f (a x))).symm.trans (congrArg e h'))

/-- Canonical multipliers are invariant under an actual isomorphism to a
finite quasisimple model, with their group structures retained. -/
def schurMultiplierCongr
    {S : Type u} {G : Type v}
    [Group S] [Finite S] [Group.IsPerfect S]
    [Group G] [Finite G] [IsQuasisimple G]
    (e : S ≃* G) : schurMultiplier S ≃* schurMultiplier G :=
  schurMultiplierEquivOfUniversal e (universalQuasisimpleCover G)
    (universalQuasisimpleCover_isUniversal G)

end PerfectCentralCovering
