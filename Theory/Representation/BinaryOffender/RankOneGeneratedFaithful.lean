module
public import Theory.Representation.BinaryOffender.RankOneGeneratedRestriction
public import Theory.Representation.BinaryOffender.MovedFaithfulness
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
/-!
# Faithfulness on the residual-containing displacement orbit

If the normal closure of an actor contains the odd residual of a finite
binary group with trivial two-core, it is self-centralizing. A faithful
representation stays faithful on that actor's exact displacement orbit:
its restricted kernel fixes all displacements of the normal closure and
therefore vanishes. Together with rank-one generation, this supplies the
faithful generated module required by G.6.1 without changing the quotient.

Source application: Aschbacher–Smith G.6.1–4 and10.2.1, pp.345–346 and743.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
theorem faithful_conjugate_displacement_restriction
    (hρ : Function.Injective ρ) (hcore : pCore 2 G=⊥) (a : G)
    (hres : pResidual 2 G ≤ normalClosure ({a} : Set G))
    (S : Subrepresentation ρ)
    (hS : S.toSubmodule=conjugateDisplacementSpan ρ a ⊤) :
    Function.Injective S.toRepresentation := by
  let K := normalClosure ({a} : Set G)
  have hK : centralizer (K : Set G) ≤ K :=
    (centralizer_le hres).trans ((centralizer_pResidual_le_of_pCore_eq_bot hcore).trans hres)
  have hker : S.toRepresentation.ker=⊥ := by
    apply normal_eq_bot_of_fixes_displacements ρ hρ hcore K _ hK
    intro n hn k hk v
    have hv : ρ k v-v∈S.toSubmodule := by
      rw [hS,←commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top]
      exact Submodule.subset_span ⟨k,hk,v,Submodule.mem_top,rfl⟩
    have he : S.toRepresentation n = 1 := hn
    have hh := congrArg (fun f : Module.End (ZMod 2) S.toSubmodule => f ⟨ρ k v-v,hv⟩) he
    exact congrArg Subtype.val hh
  exact (MonoidHom.ker_eq_bot_iff _).mp hker
end Representation.BinaryOffender
