module
public import Theory.Representation.BinaryConjugationSection.NormalizerAction

/-!
# Actors on a faithful section with trivial commutant

A normalizing actor whose commutators with the acting group centralize
the section induces a commuting linear automorphism. If the marked
representation has trivial automorphism commutant, faithfulness of the
section coordinates makes that actor centralize the original subgroup.

This retains the original conjugation maps in the endomorphism argument
of Aschbacher–Smith 12.3.8, printed p.810.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {B E : Subgroup G} {ρ : Representation (ZMod 2) B W}

/-- Commuting actors on a faithfully marked section with trivial commutant act trivially. -/
theorem centralizes_of_faithful_trivial_commutant
    (d : BinaryConjugationSection B E ⊥ ρ)
    (htriv : ∀ f : W ≃ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      f = LinearEquiv.refl _ _)
    (Q : Subgroup G) (hQE : Q ≤ normalizer (E : Set G))
    (hcomm : ⁅Q,B⁆ ≤ centralizer (E : Set G)) :
    Q ≤ centralizer (E : Set G) := by
  have hi : Function.Injective d.coordinates := by
    apply d.coordinates.ker_eq_bot_iff.mp
    rw [d.kernel_eq,bot_subgroupOf]
  let α := normalizerAction d.coordinates ⟨hi,d.onto⟩
  have hco (q : Q) (b : B) :
      Commute (E.normalizerMonoidHom (inclusion hQE q))
        (E.normalizerMonoidHom (inclusion d.normalized b)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    change ⁅inclusion hQE q,inclusion d.normalized b⁆ ∈ E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcomm (commutator_mem_commutator q.property b.property)
  have hfix (q : Q) : α (inclusion hQE q) = LinearEquiv.refl _ _ := by
    apply htriv
    intro b w
    obtain ⟨e,he⟩ := d.onto (Multiplicative.ofAdd w)
    have hw : (d.coordinates e).toAdd = w := congrArg Multiplicative.toAdd he
    rw [← hw]
    calc
      α (inclusion hQE q) (ρ b (d.coordinates e).toAdd) =
          α (inclusion hQE q) (d.coordinates
            (E.normalizerMonoidHom (inclusion d.normalized b) e)).toAdd :=
        congrArg (α (inclusion hQE q)) (d.equivariant b e).symm
      _ = (d.coordinates (E.normalizerMonoidHom (inclusion hQE q)
          (E.normalizerMonoidHom (inclusion d.normalized b) e))).toAdd :=
        normalizerAction_coordinates d.coordinates ⟨hi,d.onto⟩ _ _
      _ = (d.coordinates (E.normalizerMonoidHom (inclusion d.normalized b)
          (E.normalizerMonoidHom (inclusion hQE q) e))).toAdd :=
        congrArg (fun e : E => (d.coordinates e).toAdd)
          (DFunLike.congr_fun (hco q b).eq e)
      _ = ρ b (d.coordinates (E.normalizerMonoidHom (inclusion hQE q) e)).toAdd :=
        d.equivariant b _
      _ = ρ b (α (inclusion hQE q) (d.coordinates e).toAdd) :=
        congrArg (ρ b) (normalizerAction_coordinates d.coordinates ⟨hi,d.onto⟩ _ _).symm
  intro q hq e he
  have hh := normalizerAction_coordinates d.coordinates ⟨hi,d.onto⟩
    (inclusion hQE ⟨q,hq⟩) ⟨e,he⟩
  change α (inclusion hQE ⟨q,hq⟩) _ = _ at hh
  rw [hfix] at hh
  have hh' := hi (Multiplicative.toAdd.injective hh.symm)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh')).symm
end Representation.BinaryConjugationSection
