module
public import Theory.Representation.BinaryConjugationSection.TrivialCommutant
public import Theory.Representation.BinaryScalarCommutant.TwoGroups

/-!
# Two-group centralization of a marked moving submodule

A two-group commuting with an actor on an elementary module acts as scalars
on its marked central quotient, hence trivially there. The three-subgroup
lemma then makes it centralize the entire actor commutator, including any
central attachment. The original module need not split over its fixed space.

Source application: DGS, Groups and Graphs (1985), (6.5), pp.121--122.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {F G W : Type*} [Field F] [CharP F 2] [Group G] [AddCommGroup W]
  [Module (ZMod 2) W] [Module F W] [Nontrivial W]
  {B E : Subgroup G} [IsElementaryAbelian 2 E]
  {ρ : Representation (ZMod 2) B W}

theorem centralizes_movement_of_twoGroup_scalar_commutant
    (d : BinaryConjugationSection B E (E ⊓ centralizer (B : Set G)) ρ)
    (hs : ∀ f : W →ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      ∃ c : F, ∀ w, f w = c • w)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQB : Q ≤ normalizer (B : Set G))
    (hQE : Q ≤ normalizer (E : Set G))
    (hcomm : ⁅Q,B⁆ ≤ centralizer (E : Set G)) :
    Q ≤ centralizer (↑(⁅E,B⁆ : Subgroup G) : Set G) := by
  have hQZ : Q ≤ normalizer (↑(E ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
    (le_inf hQE (hQB.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨η,hη⟩ := d.exists_original_quotient_action hQE hQZ
  have hco (q : Q) (b : B) :
      Commute (E.normalizerMonoidHom (inclusion hQE q))
        (E.normalizerMonoidHom (inclusion d.normalized b)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    change ⁅inclusion hQE q,inclusion d.normalized b⁆ ∈ E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcomm (commutator_mem_commutator q.property b.property)
  have hηcomm (q : Q) (b : B) (w : W) : η q (ρ b w) = ρ b (η q w) := by
    obtain ⟨e,he⟩ := d.onto (Multiplicative.ofAdd w)
    have hw : (d.coordinates e).toAdd = w := congrArg Multiplicative.toAdd he
    rw [←hw]
    rw [←d.equivariant,hη,hη,←d.equivariant]
    apply congrArg (fun e : E => (d.coordinates e).toAdd)
    exact DFunLike.congr_fun (hco q b).eq e
  have hfix : ∀ q w, η q w = w :=
    BinaryScalarCommutant.twoGroup_commuting_action_trivial ρ hs hQ η hηcomm
  have hQEfix : ⁅Q,E⁆ ≤ centralizer (B : Set G) := by
    apply commutator_le.mpr
    intro q hq e he
    let a : E := E.normalizerMonoidHom (inclusion hQE ⟨q,hq⟩) ⟨e,he⟩
    have ha : d.coordinates a = d.coordinates ⟨e,he⟩ := by
      apply Multiplicative.toAdd.injective
      exact (hη ⟨q,hq⟩ ⟨e,he⟩).symm.trans (hfix ⟨q,hq⟩ _)
    have hk : d.coordinates (a * (⟨e,he⟩ : E)⁻¹) = 1 := by
      rw [map_mul,map_inv,ha,mul_inv_cancel]
    exact ((d.coordinates_eq_one_iff _).mp hk).2
  have hzero : ⁅⁅E,B⁆,Q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (commutator_eq_bot_iff_le_centralizer.mpr (by rwa [commutator_comm B Q]))
      (commutator_eq_bot_iff_le_centralizer.mpr hQEfix)
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
end Representation.BinaryConjugationSection
