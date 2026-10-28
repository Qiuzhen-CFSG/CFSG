module
public import Theory.Representation.BinaryConjugationSection.TrivialCommutant
public import Theory.Representation.BinaryScalarCommutant

/-!
# Perfect actors commuting with a scalar section

A perfect group acting on a marked moved central quotient with scalar
commutant acts trivially there. The three-subgroup lemma and E = [E,B]
then remove the displacement into C_E(B), so it centralizes all of E.
The quotient and both conjugation actions are the original ones.

Source application: crossed centralization in Aschbacher--Smith 10.1.1,
printed p.741, for the orthogonal and Suzuki rows.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {F G W : Type*} [Field F] [Group G] [AddCommGroup W]
  [Module (ZMod 2) W] [Module F W]
  {B E : Subgroup G} [IsElementaryAbelian 2 E]
  {ρ : Representation (ZMod 2) B W}

theorem centralizes_of_perfect_scalar_commutant
    (d : BinaryConjugationSection B E (E ⊓ centralizer (B : Set G)) ρ)
    (hs : ∀ f : W →ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      ∃ c : F, ∀ w, f w = c • w)
    (Q : Subgroup G) [Group.IsPerfect Q] (hQB : Q ≤ normalizer (B : Set G))
    (hQE : Q ≤ normalizer (E : Set G))
    (hcomm : ⁅Q,B⁆ ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E) :
    Q ≤ centralizer (E : Set G) := by
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
    BinaryScalarCommutant.perfect_commuting_action_trivial ρ hs η hηcomm
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
  rw [hmove] at hzero
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
end Representation.BinaryConjugationSection
