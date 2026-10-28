module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.Contracts
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson

/-!
# Simultaneous marking for small-prime generation in J₄

Every element of order 3, 5, 7 or 11 has a power conjugate to one of five
explicit words. The three first words are the certified prime representatives;
the last two are the central and noncentral representatives in the certified
Sylow eleven-subgroup. The actual model-order theorem discharges the order
premises of all four cyclic-coverage arguments.

Conjugating that power also conjugates its inverter a and the chosen Sylow
subgroup of C(a). We construct the exact centralizer isomorphism and Sylow
image, prove the transported inversion identity, and pull generation back
through the same conjugation. Generation by a power is sufficient, so no
choice of an inverse exponent is needed.

The final theorem applies these results to the published
`CentralSmallPrimeGeneration` contract. Its marked-word generation premise
is still open: one must cover every conjugate of a inverting each word and
every Sylow two-subgroup of its centralizer. Ordinary cyclic coverage or
normal generation of a word does not prove this premise. In particular,
`centralSmallPrimeGeneration` is not asserted here.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48, citing Aschbacher,
*Overgroups of Sylow subgroups in sporadic groups* (1986), no.343, and
Kleidman–Wilson, *The maximal subgroups of J₄* (1988), pp.484–510.
Word and matrix attribution is retained in `Simplicity.Words` and
`Simplicity.PrimeCoverage.Elevens.Words`; the imported coverage and order
certificates concern the literal matrix model.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.SmallPrimeGeneration
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem map_centralizer (e : Janko4.Model ≃* Janko4.Model) (z : Janko4.Model) :
    (centralizer ({z} : Set Janko4.Model)).map e.toMonoidHom =
      centralizer ({e z} : Set Janko4.Model) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({z} : Set Janko4.Model) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- Conjugation transports the full literal centralizer, with its marked involution. -/
private noncomputable def conjugateCentralizer (g : Janko4.Model) :
    centralizer ({Janko4.a} : Set Janko4.Model) ≃*
      centralizer ({(MulAut.conj g) Janko4.a} : Set Janko4.Model) :=
  ((MulAut.conj g).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_centralizer (MulAut.conj g) Janko4.a))

/-- The actual Sylow image in the transported centralizer. -/
noncomputable def conjugateSylow (g : Janko4.Model)
    (P : Sylow 2 (centralizer ({Janko4.a} : Set Janko4.Model))) :
    Sylow 2 (centralizer ({(MulAut.conj g) Janko4.a} : Set Janko4.Model)) :=
  P.mapSurjective (f := (conjugateCentralizer g).toMonoidHom)
    (conjugateCentralizer g).surjective

/-- Both literal centralizer inclusions commute with the Sylow transport. -/
theorem conjugateSylow_image (g : Janko4.Model)
    (P : Sylow 2 (centralizer ({Janko4.a} : Set Janko4.Model))) :
    (conjugateSylow g P).toSubgroup.map
        (centralizer ({(MulAut.conj g) Janko4.a} : Set Janko4.Model)).subtype =
      (P.toSubgroup.map (centralizer ({Janko4.a} : Set Janko4.Model)).subtype).map
        (MulAut.conj g).toMonoidHom := by
  change (P.toSubgroup.map (conjugateCentralizer g).toMonoidHom).map _ = _
  rw [map_map, map_map]
  rfl

/-- The transported involution inverts every transported power. -/
theorem conjugate_inverts_power (g r : Janko4.Model) (k : ℕ)
    (hr : (MulAut.conj Janko4.a) r = r⁻¹) :
    (MulAut.conj ((MulAut.conj g) Janko4.a)) ((MulAut.conj g) (r ^ k)) =
      ((MulAut.conj g) (r ^ k))⁻¹ := by
  have hk : (MulAut.conj Janko4.a) (r ^ k) = (r ^ k)⁻¹ := by
    rw [map_pow, hr, inv_pow]
  calc
    _ = (MulAut.conj g) ((MulAut.conj Janko4.a) (r ^ k)) := by
      change (MulAut.conj g) Janko4.a * (MulAut.conj g) (r ^ k) *
        ((MulAut.conj g) Janko4.a)⁻¹ =
        (MulAut.conj g) (Janko4.a * r ^ k * Janko4.a⁻¹)
      rw [map_mul, map_mul, map_inv]
    _ = (MulAut.conj g) ((r ^ k)⁻¹) := congrArg (MulAut.conj g) hk
    _ = _ := map_inv _ _

/-- Generation by a conjugated power and the same conjugated subgroup pulls back. -/
theorem generation_of_conjugate_power (g r w : Janko4.Model) (k : ℕ)
    (U : Subgroup Janko4.Model) (hw : w = (MulAut.conj g) (r ^ k))
    (hgen : closure (insert w (U.map (MulAut.conj g).toMonoidHom : Set Janko4.Model)) = ⊤) :
    closure (insert r (U : Set Janko4.Model)) = ⊤ := by
  let e := MulAut.conj g
  let H := closure (insert r (U : Set Janko4.Model))
  have hU : U ≤ H := fun x hx => subset_closure (Set.mem_insert_of_mem r hx)
  have hrH : r ∈ H := subset_closure (Set.mem_insert r _)
  have htop : H.map e.toMonoidHom = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro x (rfl | hx)
    · rw [hw]
      exact mem_map_of_mem _ (H.pow_mem hrH k)
    · exact map_mono hU hx
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_top_of_surjective e.toMonoidHom e.surjective]
  exact htop

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.SmallPrimeGeneration


namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.SmallPrimeGeneration
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Janko4.Simplicity

/-- Three prime words followed by the central and noncentral eleven-words. -/
@[expose] noncomputable def representative : Fin 5 → Janko4.Model :=
  ![primeRepresentative Janko4.a Janko4.b 2,
    primeRepresentative Janko4.a Janko4.b 3,
    primeRepresentative Janko4.a Janko4.b 4,
    Elevens.localRepresentative Janko4.a Janko4.b 0,
    Elevens.localRepresentative Janko4.a Janko4.b 1]

private theorem certified_a : a Janko4.matrixA_mul_self = Janko4.a := by
  apply Janko4.toMatrix_injective
  rfl

private theorem certified_b : b Janko4.matrixB_pow_four = Janko4.b := by
  apply Janko4.toMatrix_injective
  rfl

/-- Unconditional cyclic coverage of all four small primes in the actual model. -/
theorem cyclic_coverage (q : ℕ) (hq : q ∈ ({3, 5, 7, 11} : Finset ℕ))
    (r : Janko4.Model) (hr : orderOf r = q) :
    ∃ (i : Fin 5) (k : ℕ) (g : Janko4.Model),
      representative i = (MulAut.conj g) (r ^ k) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · obtain ⟨k, g, hg⟩ := three_explicit_coverage Janko4.matrixA_mul_self
      Janko4.matrixB_pow_four Janko4.Cardinality.Thompson.model_card r hr
    refine ⟨0, k, g, ?_⟩
    rw [certified_a, certified_b] at hg
    exact hg
  · have ho := orderOf_primeRepresentative_five Janko4.matrixA_mul_self
      Janko4.matrixB_pow_four
    rw [certified_a, certified_b] at ho
    obtain ⟨k, g, hg⟩ := exists_conjugate_pow_of_prime_sq_not_dvd
      (by decide : Nat.Prime 5)
      (by rw [Janko4.Cardinality.Thompson.model_card]; decide :
        ¬ 5 ^ 2 ∣ Nat.card Janko4.Model) hr ho
    exact ⟨1, k, g, hg⟩
  · have ho := orderOf_primeRepresentative_seven Janko4.matrixA_mul_self
      Janko4.matrixB_pow_four
    rw [certified_a, certified_b] at ho
    obtain ⟨k, g, hg⟩ := exists_conjugate_pow_of_prime_sq_not_dvd
      (by decide : Nat.Prime 7)
      (by rw [Janko4.Cardinality.Thompson.model_card]; decide :
        ¬ 7 ^ 2 ∣ Nat.card Janko4.Model) hr ho
    exact ⟨2, k, g, hg⟩
  · have hc := Elevens.coverage_of_card_1331 Janko4.Cardinality.Thompson.model_card
      (Elevens.localRepresentative (a Janko4.matrixA_mul_self) (b Janko4.matrixB_pow_four))
      (Elevens.localSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
      (Elevens.local_card Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
      (Elevens.local_coverage Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    obtain ⟨i, k, g, hg⟩ := hc r hr
    rw [certified_a, certified_b] at hg
    fin_cases i
    · exact ⟨3, k, g, hg⟩
    · exact ⟨4, k, g, hg⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.SmallPrimeGeneration

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Subgroup SmallPrimeGeneration
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Application to the exact generation contract consumed by
`maximalTwoCoreNontrivial_of_oddPrimeGeneration`. The remaining premise is
universal in the transported inverter and its centralizer Sylow; it is not
supplied by the cyclic-coverage certificates. -/
theorem centralSmallPrimeGeneration_of_marked_representatives
    (hwords : ∀ (i : Fin 5) (g : Janko4.Model)
      (Q : Sylow 2 (centralizer ({(MulAut.conj g) Janko4.a} : Set Janko4.Model))),
      (MulAut.conj ((MulAut.conj g) Janko4.a)) (representative i) = (representative i)⁻¹ →
      closure (insert (representative i)
        (Q.toSubgroup.map
          (centralizer ({(MulAut.conj g) Janko4.a} : Set Janko4.Model)).subtype :
            Set Janko4.Model)) = ⊤) :
    CentralSmallPrimeGeneration := by
  intro P q hq r hr hinv
  obtain ⟨i, k, g, hg⟩ := cyclic_coverage q hq r hr
  apply generation_of_conjugate_power g r (representative i) k _ hg
  rw [← conjugateSylow_image]
  apply hwords i g (conjugateSylow g P)
  rw [hg]
  exact conjugate_inverts_power g r k hinv

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
