module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.Contract

/-!
# The two noncentral module chief intervals of the point parabolic

The original projections identify B/A with V/⟨x⟩ and C/B with ann(x).
Their conjugation actions have the full linear images on these three-spaces.
An isomorphism between two nonzero one-dimensional spans extends to a linear
automorphism, so these images are transitive on nonzero vectors. Any intermediate
P-normal subgroup containing a nonzero quotient vector therefore contains the
whole quotient. A linear automorphism moving a nonzero vector also proves that
the commutator is not contained in the lower term.

The conclusions include strictness, containment in P, relative normality and
noncentrality for the actual subgroups of G. Both actions retain the common
marking and the contragredient compatibility of `ChiefLayers.Quotients`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

private theorem transitive_nonzero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : V ≃ₗ[ZMod 2] V, g u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V v hv
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (eu.symm.trans ev)
  refine ⟨g, ?_⟩
  have he := hg (eu 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at he
  simpa [eu, ev] using he.symm

/-- A nonzero normal intermediate image contains every nonzero quotient vector. -/
private theorem chief_of_full_linear_image
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (P A B : Subgroup G) (hBP : B ≤ P) (hBN : P ≤ normalizer (B : Set G))
    (f : B →* Multiplicative V) (hker : f.ker = A.subgroupOf B)
    (ρ : P →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Surjective ρ)
    (hequiv : ∀ (p : P) (b : B), (f (conjugate P B hBN p b)).toAdd = ρ p (f b).toAdd)
    (D : Subgroup G) (hAD : A ≤ D) (hDB : D ≤ B) (hDN : (D.subgroupOf P).Normal) :
    D = A ∨ D = B := by
  classical
  by_cases hDA : D ≤ A
  · exact Or.inl (le_antisymm hDA hAD)
  right
  apply le_antisymm hDB
  obtain ⟨b, hbD, hbA⟩ := SetLike.not_le_iff_exists.mp hDA
  let b' : B := ⟨b, hDB hbD⟩
  have hb0 : (f b').toAdd ≠ 0 := by
    intro he
    have hk : b' ∈ f.ker := by
      change f b' = 1
      exact Multiplicative.toAdd.injective he
    rw [hker] at hk
    exact hbA hk
  have hnorm : P ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hDB.trans hBP)).mp hDN
  intro c hcB
  let c' : B := ⟨c, hcB⟩
  by_cases hc0 : (f c').toAdd = 0
  · apply hAD
    have hk : c' ∈ f.ker := by
      change f c' = 1
      exact Multiplicative.toAdd.injective hc0
    rw [hker] at hk
    exact hk
  obtain ⟨g, hg⟩ := transitive_nonzero (f b').toAdd (f c').toAdd hb0 hc0
  obtain ⟨p, hp⟩ := hρ g
  let z := conjugate P B hBN p b'
  have hzD : (z : G) ∈ D :=
    (le_normalizer_iff.mp hnorm) p p.property b hbD
  have hfz : f z = f c' := by
    apply Multiplicative.toAdd.injective
    change (f (conjugate P B hBN p b')).toAdd = _
    rw [hequiv, hp, hg]
  have hk : c' * z⁻¹ ∈ f.ker := by
    change f (c' * z⁻¹) = 1
    rw [map_mul, map_inv, hfz, mul_inv_cancel]
  rw [hker] at hk
  have hm := D.mul_mem (hAD hk) hzD
  change (c * (z : G)⁻¹) * (z : G) ∈ D at hm
  simpa only [inv_mul_cancel_right] using hm

/-- A quotient with at least two nonzero vectors has a genuinely moving actor. -/
private theorem noncentral_of_full_linear_image
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hcard : 2 < Nat.card V)
    (P A B : Subgroup G) (hBN : P ≤ normalizer (B : Set G))
    (f : B →* Multiplicative V) (hf : Function.Surjective f)
    (hker : f.ker = A.subgroupOf B)
    (ρ : P →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Surjective ρ)
    (hequiv : ∀ (p : P) (b : B), (f (conjugate P B hBN p b)).toAdd = ρ p (f b).toAdd) :
    ¬ ⁅P, B⁆ ≤ A := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp (show 2 < Fintype.card V by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hpairs : ∃ u v : V, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
    by_cases ha : a = 0
    · exact ⟨b, c, by aesop, by aesop, hbc⟩
    by_cases hb : b = 0
    · exact ⟨a, c, ha, by aesop, hac⟩
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨u, v, hu, hv, huv⟩ := hpairs
  obtain ⟨g, hg⟩ := transitive_nonzero u v hu hv
  obtain ⟨p, hp⟩ := hρ g
  obtain ⟨w, hw⟩ := hf (Multiplicative.ofAdd u)
  intro hcentral
  let z := conjugate P B hBN p w
  have hk : z * w⁻¹ ∈ f.ker := by
    rw [hker]
    exact hcentral (commutator_mem_commutator p.property w.property)
  have heq : f z = f w := by
    apply mul_inv_eq_one.mp
    simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hk
  have hmove : (f z).toAdd = v := by
    change (f (conjugate P B hBN p w)).toAdd = v
    rw [hequiv, hp, hw]
    exact hg
  exact huv (show u = v from (congrArg Multiplicative.toAdd hw).symm.trans
    ((congrArg Multiplicative.toAdd heq).symm.trans hmove))

/-- The actual interval B/A is a noncentral chief interval for P. Its marked
quotient is V/⟨x⟩, and the original P-action has the full linear image. -/
public theorem natural_interval_chief [Finite G] (h : NaturalDual d L) {x : Space 4}
    (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    IsNoncentralChiefInterval h x (lineSubgroup h x) (naturalSubgroup h) := by
  have hBP : naturalSubgroup h ≤ point h x :=
    (coordinateSubgroup_le_module h naturalSpace).trans (hU.trans (pCoreIn_le 2 _))
  have hcard : 2 < Nat.card (pointQuotient x) := by
    rw [Nat.card_congr (Pure.quotientCoordinates hx).toEquiv]
    simp [Space, Nat.card_eq_fintype_card]
  exact {
    strict := (ordered_flag h hx hU).1
    upper_le := hBP
    lower_normal := lineSubgroup_normal h x
    upper_normal := naturalSubgroup_normal h x
    chief := chief_of_full_linear_image _ _ _ hBP (naturalSubgroup_normalized h x)
      (naturalProjection h x) (naturalProjection_ker h x)
      (quotientActor h x) (quotientActor_surjective h x) (naturalProjection_conj h x)
    noncentral := noncentral_of_full_linear_image hcard _ _ _ (naturalSubgroup_normalized h x)
      (naturalProjection h x) (naturalProjection_surjective h x) (naturalProjection_ker h x)
      (quotientActor h x) (quotientActor_surjective h x) (naturalProjection_conj h x) }

/-- The actual interval C/B is a noncentral chief interval for P. It retains the
annihilator action dual to B/A under `commonActorEquiv`, with no new marking. -/
public theorem mixed_interval_chief [Finite G] (h : NaturalDual d L) {x : Space 4}
    (hx : x ≠ 0) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    IsNoncentralChiefInterval h x (naturalSubgroup h) (mixedSubgroup h x) := by
  let : Finite (annihilator x) := Module.finite_of_finite (ZMod 2)
  have hCP : mixedSubgroup h x ≤ point h x :=
    (coordinateSubgroup_le_module h (mixedSpace x)).trans (hU.trans (pCoreIn_le 2 _))
  have hcard : 2 < Nat.card (annihilator x) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, annihilator_finrank hx]
    decide
  exact {
    strict := (ordered_flag h hx hU).2.1
    upper_le := hCP
    lower_normal := naturalSubgroup_normal h x
    upper_normal := mixedSubgroup_normal h x
    chief := chief_of_full_linear_image _ _ _ hCP (mixedSubgroup_normalized h x)
      (mixedProjection h x) (mixedProjection_ker h x)
      (annihilatorActor h x) (annihilatorActor_surjective h x) (mixedProjection_conj h x)
    noncentral := noncentral_of_full_linear_image hcard _ _ _ (mixedSubgroup_normalized h x)
      (mixedProjection h x) (mixedProjection_surjective h x) (mixedProjection_ker h x)
      (annihilatorActor h x) (annihilatorActor_surjective h x) (mixedProjection_conj h x) }


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
