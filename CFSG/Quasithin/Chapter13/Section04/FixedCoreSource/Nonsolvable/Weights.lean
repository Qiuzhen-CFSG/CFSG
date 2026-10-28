module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.Representation.BinaryPermutation.SixConstantWeight

/-!
# Weight and centralizer transport in the original fixed core

The all-one coordinate word is the actual generator of C_V(L). Equal-weight
vectors are conjugate by elements of the original L, through the literal
L/centralCore L marking. Consequently containment of their full ambient
centralizers in N_G(L) is constant on each weight class.

After source 13.4.12 supplies a unique escaping vector in V∩Ω₁Z(T), its
product with the fixed generator is the other Sylow-central weight choice.
Uniqueness and the fixed-generator centralizer theorem therefore force every
escaping nonidentity vector of V to have the same weight. The proof of
13.4.12 remains with qt-d-1341-nonsolvable-source; this is its conditional
weight-transport consumer, not a proof of that uniqueness assertion.

Source: Aschbacher–Smith 13.4.12 and 13.4.16–17, pp.910–914.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace CoreMarking
variable {D : ChosenModule T L V} (m : CoreMarking D)

def weight (v : V) : ℕ := wordWeight (m.coordinate v).toAdd.val

def constant : V := m.coordinate.symm (Multiplicative.ofAdd sixCoreConstant)

theorem constant_coordinate : (m.coordinate m.constant).toAdd = sixCoreConstant :=
  m.coordinate.apply_symm_apply _

theorem constant_ne_one : m.constant ≠ 1 := by
  intro he
  have hh := m.constant_coordinate
  rw [he, map_one] at hh
  exact sixCoreConstant_ne_zero hh.symm

theorem constant_fixed : m.constant.val ∈ centralizer (L : Set G) := by
  apply (m.mem_fixed_iff _).mpr
  rw [m.constant_coordinate]
  exact (core_fixed_iff_constant (by simp) sixCoreConstant).mp
    sixCoreConstant_fixed

theorem fixed_iff (v : V) : v.val ∈ centralizer (L : Set G) ↔
    v = 1 ∨ v = m.constant := by
  rw [m.mem_fixed_iff, ← core_fixed_iff_constant (by simp)]
  change (∀ a, alternatingCoreRepresentation (Fin 6) a (m.coordinate v).toAdd =
    (m.coordinate v).toAdd) ↔ _
  rw [sixCore_fixed_iff]
  constructor
  · rintro (hv | hv)
    · left
      exact m.coordinate.injective (hv.trans m.coordinate.map_one.symm)
    · right
      apply m.coordinate.injective
      exact hv.trans m.constant_coordinate.symm
  · rintro (rfl | rfl)
    · exact Or.inl m.coordinate.map_one
    · exact Or.inr m.constant_coordinate

theorem exists_conjugator_of_weight_eq (v w : V) (he : m.weight v = m.weight w) :
    ∃ l ∈ L, MulAut.conj l v.val = w.val := by
  obtain ⟨a, ha⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card (Fin 6))
    (m.coordinate v).toAdd.val (m.coordinate w).toAdd.val he
  obtain ⟨q, rfl⟩ := m.quotient.surjective a
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨l, l.property, ?_⟩
  have hh := m.equivariant l v
  have heq : coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' _ l)).val (m.coordinate v).toAdd =
      (m.coordinate w).toAdd := Subtype.ext ha
  exact congrArg Subtype.val (m.coordinate.injective
    (Multiplicative.toAdd.injective (hh.trans heq)))

private theorem centralizer_le_of_conjugator (M : Subgroup G) {v w l : G}
    (hl : l ∈ M) (he : MulAut.conj l v = w)
    (hc : centralizer ({v} : Set G) ≤ M) : centralizer ({w} : Set G) ≤ M := by
  intro x hx
  have hcx : MulAut.conj l⁻¹ x ∈ centralizer ({v} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj l).injective
    simpa only [map_mul, he, MulAut.conj_apply, inv_inv, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel, mul_one, one_mul] using mem_centralizer_singleton_iff.mp hx
  have hmem := M.mul_mem (M.mul_mem hl (hc hcx)) (M.inv_mem hl)
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hmem

theorem centralizer_le_iff_of_weight_eq (v w : V) (he : m.weight v = m.weight w) :
    centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) ↔
    centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) := by
  constructor
  · obtain ⟨l, hl, he⟩ := m.exists_conjugator_of_weight_eq v w he
    exact centralizer_le_of_conjugator _ (L.le_normalizer hl) he
  · obtain ⟨l, hl, he⟩ := m.exists_conjugator_of_weight_eq w v he.symm
    exact centralizer_le_of_conjugator _ (L.le_normalizer hl) he


@[simp] theorem weight_one : m.weight 1 = 0 := by
  simp [weight, wordWeight]

theorem weight_constant : m.weight m.constant = 6 := by
  rw [weight, m.constant_coordinate]
  decide

theorem weight_mul_constant (v : V) : m.weight (v * m.constant) = 6 - m.weight v := by
  unfold weight
  rw [map_mul]
  change wordWeight ((m.coordinate v).toAdd + (m.coordinate m.constant).toAdd).val = _
  rw [m.constant_coordinate]
  exact sixCore_complement_weight _

theorem nonfixed_weight (v : V) (hv : v.val ∉ centralizer (L : Set G)) :
    m.weight v = 2 ∨ m.weight v = 4 := by
  have hne := not_or.mp ((not_congr (m.fixed_iff v)).mp hv)
  apply sixCore_nonconstant_weight
  · intro he
    exact hne.1 (m.coordinate.injective (he.trans m.coordinate.map_one.symm))
  · intro he
    exact hne.2 (m.coordinate.injective (he.trans m.constant_coordinate.symm))

include D in
/-- In the chosen elementary module, Sylow centrality is exactly membership
in the source subgroup Ω₁Z(T). -/
theorem mem_omega_iff (v : V) :
    v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ↔
      v.val ∈ centralizer (T : Set G) := by
  constructor
  · intro hv
    apply mem_centralizer_iff.mpr
    intro t ht
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hv).2.2 t ht
  · intro hv
    let := D.elementary
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨D.le_sylow v.property, elemPow_eq_one_of_isElementaryAbelian v.val v.property, ?_⟩
    intro t ht
    exact mem_centralizer_iff.mp hv t ht

variable [Finite G]

/-- Source 13.4.12 uniqueness propagates to every vector of the original core.
The second Sylow-central choice is the actual product with the fixed generator. -/
theorem escape_has_unique_weight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (v : V) (hv1 : v ≠ 1)
    (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
    m.weight v = m.weight z := by
  have nonfixed (u : V) (hu : u ≠ 1)
      (hout : ¬ centralizer ({u.val} : Set G) ≤ normalizer (L : Set G)) :
      u.val ∉ centralizer (L : Set G) := by
    intro hf
    exact hout (fixed_generator_centralizer h structural D m ⟨u.property,hf⟩
      (fun he => hu (Subtype.ext he))).le
  have hzwt := m.nonfixed_weight z (nonfixed z hz1 hzout)
  have hvwt := m.nonfixed_weight v (nonfixed v hv1 hvout)
  have hdT : m.constant.val ∈ centralizer (T : Set G) := by
    have hh : (T : Subgroup G) ≤ centralizer (V ⊓ centralizer (L : Set G) : Set G) :=
      D.sylow_normalizes_component.trans (normalizer_component_le_fixed_centralizer h structural D m)
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp (hh ht) m.constant.val
      ⟨m.constant.property,m.constant_fixed⟩).symm
  have hwT : (z * m.constant).val ∈ centralizer (T : Set G) :=
    (centralizer (T : Set G)).mul_mem ((mem_omega_iff (D := D) z).mp hzT) hdT
  have hww := m.weight_mul_constant z
  have hw1 : z * m.constant ≠ 1 := by
    intro he
    rw [he, m.weight_one] at hww
    omega
  have hwz : z * m.constant ≠ z := by
    intro he
    rw [he] at hww
    omega
  have hwc : centralizer ({(z * m.constant).val} : Set G) ≤ normalizer (L : Set G) := by
    by_contra hh
    exact hwz (hunique _ hw1 ((mem_omega_iff (D := D) _).mpr hwT) hh)
  by_contra hne
  have he : m.weight v = m.weight (z * m.constant) := by omega
  exact hvout ((m.centralizer_le_iff_of_weight_eq v _ he).mpr hwc)

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
