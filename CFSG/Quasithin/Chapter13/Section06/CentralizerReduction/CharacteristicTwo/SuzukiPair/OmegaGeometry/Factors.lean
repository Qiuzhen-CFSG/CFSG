module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Sylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Literal coordinates and central kernels for the Suzuki pair

The two embeddings are K itself and its conjugate by an actual element
of Tᵥ. PairFactors records their central-quotient coordinates, the
component orbit and the factor permutation. The separate coordinate
markings allow independent inner conjugation when aligning the Sylow.
No existence of these coordinates is asserted here; their producer is
MovingComponent.Coordinates.

Distinct components commute. Their product is the whole orbit, and the
coordinate equations show that its center is the image of Z(K) × Z(K).
Thus an elementary center of K gives an elementary center of the orbit.
Involution lifting through the single-factor center gives lifting through
the paired center by multiplying commuting lifts. The literal conjugation
action on the orbit retains its full ambient centralizer kernel.

Source: Aschbacher–Smith, 13.6.6, p.927; multiplier input I.1.3 and the
involution-lifting clause I.2.2(4), pp.409–411. The source inputs remain
explicit, including in the Sz(8) cover case.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped Pointwise
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}

/-- The original K embedded in its actual Tᵥ-orbit. -/
def firstEmbedding (T K : Subgroup G) (v : G) : K →* orbit T K v :=
  inclusion (le_conjugateSpanBy K (Tv T v))

/-- The literal moving conjugate of K embedded in the same orbit. -/
def secondEmbedding (T K : Subgroup G) (v : G) (t : Tv T v) : K →* orbit T K v :=
  ((orbit T K v).normalizerMonoidHom
    ⟨t, le_normalizer_conjugateSpanBy K (Tv T v) t.property⟩).toMonoidHom.comp
      (firstEmbedding T K v)

/-- The actual action of Tᵥ on its component orbit. -/
def orbitAction (T K : Subgroup G) (v : G) : Tv T v →* MulAut (orbit T K v) :=
  (orbit T K v).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy K (Tv T v)))

/-- The action kernel is the centralizer of the whole orbit inside Tᵥ. -/
theorem orbitAction_kernel (T K : Subgroup G) (v : G) :
    (orbitAction T K v).ker =
      (centralizer (orbit T K v : Set G)).subgroupOf (Tv T v) := by
  ext x
  change (orbit T K v).normalizerMonoidHom
    (inclusion (le_normalizer_conjugateSpanBy K (Tv T v)) x) = 1 ↔ _
  change inclusion (le_normalizer_conjugateSpanBy K (Tv T v)) x ∈
    (orbit T K v).normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- Actual factor coordinates, including the permutation and both possibly different markings. -/
structure PairFactors (d : Marking T K v) where
  moving : Tv T v
  moved : (moving : G) ∉ normalizer (K : Set G)
  orbit_eq : orbit T K v = K ⊔ K.map (MulAut.conj (moving : G)).toMonoidHom
  permutation : ∀ u : Tv T v,
    let K' := K.map (MulAut.conj (moving : G)).toMonoidHom
    (K.map (MulAut.conj (u : G)).toMonoidHom = K ∧
      K'.map (MulAut.conj (u : G)).toMonoidHom = K') ∨
    (K.map (MulAut.conj (u : G)).toMonoidHom = K' ∧
      K'.map (MulAut.conj (u : G)).toMonoidHom = K)
  firstEquiv : (K ⧸ center K) ≃* SuzukiMatrixGroup d.parameter
  secondEquiv : (K ⧸ center K) ≃* SuzukiMatrixGroup d.parameter
  first_eq : ∀ k : K, d.quotientMap (firstEmbedding T K v k) =
    (firstEquiv (QuotientGroup.mk' (center K) k), 1)
  second_eq : ∀ k : K, d.quotientMap (secondEmbedding T K v moving k) =
    (1, secondEquiv (QuotientGroup.mk' (center K) k))

namespace PairFactors
variable {d : Marking T K v} (c : PairFactors d)

/-- The component hypothesis makes the two marked embeddings commute. -/
theorem commute_factors (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v))) (k l : K) :
    Commute (firstEmbedding T K v k) (secondEmbedding T K v c.moving l) := by
  let t : Gv v := ⟨c.moving, c.moving.property.2⟩
  have he : ((K.subgroupOf (Gv v)).map (MulAut.conj t).toMonoidHom).map (Gv v).subtype =
      K.map (MulAut.conj (c.moving : G)).toMonoidHom := by
    rw [map_map]
    change ((K.subgroupOf (Gv v)).map
      ((MulAut.conj (c.moving : G)).toMonoidHom.comp (Gv v).subtype)) = _
    rw [← map_map, map_subgroupOf_eq_of_le hKG]
  have hne : K.subgroupOf (Gv v) ≠
      (K.subgroupOf (Gv v)).map (MulAut.conj t).toMonoidHom := by
    intro h
    have hh := congrArg (Subgroup.map (Gv v).subtype) h
    rw [he, map_subgroupOf_eq_of_le hKG] at hh
    exact c.moved (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hK.commutator_eq_bot_of_ne (hK.map_conj t) hne)
  have hk : (⟨k, hKG k.property⟩ : Gv v) ∈ K.subgroupOf (Gv v) := k.property
  have hl : (⟨l, hKG l.property⟩ : Gv v) ∈ K.subgroupOf (Gv v) := l.property
  exact Subtype.ext (congrArg Subtype.val (hc hk _ (mem_map_of_mem _ hl))).symm


/-- Every element of the actual orbit is a product from the two literal factors. -/
theorem factorization (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v))) (x : orbit T K v) :
    ∃ k l : K, firstEmbedding T K v k * secondEmbedding T K v c.moving l = x := by
  have hc : K ≤ centralizer (K.map (MulAut.conj (c.moving : G)).toMonoidHom : Set G) := by
    intro k hk y hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact (congrArg Subtype.val (c.commute_factors hKG hK ⟨k, hk⟩ ⟨l, hl⟩).eq).symm
  have hx : (x : G) ∈ (K : Set G) *
      (K.map (MulAut.conj (c.moving : G)).toMonoidHom : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right K _
      (hc.trans (centralizer_le_normalizer _)), ← c.orbit_eq]
    exact x.property
  obtain ⟨k, hk, y, ⟨l, hl, rfl⟩, hkl⟩ := hx
  exact ⟨⟨k, hk⟩, ⟨l, hl⟩, Subtype.ext hkl⟩

include c in
/-- The multiplier input for K implies the corresponding center bound for its pair. -/
theorem orbit_center_elementary (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)] : IsElementaryAbelian 2 (center (orbit T K v)) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨k, l, hkl⟩ := c.factorization hKG hK x.val
  have hq : d.quotientMap x.val = 1 := by
    change x.val ∈ d.quotientMap.ker
    rw [d.quotientMap_ker]
    exact x.property
  rw [← hkl, map_mul, c.first_eq, c.second_eq] at hq
  have hk : k ∈ center K := by
    apply (QuotientGroup.eq_one_iff k).mp
    apply c.firstEquiv.injective
    simpa using congrArg Prod.fst hq
  have hl : l ∈ center K := by
    apply (QuotientGroup.eq_one_iff l).mp
    apply c.secondEquiv.injective
    simpa using congrArg Prod.snd hq
  apply Subtype.ext
  change x.val ^ 2 = 1
  rw [← hkl, (c.commute_factors hKG hK k l).mul_pow, ← map_pow, ← map_pow,
    elemPow_eq_one_of_isElementaryAbelian k hk, elemPow_eq_one_of_isElementaryAbelian l hl,
    map_one, map_one, mul_one]

include c in
/-- The genuine single-factor lifting clause supplies involution lifts for the product. -/
theorem lift_pair_involutions (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (q : SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter) (hq : q ^ 2 = 1) :
    ∃ x : orbit T K v, x ^ 2 = 1 ∧ d.quotientMap x = q := by
  obtain ⟨k, hk, hqk⟩ := hlift (c.firstEquiv.symm q.1) (by
    rw [← map_pow, show q.1 ^ 2 = 1 from congrArg Prod.fst hq, map_one])
  obtain ⟨l, hl, hql⟩ := hlift (c.secondEquiv.symm q.2) (by
    rw [← map_pow, show q.2 ^ 2 = 1 from congrArg Prod.snd hq, map_one])
  refine ⟨firstEmbedding T K v k * secondEmbedding T K v c.moving l, ?_, ?_⟩
  · rw [(c.commute_factors hKG hK k l).mul_pow, ← map_pow, ← map_pow, hk, hl,
      map_one, map_one, mul_one]
  · rw [map_mul, c.first_eq, c.second_eq, hqk, hql,
      c.firstEquiv.apply_symm_apply, c.secondEquiv.apply_symm_apply]
    exact Prod.ext (mul_one _) (one_mul _)

end PairFactors
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
