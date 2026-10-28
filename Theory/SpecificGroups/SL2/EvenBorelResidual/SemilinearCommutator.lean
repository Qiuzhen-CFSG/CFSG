module

public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear

/-!
# Cyclic semilinear commutators modulo their intrinsic two-core

Let B be the actual upper triangular Borel in PSL₂(F), for a finite field
F of characteristic two. For an arbitrary inner Borel twist of a field
actor, the entire cyclic action preserves B. Projecting its action
commutator C to Fˣ contains the field displacement image: lift a unit to B
and project its displacement by the generating actor. The projection kills
O₂(C), since Fˣ has odd order, giving the required lower bound on |C/O₂(C)|.

The general transport lemmas send both the subgroup and its cyclic actor
through a genuine group equivalence. They identify the commutator groups
and their quotients by the intrinsic p-cores, hence preserve cardinality.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
These are the quotient bound and transport used in the L₂ branch; the
exceptional-degree calculation and final source assembly are separate.
-/

@[expose] public section

open Subgroup
open scoped Pointwise MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.SemilinearCommutator

/-- Stability under the generator gives containment for the whole cyclic action. -/
theorem cyclic_commutator_le {G : Type*} [Group G] (B : Subgroup G)
    (a : MulAut G) (ha : B.map a.toMonoidHom = B) :
    commutatorSubgroup (zpowers a) G B ≤ B := by
  have hle : zpowers a ≤ MulAction.stabilizer (MulAut G) B := zpowers_le.mpr ha
  change Subgroup.closure _ ≤ B
  apply (Subgroup.closure_le B).2
  rintro _ ⟨b, x, hx, rfl⟩
  apply B.mul_mem (B.inv_mem hx)
  have hb : B.map b.val.toMonoidHom = B := hle b.property
  have hm := mem_map_of_mem b.val.toMonoidHom hx
  rwa [hb] at hm

/-- Transport the actual cyclic-action commutator, with both inputs mapped. -/
theorem cyclic_commutator_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (a : MulAut G) :
    (commutatorSubgroup (zpowers a) G B).map e.toMonoidHom =
      commutatorSubgroup (zpowers (MulAut.congr e a)) H (B.map e.toMonoidHom) := by
  have hA : (zpowers a).map (MulAut.congr e).toMonoidHom =
      zpowers (MulAut.congr e a) := MonoidHom.map_zpowers (MulAut.congr e).toMonoidHom a
  rw [commutatorSubgroup, commutatorSubgroup, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, y, hy, rfl⟩, rfl⟩
    have hb : MulAut.congr e b.val ∈ zpowers (MulAut.congr e a) := by
      rw [← hA]
      exact mem_map_of_mem (MulAut.congr e).toMonoidHom b.property
    refine ⟨⟨MulAut.congr e b.val, hb⟩, e y, mem_map_of_mem e.toMonoidHom hy, ?_⟩
    change e (y⁻¹ * b.val y) = (e y)⁻¹ * (MulAut.congr e b.val) (e y)
    simp
  · rintro ⟨b, _, ⟨y, hy, rfl⟩, rfl⟩
    have hb : (b : MulAut H) ∈ (zpowers a).map (MulAut.congr e).toMonoidHom := by
      simpa only [hA] using b.property
    obtain ⟨c, hc, he⟩ := hb
    refine ⟨y⁻¹ * c y, ⟨⟨c, hc⟩, y, hy, rfl⟩, ?_⟩
    change e (y⁻¹ * c y) = (e y)⁻¹ * b.val (e y)
    rw [← he]
    simp

/-- The restriction of a group equivalence to the cyclic-action commutator. -/
noncomputable def cyclic_commutator_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (a : MulAut G) :
    commutatorSubgroup (zpowers a) G B ≃*
      commutatorSubgroup (zpowers (MulAut.congr e a)) H (B.map e.toMonoidHom) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (cyclic_commutator_map e B a))

/-- Intrinsic p-core quotients of cyclic-action commutators transport canonically. -/
noncomputable def cyclic_commutator_quotient_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (a : MulAut G) (p : ℕ) :
    let C := commutatorSubgroup (zpowers a) G B
    let D := commutatorSubgroup (zpowers (MulAut.congr e a)) H (B.map e.toMonoidHom)
    C ⧸ pCore p C ≃* D ⧸ pCore p D :=
  QuotientGroup.congr _ _ (cyclic_commutator_equiv e B a)
    (pCore_map_iso p (cyclic_commutator_equiv e B a))

/-- In particular, every genuine group equivalence preserves the quotient order. -/
theorem cyclic_commutator_quotient_card {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (a : MulAut G) (p : ℕ) :
    let C := commutatorSubgroup (zpowers a) G B
    let D := commutatorSubgroup (zpowers (MulAut.congr e a)) H (B.map e.toMonoidHom)
    Nat.card (C ⧸ pCore p C) = Nat.card (D ⧸ pCore p D) :=
  Nat.card_congr (cyclic_commutator_quotient_equiv e B a p).toEquiv

private theorem card_range_le_quotient_twoCore
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hodd : Odd (Nat.card H)) :
    Nat.card f.range ≤ Nat.card (G ⧸ pCore 2 G) := by
  have hker : pCore 2 G ≤ f.rangeRestrict.ker := by
    intro x hx
    apply Subtype.ext
    change f x = 1
    obtain ⟨k, hk⟩ := pCore_isPGroup (⟨x, hx⟩ : pCore 2 G)
    have hf : f x ^ (2 ^ k) = 1 := by
      rw [← map_pow, show x ^ (2 ^ k) = 1 from congrArg Subtype.val hk, map_one]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hodd.coprime_two_left.pow_left k)
      (orderOf_dvd_of_pow_eq_one hf) (orderOf_dvd_natCard _))
  let q := QuotientGroup.lift (pCore 2 G) f.rangeRestrict hker
  apply Nat.card_le_card_of_surjective q
  intro y
  obtain ⟨x, hx⟩ := f.rangeRestrict_surjective y
  exact ⟨QuotientGroup.mk x, hx⟩

open OddBorel Semilinear Atlas FiniteField.BinaryTorusInvolution
variable (F : Type*) [Field F]

/-- Every inner Borel twist of a field actor preserves the Borel. -/
theorem semilinear_map_borel (g : borel F) (σ : F ≃+* F) :
    (borel F).map (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ).toMonoidHom =
      borel F := by
  change (borel F).map ((MulAut.conj (g : PSL(2,F))).toMonoidHom.comp
    (fieldEquivPSL 2 σ).toMonoidHom) = _
  rw [← Subgroup.map_map, field_map_borel]
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer g.property)

/-- All displacements by powers of the semilinear actor remain in the Borel. -/
theorem commutator_le_borel (g : borel F) (σ : F ≃+* F) :
    commutatorSubgroup (zpowers (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ))
      PSL(2,F) (borel F) ≤ borel F :=
  cyclic_commutator_le _ _ (semilinear_map_borel F g σ)

variable [CharP F 2]

/-- Restrict the Borel torus projection to the actual cyclic-action commutator. -/
noncomputable def commutatorProjection (g : borel F) (σ : F ≃+* F) :
    commutatorSubgroup (zpowers (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ))
      PSL(2,F) (borel F) →* Fˣ :=
  (torusProjection F).comp (inclusion (commutator_le_borel F g σ))

/-- The field displacement image is contained in the projected commutator. -/
theorem displacement_range_le_projection_range (g : borel F) (σ : F ≃+* F) :
    (displacement σ).range ≤ (commutatorProjection F g σ).range := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨x, hx⟩ := torusProjection_surjective F u
  have hc : (x : PSL(2,F))⁻¹ *
      (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) x ∈
      commutatorSubgroup (zpowers (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ))
        PSL(2,F) (borel F) :=
    subset_closure ⟨⟨_, mem_zpowers _⟩, x, x.property, rfl⟩
  refine ⟨⟨_, hc⟩, ?_⟩
  change torusProjection F (x⁻¹ * borelActor F g σ x) =
    Units.map σ.toMonoidHom u * u⁻¹
  rw [map_mul, map_inv, torusProjection_borelActor, hx, mul_comm]

variable [Finite F]

private theorem odd_card_units : Odd (Nat.card Fˣ) := by
  let := Fintype.ofFinite F
  have he : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
  rw [Nat.card_units]
  exact Nat.Even.sub_odd (by have := Finite.one_lt_card (α := F); omega) he odd_one

/-- The field displacement order bounds the intrinsic two-core quotient from below,
including for inner twists and actors of arbitrary order. -/
theorem displacement_card_le_commutator_quotient (g : borel F) (σ : F ≃+* F) :
    let C := commutatorSubgroup
      (zpowers (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ)) PSL(2,F) (borel F)
    Nat.card (displacement σ).range ≤ Nat.card (C ⧸ pCore 2 C) := by
  have hle := displacement_range_le_projection_range F g σ
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (card_range_le_quotient_twoCore (commutatorProjection F g σ) (odd_card_units F))

end Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.SemilinearCommutator
