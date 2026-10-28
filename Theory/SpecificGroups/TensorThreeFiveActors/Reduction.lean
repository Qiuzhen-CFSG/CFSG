module

public import Theory.SpecificGroups.TensorThreeFiveLocalQuotients
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PResidual.Defs

/-!
# Product and transport reductions for cubic tensor actors

A Sylow subgroup of a product is the product of its projections. When the first
factor is solvable, the solvable residual and its Sylow-relative normalizer lie
entirely in the second factor. Isomorphisms preserve these literal subgroups and
the quotient by the intrinsic two-core.

The last theorem combines two separate finite calculations: elimination of
mixed or diagonal actors, and classification in the five-point factor. Those
calculations are explicit premises, not a proved catalogue. Source application:
Aschbacher–Smith, Lemma 14.4.10(1), printed p.1010/PDF p.1027, under the models
of 14.4.2(5), printed p.1006/PDF p.1023 (combined 1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.TensorThreeFiveActors


/-- The independent-factor assertion required to exclude mixed and diagonal actors.
This is an input to the assembly below, not an assumed model catalogue. -/
def ProductSplitting (D : Type*) [Group D] : Prop :=
  ∀ (Q : Sylow 2 (Equiv.Perm (Fin 3) × D))
    (A : Subgroup (Equiv.Perm (Fin 3) × D)),
    (Q : Subgroup (Equiv.Perm (Fin 3) × D)) ≤ normalizer (A : Set (Equiv.Perm (Fin 3) × D)) → IsPPerfect 2 A →
    Nat.card (A ⧸ pCore 2 A) = 3 →
    A = (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) ∨
    ∃ B : Subgroup D, A = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod B ∧
      IsPPerfect 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3

/-- The remaining one-factor calculation, with the actual Sylow intersection. -/
def FactorActors (D : Type*) [Group D] : Prop :=
  ∀ (Q : Sylow 2 D) (B : Subgroup D),
    (Q : Subgroup D) ≤ normalizer (B : Set D) → IsPPerfect 2 B →
    Nat.card (B ⧸ pCore 2 B) = 3 →
    B = solvableResidual D ⊓ normalizer
      (((Q : Subgroup D) ⊓ solvableResidual D : Subgroup D) : Set D)

variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]

/-- A Sylow subgroup of a direct product contains its two independent projections. -/
theorem sylow_eq_prod (Q : Sylow 2 (E × D)) :
    (Q : Subgroup (E × D)) =
      (Q.map (MonoidHom.fst E D)).prod (Q.map (MonoidHom.snd E D)) := by
  let L := Q.map (MonoidHom.fst E D)
  let R := Q.map (MonoidHom.snd E D)
  have hp : IsPGroup 2 (L.prod R) := by
    obtain ⟨m, hm⟩ := (Q.isPGroup'.map (MonoidHom.fst E D)).exists_card_eq
    obtain ⟨n, hn⟩ := (Q.isPGroup'.map (MonoidHom.snd E D)).exists_card_eq
    apply IsPGroup.of_card (n := m + n)
    rw [Nat.card_congr (prodEquiv L R).toEquiv, Nat.card_prod, hm, hn, pow_add]
  symm
  apply Q.is_maximal' hp
  intro x hx
  exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

omit [Finite E] in
/-- With a solvable first factor, the residual is exactly the second residual. -/
theorem residual_prod [Group.IsSolvable E] :
    solvableResidual (E × D) = (⊥ : Subgroup E).prod (solvableResidual D) := by
  let e : (⊥ : Subgroup E).prod (solvableResidual D) ≃* solvableResidual D :=
    (prodEquiv _ _).trans .uniqueProd
  let : Group.IsPerfect ((⊥ : Subgroup E).prod (solvableResidual D)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply le_antisymm _ (le_solvableResidual_of_isPerfect _)
  apply le_prod_iff.mpr
  exact ⟨by simpa only [solvableResidual_eq_bot] using
    map_solvableResidual_le (MonoidHom.fst E D),
    map_solvableResidual_le (MonoidHom.snd E D)⟩

omit [Finite E] [Finite D] in
private theorem normalizer_bot_prod (R : Subgroup D) :
    normalizer (((⊥ : Subgroup E).prod R) : Set (E × D)) =
      (⊤ : Subgroup E).prod (normalizer (R : Set D)) := by
  ext x
  change (∀ y : E × D, y ∈ (⊥ : Subgroup E).prod R ↔
    x * y * x⁻¹ ∈ (⊥ : Subgroup E).prod R) ↔ _
  constructor
  · intro h
    refine ⟨mem_top _, ?_⟩
    intro y
    have hy := h (1, y)
    change (1 = (1 : E) ∧ y ∈ R) ↔
      (x.1 * 1 * x.1⁻¹ = 1 ∧ x.2 * y * x.2⁻¹ ∈ R) at hy
    change y ∈ R ↔ x.2 * y * x.2⁻¹ ∈ R
    simpa only [mul_one, mul_inv_cancel, true_and] using hy
  · rintro ⟨_, h⟩ y
    change (y.1 = 1 ∧ y.2 ∈ R) ↔
      (x.1 * y.1 * x.1⁻¹ = 1 ∧ x.2 * y.2 * x.2⁻¹ ∈ R)
    exact and_congr (by simp) (h y.2)

/-- The literal residual-relative normalizer is compatible with product coordinates. -/
theorem relativeNormalizer_prod [Group.IsSolvable E] (Q : Sylow 2 (E × D)) :
    solvableResidual (E × D) ⊓ normalizer
      (((Q : Subgroup (E × D)) ⊓ solvableResidual (E × D) : Subgroup (E × D)) : Set (E × D)) =
    (⊥ : Subgroup E).prod (solvableResidual D ⊓ normalizer
      (((Q.map (MonoidHom.snd E D)) ⊓ solvableResidual D : Subgroup D) : Set D)) := by
  have hi : (Q : Subgroup (E × D)) ⊓ ((⊥ : Subgroup E).prod (solvableResidual D)) =
      (⊥ : Subgroup E).prod ((Q.map (MonoidHom.snd E D)) ⊓ solvableResidual D) := by
    conv_lhs => rw [sylow_eq_prod Q]
    ext x
    simp only [mem_inf, mem_prod, mem_bot]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, he, hr⟩
      exact ⟨he, h₂, hr⟩
    · rintro ⟨he, h₂, hr⟩
      exact ⟨⟨he ▸ (Q.map (MonoidHom.fst E D)).one_mem, h₂⟩, he, hr⟩
  rw [residual_prod, hi, normalizer_bot_prod]
  ext x
  simp only [mem_inf, mem_prod, mem_bot, mem_top, true_and, and_assoc]

/-- The three-point symmetric group is solvable through its sign quotient. -/
theorem s3_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

/-- The first cubic factor is literally the three-core of S₃. -/
theorem s3_threeCore_eq : pCore 3 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num
  symm
  apply eq_of_le_of_card_ge
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using hc)⟩
  · rw [hc, TensorThreeFive.s3_threeCore_card]

end Theory.SpecificGroups.TensorThreeFiveActors

namespace Theory.SpecificGroups.TensorThreeFiveActors
open Subgroup
variable {J D : Type*} [Group J] [Group D] [Finite J] [Finite D]

omit [Finite D] in
/-- Actual isomorphisms transport both actor hypotheses and the relative normalizer. -/
theorem actors_of_equiv (e : J ≃* D)
    (hactors : ∀ (Q : Sylow 2 D) (A : Subgroup D),
      (Q : Subgroup D) ≤ normalizer (A : Set D) → IsPPerfect 2 A →
      Nat.card (A ⧸ pCore 2 A) = 3 →
      A = pCore 3 D ∨ A = solvableResidual D ⊓
        normalizer (((Q : Subgroup D) ⊓ solvableResidual D : Subgroup D) : Set D))
    (Q : Sylow 2 J) (A : Subgroup J)
    (hn : (Q : Subgroup J) ≤ normalizer (A : Set J))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 J ∨ A = solvableResidual J ⊓
      normalizer (((Q : Subgroup J) ⊓ solvableResidual J : Subgroup J) : Set J) := by
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map e.toMonoidHom
  let ea : A ≃* A' := e.subgroupMap A
  have hn' : (Q' : Subgroup D) ≤ normalizer (A' : Set D) := by
    exact (map_mono hn).trans (A.le_normalizer_map e.toMonoidHom)
  have hp' : IsPPerfect 2 A' := hp.of_surjective ea.toMonoidHom ea.surjective
  have hc' : Nat.card (A' ⧸ pCore 2 A') = 3 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact hc
  rcases hactors Q' A' hn' hp' hc' with h | h
  · left
    apply map_injective (f := e.toMonoidHom) e.injective
    exact h.trans (pCore_map_iso 3 e).symm
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_inf _ _ _ e.injective, map_solvableResidual_eq _ e.surjective,
      map_equiv_normalizer_eq, map_inf _ _ _ e.injective,
      map_solvableResidual_eq _ e.surjective]
    exact h

/-- A split actor is classified by the calculation in its second factor.
The splitting premise is responsible for excluding mixed and diagonal actors. -/
theorem product_actors_of_factors
    (hcore : pCore 3 D = ⊥)
    (hsplit : ProductSplitting D) (hfive : FactorActors D)
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × D))
    (A : Subgroup (Equiv.Perm (Fin 3) × D))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × D)) ≤ normalizer (A : Set (Equiv.Perm (Fin 3) × D)))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 (Equiv.Perm (Fin 3) × D) ∨
      A = solvableResidual (Equiv.Perm (Fin 3) × D) ⊓ normalizer
        (((Q : Subgroup (Equiv.Perm (Fin 3) × D)) ⊓ solvableResidual (Equiv.Perm (Fin 3) × D) : Subgroup (Equiv.Perm (Fin 3) × D)) : Set (Equiv.Perm (Fin 3) × D)) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := s3_solvable
  rcases hsplit Q A hn hp hc with h | ⟨B, hB, hBp, hBc⟩
  · left
    simpa only [pCore_prod, hcore] using h
  · right
    let q := MonoidHom.snd (Equiv.Perm (Fin 3)) D
    let Q' := Q.mapSurjective (f := q) (fun d => ⟨(1, d), rfl⟩)
    have hmap : A.map q = B := by
      rw [hB]
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha.2
      · intro hb
        exact ⟨(1, b), ⟨rfl, hb⟩, rfl⟩
    have hBn : (Q' : Subgroup D) ≤ normalizer (B : Set D) := by
      rw [← hmap]
      exact (map_mono hn).trans (A.le_normalizer_map q)
    rw [hB, relativeNormalizer_prod Q]
    congr 1
    exact hfive Q' B hBn hBp hBc
end Theory.SpecificGroups.TensorThreeFiveActors

end
