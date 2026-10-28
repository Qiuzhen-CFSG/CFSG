module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NormalClosure
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# Movement of normal-closure residuals in S₃ × S₃

The odd residual has order nine. Coprime commutator idempotence therefore
makes the residual of a two-subgroup's normal closure its own commutator
with that subgroup. Every full Sylow two-subgroup moves the whole odd
residual: this is checked on the coordinate Sylow and transported by
conjugacy. Consequently a cubic commutator image forces the actor to have
order two; its nonidentity element acts by inversion.

Source: Aschbacher--Smith, 15.2.3(1), printed p.1105. The Chapter15 source
application retains the actual intersection-core and conjugation image.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup
private theorem coprime_commutator_idempotent
    {G : Type*} [Group G] [Finite G]
    (Q R : Subgroup G) (hnorm : R ≤ normalizer (Q : Set G))
    (hsolv : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card R) (Nat.card Q)) :
    ⁅⁅Q,R⁆,R⁆ = ⁅Q,R⁆ := by
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right Q R)
  let _ : Normalizes R Q := ⟨hnorm⟩
  have hidem := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := Q) (A := R) hsolv hcop
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator Q R hnorm
  have hiter : (commutatorAction₂ (A := R) (G := Q)).map Q.subtype ≤ ⁅⁅Q,R⁆,R⁆ := by
    rw [commutatorAction₂,commutatorSubgroup,MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨q,⟨r,a,ha,rfl⟩,rfl⟩
    have haM : (a : G) ∈ ⁅Q,R⁆ := by
      rw [← hmap]
      exact mem_map_of_mem Q.subtype ha
    have hmem := commutator_mem_commutator ((⁅Q,R⁆).inv_mem haM) r.property
    change (a : G)⁻¹ * ((r : G) * (a : G) * (r : G)⁻¹) ∈ (⁅⁅Q,R⁆,R⁆ : Subgroup G)
    simpa only [commutatorElement_def,inv_inv,
      conjMulDistribMulActionOfLeNormalizer_smul_coe,mul_assoc] using hmem
  rwa [hidem,hmap] at hiter

end Subgroup

namespace SymmetricThreeProductResidual
theorem residual_self_commutator
    {D : Type*} [Group D]
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (P : Sylow 2 D) (R : Subgroup D) (hle : R ≤ (P : Subgroup D)) :
    let Y := (pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype
    ⁅Y,R⁆ = Y := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have hA : Nat.card (pResidual 2 D) = 3 ^ 2 := by
    have hh := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) => Nat.card H)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rw [card_map_of_injective e.injective,residual_card] at hh
    exact hh
  have hR : IsPGroup 2 R := P.isPGroup'.to_le hle
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hR
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (pResidual 2 D)) := by
    rw [hA,hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n |>.pow_right 2
  let : IsMulCommutative (pResidual 2 D) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hA
  let : CommGroup (pResidual 2 D) := IsMulCommutative.instCommGroup
  dsimp only
  rw [normalClosure_residual_eq_commutator e P R hle]
  exact coprime_commutator_idempotent _ _ le_normalizer_of_normal inferInstance hcop
end SymmetricThreeProductResidual



namespace SymmetricThreeProductResidual
private theorem model_full_sylow_commutator :
    ⁅pResidual 2 SymmetricThreeProduct.G, SymmetricThreeProduct.borel⁆ =
      pResidual 2 SymmetricThreeProduct.G := by
  apply le_antisymm (commutator_le_left _ _) ?_
  intro a ha
  have hinv : ∀ a : SymmetricThreeProduct.G,
      a ∈ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) →
        ⁅a⁻¹, (Equiv.swap 1 2, Equiv.swap 1 2)⁆ = a := by
    simp only [Subgroup.mem_prod, Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  rw [residual_eq] at ha
  rw [← hinv a ha]
  apply commutator_mem_commutator
  · rw [residual_eq]
    exact inv_mem ha
  · decide +kernel

theorem full_sylow_commutator {D : Type*} [Group D]
    (e : D ≃* SymmetricThreeProduct.G) (P : Sylow 2 D) :
    ⁅pResidual 2 D, (P : Subgroup D)⁆ = pResidual 2 D := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have model (Q : Sylow 2 SymmetricThreeProduct.G) :
      ⁅pResidual 2 SymmetricThreeProduct.G, (Q : Subgroup SymmetricThreeProduct.G)⁆ =
        pResidual 2 SymmetricThreeProduct.G := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SymmetricThreeProduct.G SymmetricThreeProduct.sylow Q
    have hB : SymmetricThreeProduct.borel.map (MulAut.conj g).toMonoidHom = Q := by
      change ((g • SymmetricThreeProduct.sylow : Sylow 2 SymmetricThreeProduct.G) :
        Subgroup SymmetricThreeProduct.G) = _
      rw [hg]
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) model_full_sylow_commutator
    rwa [map_commutator, map_pResidual_of_surjective 2 _ (MulAut.conj g).surjective, hB] at hh
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_commutator, map_pResidual_of_surjective 2 _ e.surjective]
  exact model (P.mapSurjective (f := e.toMonoidHom) e.surjective)

theorem cubic_actor_card {D : Type*} [Group D]
    (e : D ≃* SymmetricThreeProduct.G) (P : Sylow 2 D)
    (R : Subgroup D) (hle : R ≤ (P : Subgroup D))
    (hc : Nat.card (⁅pResidual 2 D, R⁆ : Subgroup D) = 3) : Nat.card R = 2 := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have hD : Nat.card D = 36 := (Nat.card_congr e.toEquiv).trans SymmetricThreeProduct.card_group
  have hP : Nat.card P = 4 := by rw [P.card_eq_multiplicity, hD]; decide +kernel
  have hd : Nat.card R ∣ 4 := hP ▸ card_dvd_of_le hle
  have hpos := Nat.card_pos (α := R)
  have hu : Nat.card R ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hne1 : Nat.card R ≠ 1 := by
    intro hh
    rw [card_eq_one.mp hh, commutator_bot_right, card_bot] at hc
    contradiction
  have hne4 : Nat.card R ≠ 4 := by
    intro hh
    have heq : R = P := eq_of_le_of_card_ge hle (by rw [hh,hP])
    rw [heq, full_sylow_commutator e P] at hc
    have hm := congrArg (fun H : Subgroup SymmetricThreeProduct.G => Nat.card H)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rw [card_map_of_injective e.injective, residual_card, hc] at hm
    contradiction
  interval_cases hh : Nat.card R <;> simp_all

theorem cubic_actor_inverts {D : Type*} [Group D]
    (e : D ≃* SymmetricThreeProduct.G) (P : Sylow 2 D)
    (R : Subgroup D) (hle : R ≤ (P : Subgroup D))
    (hc : Nat.card (⁅pResidual 2 D, R⁆ : Subgroup D) = 3) :
    Nat.card R = 2 ∧ ∀ r ∈ R, r ≠ 1 →
      ∀ y ∈ ⁅pResidual 2 D,R⁆, r * y * r⁻¹ = y⁻¹ := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have hR := cubic_actor_card e P R hle hc
  have hself : ⁅⁅pResidual 2 D,R⁆,R⁆ = ⁅pResidual 2 D,R⁆ := by
    have h := residual_self_commutator e P R hle
    simpa only [normalClosure_residual_eq_commutator e P R hle] using h
  refine ⟨hR, fun r hr hrne y hy => ?_⟩
  by_cases hyne : y = 1
  · simp [hyne]
  exact cyclicThree_full_commutator_inverts _ _ hc hR
    (normalizer_commutator_ge_right _ _) hself y r hy hyne hr hrne
end SymmetricThreeProductResidual

