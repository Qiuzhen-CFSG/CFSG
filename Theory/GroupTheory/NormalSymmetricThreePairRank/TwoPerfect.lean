module
public import Theory.GroupTheory.NormalSymmetricThreePairRank
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Two-perfect placement in a normal symmetric-three pair

The only normal symmetric-three subgroups of a symmetric-three pair are
its two coordinates. Ambient conjugation permutes them, so a two-perfect
actor fixes both. The rank-two placement theorem therefore needs no extra
factor-preservation assumptions.

Source: Aschbacher--Smith 13.7.4(1), printed p.937, and 13.8.5, p.947.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
local notation "S3" => Equiv.Perm (Fin 3)
variable {A : Type*} [Group A]
private def firstCoordinateEquiv {X : Type*} [Group X] (e : X ≃* (S3 × S3)) :
    (((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom) ≃* S3 where
  toFun x := (e x).1
  invFun x := ⟨e.symm (x, 1), by simp [Subgroup.mem_prod]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [e.apply_symm_apply]
    exact Prod.ext rfl x.property.2.symm
  right_inv x := by simp
  map_mul' x y := congrArg Prod.fst (e.map_mul (x : X) (y : X))

private theorem firstFactor_conjugate (N : Subgroup A) [N.Normal]
    (e : N ≃* (S3 × S3)) (a : A) :
    (firstFactor N e).map (MulAut.conj a).toMonoidHom = firstFactor N e ∨
      (firstFactor N e).map (MulAut.conj a).toMonoidHom = secondFactor N e := by
  let F := ((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom
  let f : MulAut N := MulAut.conjNormal a
  let B := (F.map f.toMonoidHom).map e.toMonoidHom
  let : F.Normal := inferInstanceAs (((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom).Normal
  let : (F.map f.toMonoidHom).Normal := Normal.map inferInstance _ f.surjective
  let : B.Normal := Normal.map inferInstance _ e.surjective
  let eb : B ≃* S3 := (e.subgroupMap (F.map f.toMonoidHom)).symm.trans
    ((f.subgroupMap F).symm.trans (firstCoordinateEquiv e))
  have hb := PermThreeProduct.normal_subgroup_eq_factor B eb
  have hm : (firstFactor N e).map (MulAut.conj a).toMonoidHom =
      (B.comap e.toMonoidHom).map N.subtype := by
    rw [show B.comap e.toMonoidHom = F.map f.toMonoidHom from
      comap_map_eq_self_of_injective e.injective _]
    rw [firstFactor, map_map, map_map]
    rfl
  rw [hm]
  exact hb.imp (fun h => by rw [h]; rfl) (fun h => by rw [h]; rfl)

private theorem stabilizer_top_of_twoPerfect_pair
    {D Ω : Type*} [Group D] [Finite D] [MulAction D Ω]
    (hD : IsPPerfect 2 D) (a b : Ω) (hpair : ∀ d : D, d • a = a ∨ d • a = b) :
    MulAction.stabilizer D a = ⊤ := by
  have horbit : MulAction.orbit D a ⊆ ({a, b} : Set Ω) := by
    rintro y ⟨d, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair d
  have hindex : (MulAction.stabilizer D a).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard horbit).trans (by simpa using Set.ncard_insert_le a {b})
  have hpos := (MulAction.stabilizer D a).index_ne_zero_of_finite
  have hc : (MulAction.stabilizer D a).index = 1 ∨
      (MulAction.stabilizer D a).index = 2 := by omega
  rcases hc with hc | hc
  · exact index_eq_one.mp hc
  · let _ := (MulAction.stabilizer D a).normal_of_index_eq_two hc
    apply hD _ inferInstance
    apply IsPGroup.of_card (n := 1)
    simpa only [← index_eq_card, pow_one] using hc

theorem twoPerfect_normalizes_first [Finite A]
    (N : Subgroup A) [N.Normal] (e : N ≃* (S3 × S3))
    (B : Subgroup A) (hB : IsPPerfect 2 B) : B ≤ normalizer (firstFactor N e : Set A) := by
  let _ : MulAction B (Subgroup A) := {
    smul := fun b C => C.map (MulAut.conj (b : A)).toMonoidHom
    one_smul := fun C => by
      change C.map (MulAut.conj (1 : A)).toMonoidHom = C
      rw [show (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A by ext x; simp]
      exact map_id C
    mul_smul := fun b c C => by
      change C.map _ = (C.map _).map _
      rw [map_map]
      congr 1
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, coe_mul]
      group }
  have hs : MulAction.stabilizer B (firstFactor N e) = ⊤ :=
    stabilizer_top_of_twoPerfect_pair hB (firstFactor N e) (secondFactor N e)
      (fun b => firstFactor_conjugate N e b)
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (show (⟨b, hb⟩ : B) ∈ MulAction.stabilizer B (firstFactor N e) by rw [hs]; trivial)

theorem twoPerfect_normalizes_second [Finite A]
    (N : Subgroup A) [N.Normal] (e : N ≃* (S3 × S3))
    (B : Subgroup A) (hB : IsPPerfect 2 B) : B ≤ normalizer (secondFactor N e : Set A) := by
  have he : firstFactor N (e.trans MulEquiv.prodComm) = secondFactor N e := by
    unfold firstFactor secondFactor
    congr 1
    ext x
    exact and_comm
  rw [← he]
  exact twoPerfect_normalizes_first N _ B hB

theorem le_pair_of_twoPerfect [Finite A]
    (N : Subgroup A) [N.Normal] (e : N ≃* (S3 × S3))
    (B : Subgroup A) (hB : IsPPerfect 2 B) (hrank : primeRank 3 A ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n) : B ≤ N :=
  le_pair N e B hB hrank horder (twoPerfect_normalizes_first N e B hB)
    (twoPerfect_normalizes_second N e B hB)
end Theory.GroupTheory.NormalSymmetricThreePairRank
