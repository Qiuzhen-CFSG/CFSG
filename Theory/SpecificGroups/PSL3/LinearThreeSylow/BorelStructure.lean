module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Characteristic two and solvability of marked PSL₃ Borels

A Borel element centralizing the upper unitriangular group has scalar
diagonal. Its diagonal factor therefore vanishes in the projective quotient,
so the Borel has a self-centralizing two-core. The torus quotient also proves
solvability. Sylow conjugacy treats every marked Sylow, and surjective maps
with two-group kernel give both facts for central covers. The binary field
has trivial torus, so its Sylow two-subgroups are self-normalizing.

Source: the intrinsic Borel calculation in Aschbacher–Smith E.6.8,
printed p.248 (combined manuscript, 1 March 2004). Matrix factorization
and the actual scalar kernel are supplied by `CartanActions.BorelQuotient`.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.BorelStructure
variable (F : Type*) [Field F] [Finite F]

theorem borel_inf_centralizer_unipotent_le :
    borel F ⊓ centralizer (unipotent F : Set PSL(3,F)) ≤ unipotent F := by
  rintro x ⟨⟨g,hg,rfl⟩,hc⟩
  have hcomm (v : U F) : g * specialLinear F v = specialLinear F v * g := by
    have hv : specialLinear F v ∈ unipotentSL F := (specialLinear_range F).le ⟨v,rfl⟩
    have hconj : g * specialLinear F v * g⁻¹ ∈ unipotentSL F :=
      (mem_normalizer_iff.mp (borelSL_le_normalizer_unipotentSL F hg) _).mp hv
    have hp : projection F (g * specialLinear F v * g⁻¹) = projection F (specialLinear F v) := by
      simp only [map_mul, map_inv]
      rw [← hc _ (mem_map_of_mem (projection F) hv), mul_inv_cancel_right]
    have he : (⟨g * specialLinear F v * g⁻¹, hconj.2⟩ : lineLocalSL F) =
        ⟨specialLinear F v, hv.2⟩ := lineLocal_projection_injective F hp
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  have he01 := congrArg (fun a : SL(3,F) => a.val 0 1) (hcomm ⟨1,0,0⟩)
  have he12 := congrArg (fun a : SL(3,F) => a.val 1 2) (hcomm ⟨0,1,0⟩)
  change (g.val * matrix F ⟨1,0,0⟩) 0 1 = (matrix F ⟨1,0,0⟩ * g.val) 0 1 at he01
  change (g.val * matrix F ⟨0,1,0⟩) 1 2 = (matrix F ⟨0,1,0⟩ * g.val) 1 2 at he12
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at he01 he12
  have h01 : g.val 0 0 = g.val 1 1 := add_right_cancel (he01.trans (add_comm _ _))
  have h12 : g.val 1 1 = g.val 2 2 := add_right_cancel (he12.trans (add_comm _ _))
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hg
  have hcube : g.val 0 0 ^ 3 = 1 := by
    have hd := g.property
    rw [Matrix.det_fin_three, h10,h20,h21, ← h12, ← h01] at hd
    simpa [pow_succ, mul_assoc] using hd
  obtain ⟨d,u,hu,he⟩ := BorelQuotient.borelSL_factorization F g hg
  have hu00 := ((mem_pointLocalSL_iff F u).mp hu.1).1
  have hu22 := ((mem_lineLocalSL_iff F u).mp hu.2).2.2
  have hd0 : g.val 0 0 = (d.1 : F) := by
    rw [he, SpecialLinearGroup.coe_mul, torusSL_val, Matrix.mul_diagonal]
    simp [hu00]
  have hd2 : g.val 2 2 = (d.2 : F) := by
    rw [he, SpecialLinearGroup.coe_mul, torusSL_val, Matrix.mul_diagonal]
    simp [hu22]
  have ht : torusMap F d = 1 := (BorelQuotient.torusMap_eq_one_iff F d).mpr
    ⟨Units.ext (hd0.symm.trans ((h01.trans h12).trans hd2)),
      Units.ext (by simpa [hd0] using hcube)⟩
  rw [he, map_mul]
  change projection F u * torusMap F d ∈ unipotent F
  rw [ht, mul_one]
  exact mem_map_of_mem _ hu

theorem borel_core_selfCentralizing {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    centralizer (pCore 2 (borel F) : Set (borel F)) ≤ pCore 2 (borel F) := by
  rw [BorelQuotient.twoCore_eq F hF]
  intro x hx
  apply borel_inf_centralizer_unipotent_le F
  refine ⟨x.property, ?_⟩
  intro u hu
  exact congrArg Subtype.val (hx ⟨u,unipotent_le_borel F hu⟩ hu)

theorem borel_isSolvable {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Group.IsSolvable (borel F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := (pCore_isPGroup (p := 2) (G := borel F)).isNilpotent
  let e := BorelQuotient.quotientTorusEquiv F hF
  let : Group.IsSolvable (borel F ⧸ pCore 2 (borel F)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  apply Group.isSolvable_of_ker_le_range (pCore 2 (borel F)).subtype
    (QuotientGroup.mk' (pCore 2 (borel F)))
  rw [QuotientGroup.ker_mk', range_subtype]

end Matrix.PSL3.LinearThree.BorelStructure

namespace Matrix.PSL3.LinearThree.BorelStructure
variable (F : Type*) [Field F] [Finite F]

theorem sylowNormalizer_core_selfCentralizing {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F)) :
    centralizer (pCore 2 (normalizer (S : Set PSL(3,F))) :
      Set (normalizer (S : Set PSL(3,F)))) ≤ pCore 2 (normalizer (S : Set PSL(3,F))) :=
  (Theory.Quasithin.centralizer_pCore_le_iff 2
    (BorelQuotient.sylowNormalizerEquiv F hn hF S)).mpr (borel_core_selfCentralizing F hF)

theorem sylowNormalizer_isSolvable {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F)) :
    Group.IsSolvable (normalizer (S : Set PSL(3,F))) := by
  let := borel_isSolvable F hF
  exact Group.isSolvable_of_isSolvable_injective
    (f := (BorelQuotient.sylowNormalizerEquiv F hn hF S).toMonoidHom)
    (BorelQuotient.sylowNormalizerEquiv F hn hF S).injective

variable {J : Type*} [Group J] [Finite J]

theorem sylowNormalizer_core_selfCentralizing_of_surjective {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (f : J →* PSL(3,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 J) :
    centralizer (pCore 2 (normalizer (S : Set J)) : Set (normalizer (S : Set J))) ≤
      pCore 2 (normalizer (S : Set J)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply f.centralizer_pCore_subgroup_of_image hk (normalizer (S : Set J))
  rw [S.normalizer_map_surjective f hf]
  exact sylowNormalizer_core_selfCentralizing F hn hF (S.mapSurjective hf)

theorem sylowNormalizer_isSolvable_of_surjective {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (f : J →* PSL(3,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 J) :
    Group.IsSolvable (normalizer (S : Set J)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normalizer (S : Set J)
  let g := f.subgroupMap N
  let : Group.IsSolvable (N.map f) := by
    rw [S.normalizer_map_surjective f hf]
    exact sylowNormalizer_isSolvable F hn hF (S.mapSurjective hf)
  have hkg : IsPGroup 2 g.ker := by
    dsimp [g]
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let := hkg.isNilpotent
  apply Group.isSolvable_of_ker_le_range g.ker.subtype g
  rw [range_subtype]

end Matrix.PSL3.LinearThree.BorelStructure

namespace Matrix.PSL3.LinearThree.BorelStructure
variable (F : Type*) [Field F] [Finite F]

/-- Over the binary field the diagonal torus is trivial. -/
theorem borel_eq_unipotent_of_card_two (hF : Nat.card F = 2) : borel F = unipotent F := by
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  let : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  apply le_antisymm _ (unipotent_le_borel F)
  intro g hg
  obtain ⟨d,u,hu,rfl⟩ := BorelQuotient.borel_factorization F g hg
  have hd : d = 1 := Subsingleton.elim _ _
  simpa only [hd, map_one, mul_one] using hu

/-- Every Sylow two-subgroup of PSL₃(2) is self-normalizing. -/
theorem normalizer_eq_self_of_card_two (hF : Nat.card F = 2) (S : Sylow 2 PSL(3,F)) :
    normalizer (S : Set PSL(3,F)) = (S : Subgroup PSL(3,F)) := by
  obtain ⟨g,hu,hb⟩ := BorelQuotient.sylow_normalizer_conjugate F
    (n := 1) (by decide) (by simpa using hF) S
  rw [borel_eq_unipotent_of_card_two F hF] at hb
  exact hb.symm.trans hu
end Matrix.PSL3.LinearThree.BorelStructure

namespace Matrix.PSL3.LinearThree.BorelStructure
variable (F : Type*) [Field F] [Finite F]

theorem three_not_dvd_card_borel_of_odd {n : ℕ} (hn : Odd n)
    (hF : Nat.card F = 2 ^ n) : ¬ 3 ∣ Nat.card (borel F) := by
  have hmod : 2 ^ n % 3 = 2 := by
    obtain ⟨k,rfl⟩ := hn
    simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have hnt : ¬ 3 ∣ (2 ^ n - 1) := by
    have hp := pow_pos (by decide : 0 < (2:ℕ)) n
    omega
  have ht : ¬ 3 ∣ Nat.card (torus F) := by
    intro ht
    have hd := dvd_mul_of_dvd_left ht (Nat.gcd 3 (Nat.card F - 1))
    rw [BorelQuotient.card_torus_mul_scalar F, hF] at hd
    exact hnt (Nat.prime_three.dvd_of_dvd_pow hd)
  have hu : ¬ 3 ∣ Nat.card (unipotent F) := by
    rw [card_unipotent, hF]
    intro hu
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow hu))
  have hc := (BorelQuotient.borel_complement F hF).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv] at hc
  rw [← hc]
  exact Nat.prime_three.not_dvd_mul hu ht

theorem three_not_dvd_card_sylowNormalizer_of_odd {n : ℕ} (hn : Odd n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F)) :
    ¬ 3 ∣ Nat.card (normalizer (S : Set PSL(3,F))) := by
  have hnpos : 0 < n := hn.pos
  rw [Nat.card_congr (BorelQuotient.sylowNormalizerEquiv F hnpos hF S).toEquiv]
  exact three_not_dvd_card_borel_of_odd F hn hF
end Matrix.PSL3.LinearThree.BorelStructure
