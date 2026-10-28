module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.SectionBound
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupTheory.PCoreRestriction


/-!
# The quotient action and inversion in the nonquasisimple branch

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).

On a section chosen irreducible for the larger actor J, O₂(X) is killed
whenever J normalizes X. An inversion error belonging to O₂(H) and X
therefore disappears in this same action. A nontrivial odd image then
forces the image of the inverting elementary two-element to have order two.
These deductions do not assert the existence of the source inverting element
or of a faithful affine extension in the image.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G W : Type*} [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [Nontrivial W]

/-- A component-invariant irreducible section kills the two-core of every
normal subgroup X of the acting group, including X=Ξ_p(K_U). -/
theorem core_killed (J X : Subgroup G) (ρ : J →* MulAut W)
    (hJX : J ≤ normalizer (X : Set G))
    (hirr : ∀ D : Subgroup W,
      (∀ j : J, ∀ w, w ∈ D → ρ j w ∈ D) → D = ⊥ ∨ D = ⊤) :
    (X.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
  have hJQ : J ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hJX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  let _ : ((X.pCoreIn 2).subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJQ
  have hQ : (X.pCoreIn 2).subgroupOf J ≤ pCore 2 J :=
    le_sSup ⟨inferInstance, (isPGroup_pCoreIn 2 X).comap_subtype⟩
  apply hQ.trans (irreducible_range_core_le_ker ρ ?_)
  intro D hD
  exact hirr D (fun j w hw => hD ⟨ρ j, ⟨j, rfl⟩⟩ w hw)

omit [Finite G] [Finite W] [IsElementaryAbelian 2 W] [Nontrivial W] in
/-- Inversion modulo O₂(H) becomes exact inversion on the SAME larger action.
The error is in X∩O₂(H)≤O₂(X); no normalization of Y by the lift is required. -/
theorem image_inversion (X H J Y : Subgroup G) (ρ : J →* MulAut W)
    (hXH : X ≤ H) (hJX : J ≤ normalizer (X : Set G))
    (hYX : Y ≤ X) (hQker : (X.pCoreIn 2).subgroupOf J ≤ ρ.ker)
    (v : J) (hinv : ∀ y ∈ Y, (v : G) * y * (v : G)⁻¹ * y ∈ H.pCoreIn 2) :
    ∀ a ∈ (Y.subgroupOf J).map ρ, ρ v * a * (ρ v)⁻¹ = a⁻¹ := by
  rintro a ⟨y, hy, rfl⟩
  have heX : (v : G) * (y : G) * (v : G)⁻¹ * (y : G) ∈ X :=
    X.mul_mem ((mem_normalizer_iff.mp (hJX v.property) y).mp (hYX hy)) (hYX hy)
  have heQ := inf_pCoreIn_le_of_le 2 hXH ⟨heX, hinv y hy⟩
  have heker : v * y * v⁻¹ * y ∈ ρ.ker := hQker heQ
  have he := MonoidHom.mem_ker.mp heker
  rw [map_mul, map_mul, map_mul, map_inv] at he
  exact eq_inv_iff_mul_eq_one.mpr he

omit [Finite G] [Finite W] [IsElementaryAbelian 2 W] [Nontrivial W] in
/-- An involutory lift that inverts a nontrivial odd action has nontrivial
involutory image. Thus SectionBound needs no separate order assertion. -/
theorem inverting_image_isInvolution (J Y : Subgroup G) (ρ : J →* MulAut W)
    (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker) (v : J) (hsq : v ^ 2 = 1)
    (hinv : ∀ a ∈ (Y.subgroupOf J).map ρ, ρ v * a * (ρ v)⁻¹ = a⁻¹) :
    IsInvolution (ρ v) := by
  constructor
  · intro hv
    apply hactive
    intro y hy
    have hi := hinv (ρ y) (mem_map_of_mem ρ hy)
    rw [hv, one_mul, inv_one, mul_one] at hi
    let A := (Y.subgroupOf J).map ρ
    have hAodd : Odd (Nat.card A) := by
      apply Odd.of_dvd_nat ?_ (card_map_dvd (Y.subgroupOf J) ρ)
      rwa [Nat.card_congr (subgroupOfEquivOfLe hYJ).toEquiv]
    let a : A := ⟨ρ y, mem_map_of_mem ρ hy⟩
    have ha2 : a ^ 2 = 1 := by
      apply Subtype.ext
      change (ρ y) ^ 2 = 1
      rw [pow_two]
      exact (congrArg (fun z => z * ρ y) hi).trans (inv_mul_cancel _)
    have hao : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hAodd.coprime_two_left
      (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_natCard a)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp hao)
  · rw [← map_pow, hsq, map_one]

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
