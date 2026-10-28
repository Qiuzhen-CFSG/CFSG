module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Eight
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.OddDisplacement
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import Theory.Representation.BinaryNormalExtension
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Ambient M12 heart bounds for source 7.4.1

A faithful normal heart identifies the actual solvable residual with M12.
On every such ambient marking, m = 4 and odd prime actors move at least six
dimensions. An elementary near-offender would have rank three or four.
The rank-three inner case contains a native elementary eight, and the
rank-four case meets the residual in one; both move at least six dimensions.
An outer involution excludes the remaining rank-three case.

NonFFSourceMathieuM12 applies these bounds to the original chosen orbit in
E.6.27. No centralizer-table or local displacement premise is retained.
Source: Aschbacher--Smith H.11.1, Table 7.2.1 and7.4.1, pp.392,698--700.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations Sporadic.Mathieu
/-- A normal perfect heart action determines the full solvable residual, including outer actors. -/
theorem input_of_normal_heart {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hρ : Function.Injective ρ)
    (K : Subgroup A) [K.Normal] [Group.IsPerfect K]
    (e : K ≃* M12) (E : W ≃ₗ[ZMod 2] M12Heart)
    (hE : ∀ k : K, ∀ v, E (ρ k v) = m12HeartRepresentation (e k) (E v)) :
    Nonempty (M12ModuleInput ρ) := by
  let a : A →* MulAut M12 :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have he (g : A) (v : W) : E (ρ g v) = Ambient.automorphismRepresentation (a g) (E v) :=
    BinaryNormalExtension.equivariant ρ K m12HeartRepresentation Ambient.automorphismRepresentation
      Ambient.automorphismRepresentation_inner (fun f hf => Ambient.heart_centralizer f hf)
      e E hE g v
  have hi : Function.Injective a := by
    intro g k hgk
    apply hρ
    ext v
    apply E.injective
    rw [he,he,hgk]
  have hm : K.map a = MulAut.innerSubgroup M12 := by
    ext g
    constructor
    · rintro ⟨k,hk,rfl⟩
      refine ⟨e ⟨k,hk⟩,?_⟩
      change MulAut.conj (e ⟨k,hk⟩) = MulAut.congr e (MulAut.conjNormal k)
      rw [show MulAut.conjNormal k = MulAut.conj (⟨k,hk⟩ : K) from (MulAut.conjNormal_val (h := (⟨k,hk⟩ : K))),
        MulAut.congr_conj]
    · rintro ⟨k,rfl⟩
      refine ⟨e.symm k,(e.symm k).property,?_⟩
      change MulAut.congr e (MulAut.conjNormal (e.symm k : A)) = MulAut.conj k
      rw [MulAut.conjNormal_val,MulAut.congr_conj,e.apply_symm_apply]
  have hp : (MulAut.innerSubgroup M12).comap a = K := by
    rw [←hm,comap_map_eq_self_of_injective hi]
  have hr : solvableResidual A = K := by
    apply le_antisymm _ (le_solvableResidual_of_isPerfect K)
    rw [←hp,←map_le_iff_le_comap]
    let : Group.IsPerfect ((solvableResidual A).map a) := Group.IsPerfect.map a
    exact le_of_isPerfect_of_index_le_two _ _ M12A5Fixer.Automorphisms.outerIndexBound
  let r : solvableResidual A ≃* M12 := (MulEquiv.subgroupCongr hr).trans e
  refine ⟨⟨hρ,r,Representation.Equiv.mk E ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  change E (ρ g v) = m12HeartRepresentation (e ((MulEquiv.subgroupCongr hr) g)) (E v)
  exact hE ((MulEquiv.subgroupCongr hr) g) v

/-- The full marked ambient heart has the exact involution minimum four. -/
theorem moduleM_eq_four {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (h : M12ModuleInput ρ) :
    ChapterE.moduleM ρ = 4 :=
  LocalActors.moduleM_eq_four ρ h (ambientExtension ρ h) outer_involution_fusion

/-- Odd prime actors of every ambient heart move at least six dimensions. -/
theorem odd_fixedCodim_ge_six {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (h : M12ModuleInput ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : A) (ha : orderOf a = p) :
    6 ≤ fixedCodim ρ (zpowers a) := by
  have hp2 : p ≠ 2 := by obtain ⟨k,hk⟩ := ho; omega
  have har := (ambientExtension ρ h).mem_residual_of_odd_prime_order a
    (ha ▸ hp) (ha ▸ hp2)
  rw [fixedCodim_residual_element ρ h ⟨a,har⟩]
  apply six_le_fixedCodim_odd_prime
  · simpa only [MulEquiv.orderOf_eq, ←Subgroup.orderOf_coe,ha] using hp
  · simpa only [MulEquiv.orderOf_eq, ←Subgroup.orderOf_coe,ha] using hp2

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations Sporadic.Mathieu
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W) (h : M12ModuleInput ρ)
include h
open ChapterE

omit [Finite G] in
private theorem residual_eight_displacement (A : Subgroup G)
    [IsElementaryAbelian 2 A]
    (hc : Nat.card (A.subgroupOf (solvableResidual G)) = 8) :
    6 ≤ fixedCodim ρ A := by
  let E := A.subgroupOf (solvableResidual G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective
    (solvableResidual G).subtype (solvableResidual G).subtype_injective A
  let B := E.map h.residualEquiv.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBcard : Nat.card B = 8 := (card_map_of_injective h.residualEquiv.injective).trans hc
  have hB : IsElementaryTwo B := ⟨fun hb => by simp [hb] at hBcard,inferInstance⟩
  have hrank : rank B = 3 := by rw [rank,hBcard]; rfl
  have hd := MathieuM12Eight.eight_fixedCodim B hB hrank
  rw [←fixedCodim_residual_subgroup ρ h E] at hd
  exact hd.trans (fixedCodim_mono ρ (by rw [subgroupOf_map_subtype]; exact inf_le_left))

/-- No elementary actor is an (F-1)-offender on a marked ambient M12 heart. -/
theorem fixedCodim_gap (A : Subgroup G) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim ρ A := by
  let := hA.2
  let d := ambientExtension ρ h
  have hr := d.elementary_rank_le_four M12AutomorphismRank.twoRank_le_four A hA.2
  have hm := (moduleM_eq_four ρ h).symm.trans_le (ChapterE.moduleM_le_fixedCodim ρ hA)
  by_contra hgap
  have hcod : fixedCodim ρ A ≤ rank A + 1 := by omega
  have h3 : 3 ≤ rank A := by omega
  by_cases h4 : rank A = 4
  · have hcard : Nat.card A = 16 := by rw [hA.card_eq_two_pow_rank,h4]; rfl
    have hi : (solvableResidual G).index ≤ 2 := by
      have he := (solvableResidual G).index_map_equiv
        (d.automorphismEquivOfElementarySixteen m12_twoRank_le_three A hA.2 hcard)
      change ((solvableResidual G).map d.embedding).index = (solvableResidual G).index at he
      rw [d.map_residual] at he
      rw [←he]
      exact M12A5Fixer.Automorphisms.outerIndexBound
    let R := solvableResidual G
    let E := A.subgroupOf R
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective
      R.subtype R.subtype_injective A
    have he : primeRank 2 R ≤ 3 := by
      rw [primeRank_equiv 2 h.residualEquiv]
      exact m12_twoRank_le_three
    have hu := (primeRank_le_iff_elementary_card_le R).mp he E inferInstance
    have hidx : (R.subgroupOf A).index ≤ 2 :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero R.index_ne_zero_of_finite)
        (R.relIndex_dvd_index_of_normal A)).trans hi
    let swap : R.subgroupOf A ≃ E :=
      { toFun := fun x => ⟨⟨x.1.1,x.2⟩,x.1.2⟩
        invFun := fun x => ⟨⟨x.1.1,x.2⟩,x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := (R.subgroupOf A).card_mul_index
    rw [hcard,Nat.card_congr swap] at hc
    have hecard : Nat.card E = 8 := by norm_num at hu; nlinarith
    have hd := residual_eight_displacement ρ h A hecard
    omega
  · have hr3 : rank A = 3 := by omega
    by_cases hi : A ≤ solvableResidual G
    · have hc : Nat.card (A.subgroupOf (solvableResidual G)) = 8 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hi).toEquiv,hA.card_eq_two_pow_rank,hr3]
        rfl
      have hd := residual_eight_displacement ρ h A hc
      omega
    · obtain ⟨t,ht,hto⟩ := SetLike.not_le_iff_exists.mp hi
      have ht1 : t ≠ 1 := fun he => hto (he ▸ (solvableResidual G).one_mem)
      have ht2 : orderOf t = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
      have hd := LocalActors.fixedCodim_outer_involution ρ h d outer_involution_fusion hto ht2
      have hb := fixedCodim_mono ρ (zpowers_le.mpr ht)
      omega
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12
