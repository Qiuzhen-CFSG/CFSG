module
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The nontrivial degree-five permutation image of SL₂(5)

Quasisimplicity makes a proper kernel central. Perfectness forces the image
into A₅, and the orders 120 and 2 force that image to be all of A₅ and the
kernel to be exactly the center. This uses actual homomorphisms and supports
the cyclic-four centralizer calculation in Aschbacher–Smith J.4.8, p.443.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SL2.PermutationFiveImage
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {K : Type*} [Group K] [Finite K]
  (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

include e
omit [Finite K] in
theorem card_source : Nat.card K=120 := by
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,Nat.card_zmod]
  norm_num

omit [Finite K] in
theorem card_center : Nat.card (center K)=2 := by
  rw [Nat.card_congr (centerCongr e).toEquiv]
  exact (GorensteinWalter.sl2ProjectiveProjection_ker (ZMod 5)) ▸
    GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod 5) (by norm_num)

theorem kernel_and_range (f : K →* Equiv.Perm (Fin 5)) (hf : f≠1) :
    f.ker=center K ∧ f.range=alternatingGroup (Fin 5) := by
  let : IsQuasisimple K := ResidualTwoExtension.quasisimple_of_equiv (by norm_num) e
  have hk : f.ker ≤ center K :=
    (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
      (fun h => hf (MonoidHom.ker_eq_top_iff.mp h))
  have hs : Equiv.Perm.sign.comp f = 1 := by
    apply MonoidHom.ker_eq_top_iff.mp
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top (G:=K)]
    exact Abelianization.commutator_subset_ker _
  have hr : f.range ≤ alternatingGroup (Fin 5) := by
    rintro x ⟨k,rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun hs k)
  have hkc : Nat.card f.ker ≤ 2 := (card_le_of_le hk).trans_eq (card_center e)
  have hrc : Nat.card f.range ≤ 60 := by
    have h := card_le_of_le hr
    norm_num only [Nat.card_eq_fintype_card,card_alternatingGroup,Fintype.card_fin] at h
    exact h
  have hc := f.ker.index_mul_card
  rw [index_ker,card_source e] at hc
  have hk2 : Nat.card f.ker=2 := by nlinarith
  have hr60 : Nat.card f.range=60 := by rw [hk2] at hc; omega
  exact ⟨eq_of_le_of_card_ge hk (by rw [hk2,card_center e]),
    eq_of_le_of_card_ge hr (by rw [hr60,nat_card_alternatingGroup,Nat.card_fin]; norm_num)⟩

end Theory.SpecificGroups.SL2.PermutationFiveImage
