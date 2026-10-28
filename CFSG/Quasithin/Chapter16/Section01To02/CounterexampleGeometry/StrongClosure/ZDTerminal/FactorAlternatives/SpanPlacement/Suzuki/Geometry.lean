module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Suzuki
public import Theory.SpecificGroups.Suzuki.AbelianRootGeometry

/-!
# The elementary smaller factor in a Suzuki Sylow subgroup

Suzuki factor rigidity gives nesting. The larger factor is then strongly
closed. Each element of the smaller factor commutes with its conjugate by a
nonidentity split-torus element. The root-coordinate commutation formula
forces its first coordinate to vanish, hence its square to be one.
Sylow conjugacy transports this calculation to the prescribed Sylow subgroup.

This exponent bound supplies the lifting step for the Suzuki branch of
Aschbacher (1975), Lemma 3.4, printed pp.94–96. The coordinate calculation is
Huppert–Blackburn III, XI.3.1, through `AbelianRootGeometry`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

private theorem suzuki_root_central_sq {m : ℕ} (hm : 1 ≤ m)
    (C : Subgroup (SuzukiMatrixGroup m)) (hC : C ≤ SuzukiRootSubgroup m)
    (hc : IsStronglyClosedSet (C : Set (SuzukiMatrixGroup m)) (SuzukiRootSubgroup m) ⊤)
    {x : SuzukiMatrixGroup m} (hx : x ∈ C)
    (hcomm : ∀ y ∈ C, Commute x y) : x ^ 2 = 1 := by
  have hcard : 1 < Nat.card (BinaryGaloisField (2*m+1))ˣ := by
    rw [Nat.card_units, GaloisField.card 2 (2*m+1) (by omega)]
    have hq : 4 ≤ 2 ^ (2*m+1) :=
      (show 4 = 2^2 by norm_num).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  let : Nontrivial (BinaryGaloisField (2*m+1))ˣ :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨t, ht⟩ := exists_ne (1 : (BinaryGaloisField (2*m+1))ˣ)
  let g : SuzukiMatrixGroup m :=
    ⟨SuzukiTorusGL m t, subset_closure (Or.inr (Or.inl ⟨t, rfl⟩))⟩
  have hg : g ∈ SuzukiSplitTorus m := subset_closure ⟨t, rfl⟩
  have hyR : g * x * g⁻¹ ∈ SuzukiRootSubgroup m :=
    (mem_normalizer_iff.mp (suzukiSplitTorus_le_normalizer_root m hg) x).mp (hC hx)
  have hyC : g * x * g⁻¹ ∈ C := by
    simpa only [inv_inv, SetLike.mem_coe] using hc.2 x hx g⁻¹ (mem_top _)
      (by simpa only [inv_inv] using hyR)
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m x).mp (hC hx)
  have hmat := (hcomm _ hyC).map (SuzukiMatrixGroup m).subtype
  change Commute x.val (SuzukiTorusGL m t * x.val * (SuzukiTorusGL m t)⁻¹) at hmat
  rw [hab] at hmat
  have ha := suzukiRootGL_first_eq_zero_of_commute_conjugate m a b t ht hmat
  apply Subtype.ext
  change x.val ^ 2 = 1
  rw [hab, ha, pow_two]
  obtain ⟨_, _, _, _, _, _, _, _, hmul, _⟩ :=
    BenderSuzuki.External.huppert_blackburn_XI_3_1 m hm (suzukiTits m) (suzukiTits_sq m)
  rw [hmul]
  simp only [zero_mul, CharTwo.add_self_eq_zero,
    BenderSuzuki.External.suzukiRootGL_zero_zero]

private theorem suzuki_nested_factor_sq {m : ℕ} (hm : 1 ≤ m)
    (P : Sylow 2 (SuzukiMatrixGroup m)) (B C : Subgroup (SuzukiMatrixGroup m))
    (hC : C ≤ P) (hBC : ⁅B, C⁆ = ⊥)
    (hc : IsStronglyClosedSet ((B : Set (SuzukiMatrixGroup m)) ∪ C) (P : Subgroup (SuzukiMatrixGroup m)) ⊤)
    (hle : B ≤ C) : ∀ x ∈ B, x ^ 2 = 1 := by
  obtain ⟨Q, hQ⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P Q
  let e := MulAut.conj g
  have hP : (P : Subgroup (SuzukiMatrixGroup m)).map e.toMonoidHom = SuzukiRootSubgroup m := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hQ] at hh
    exact hh
  have hcC : IsStronglyClosedSet (C : Set (SuzukiMatrixGroup m)) (P : Subgroup (SuzukiMatrixGroup m)) ⊤ := by
    rwa [Set.union_eq_right.mpr hle] at hc
  have hc' : IsStronglyClosedSet (C.map e.toMonoidHom : Set (SuzukiMatrixGroup m))
      (SuzukiRootSubgroup m) ⊤ := by
    rw [← hP]
    exact InternalRigidity.stronglyClosed_image P (C : Set (SuzukiMatrixGroup m)) hcC e.toMonoidHom e.surjective
  intro x hx
  have hsq : e x ^ 2 = 1 := by
    apply suzuki_root_central_sq hm (C.map e.toMonoidHom) (hP ▸ map_mono hC)
      hc' (mem_map_of_mem e.toMonoidHom (hle hx))
    rintro y ⟨z, hz, rfl⟩
    have hcomm : Commute x z := (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hBC hx) z hz).symm
    exact hcomm.map e
  apply e.injective
  simpa only [map_pow, map_one] using hsq

/-- The smaller of the two commuting Suzuki factors has exponent at most two. -/
theorem suzuki_factors_nested_elementary (m : ℕ) (hm : 1 ≤ m)
    (P : Sylow 2 (SuzukiMatrixGroup m)) (B C : Subgroup (SuzukiMatrixGroup m))
    (hB : B ≤ P) (hC : C ≤ P) (hBC : ⁅B, C⁆ = ⊥)
    (hBr : TwoRankAtLeastTwo B) (hCr : TwoRankAtLeastTwo C)
    (hc : IsStronglyClosedSet ((B : Set (SuzukiMatrixGroup m)) ∪ C) (P : Subgroup (SuzukiMatrixGroup m)) ⊤) :
    (B ≤ C ∧ ∀ x ∈ B, x ^ 2 = 1) ∨ (C ≤ B ∧ ∀ x ∈ C, x ^ 2 = 1) := by
  rcases InternalRigidity.suzuki_rigidity m hm P B C hB hC hBC hBr hCr hc with hh | hh
  · exact Or.inl ⟨hh, suzuki_nested_factor_sq hm P B C hC hBC hc hh⟩
  · exact Or.inr ⟨hh, suzuki_nested_factor_sq hm P C B hB
      (by rwa [commutator_comm]) (by rwa [Set.union_comm]) hh⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
