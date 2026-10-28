module

public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer
public import BenderSuzuki.Converse.Sz
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The Suzuki omega subgroup and its split-torus action

In the actual Suzuki matrix group, the root multiplication formula identifies
involutions with the root-group center. Thus the first omega subgroup is
central, elementary abelian, and has order q. The proved root-element
centralizer bound and the trivial root–torus intersection make the split torus
act freely; its order q − 1 makes this action regular. Coprime action gives
full displacement. Finally, the ovoid normalizer bound puts the omega
normalizer in the Borel, whose root factor centralizes omega. This gives
pointwise coverage by the torus under literal conjugation.

This is the intrinsic Suzuki calculation for the first and third paragraphs
of Aschbacher–Smith, Proposition 16.5.1, printed p.1194, combined manuscript
of 1 March 2004. Coordinate inputs are Huppert–Blackburn, Finite Groups III,
XI.3.1 and XI.3.3. The containing module aligns and embeds these subgroups
in the prescribed center-free component.
-/

public section

open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII
open scoped Pointwise LinearAlgebra.Projectivization IsMulCommutative
namespace CFSG.Quasithin.SuzukiSimpleModel

variable (m : ℕ) (hm : 0 < m)
include hm

private theorem rootClosure_center_iff_square (x : SuzukiRootClosure m) :
    x ∈ center (SuzukiRootClosure m) ↔ x ^ 2 = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := Converse.szPi m
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) :=
    Converse.szPi_apply m
  obtain ⟨_, _, _, _, _, _, _, _, hmul, hc, hz, _⟩ :=
    External.huppert_blackburn_XI_3_1 m hm pi
      (External.binaryGaloisField_tits_formula_sq m pi hpi)
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  change ∀ x : SuzukiRootClosure m, x ∈ commutator (SuzukiRootClosure m) ↔
    ∃ b : K, (x : GL (Fin 4) K) = SuzukiRootGL m 0 b at hz
  rw [hc] at hz
  have hsq (a b : K) : (SuzukiRootGL m a b) ^ 2 = SuzukiRootGL m 0 (a * pi a) := by
    rw [pow_two, hmul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (hz x).mp hx
    apply Subtype.ext
    change (x : GL (Fin 4) K) ^ 2 = 1
    rw [hb, hsq, zero_mul, External.suzukiRootGL_zero_zero]
  · intro hx
    obtain ⟨a, b, hab⟩ :=
      (External.suzukiRootGL_mem_closure_iff m pi
        (External.binaryGaloisField_tits_formula_sq m pi hpi) hpi x).mp x.property
    have hmat : (SuzukiRootGL m a b) ^ 2 = 1 := by
      rw [← hab]
      exact congrArg Subtype.val hx
    rw [hsq] at hmat
    have hab0 := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 2) hmat
    have ha0 : a * pi a = 0 := by
      simpa [SuzukiRootGL, SuzukiRootMatrix] using hab0
    have ha : a = 0 := (mul_eq_zero.mp ha0).elim id (fun hh => pi.injective (hh.trans pi.map_zero.symm))
    exact (hz x).mpr ⟨b, ha ▸ hab⟩

private theorem root_center_iff_square (x : SuzukiRootSubgroup m) :
    x ∈ center (SuzukiRootSubgroup m) ↔ x ^ 2 = 1 := by
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  constructor
  · intro hx
    apply e.injective
    rw [map_pow, map_one]
    exact (rootClosure_center_iff_square m hm (e x)).mp (centerCongr e ⟨x, hx⟩).property
  · intro hx
    have h := (rootClosure_center_iff_square m hm (e x)).mpr (by rw [← map_pow, hx, map_one])
    have hh := (centerCongr e.symm ⟨e x, h⟩).property
    change e.symm (e x) ∈ center (SuzukiRootSubgroup m) at hh
    simpa only [e.symm_apply_apply] using hh

theorem omega_eq_center : omegaOneAmbient (SuzukiRootSubgroup m) =
    (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    exact ⟨⟨x, hx⟩, (root_center_iff_square m hm _).mpr (Subtype.ext hx2), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl (x : SuzukiMatrixGroup m) x.property
      (congrArg Subtype.val ((root_center_iff_square m hm x).mp hx))

theorem omega_elementary : IsElementaryAbelian 2 (omegaOneAmbient (SuzukiRootSubgroup m)) := by
  have : IsElementaryAbelian 2 (center (SuzukiRootSubgroup m)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      exact Subtype.ext ((root_center_iff_square m hm x.val).mp x.property)
  }
  rw [omega_eq_center m hm]
  exact IsElementaryAbelian.map (SuzukiRootSubgroup m).subtype

theorem omega_card : Nat.card (omegaOneAmbient (SuzukiRootSubgroup m)) = 2 ^ (2 * m + 1) := by
  rw [omega_eq_center m hm, card_map_of_injective (SuzukiRootSubgroup m).subtype_injective,
    suzukiRootSubgroup_center_card m hm]

theorem omega_centralizes_root : omegaOneAmbient (SuzukiRootSubgroup m) ≤
    centralizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
  rw [omega_eq_center m hm]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

omit hm in
theorem torus_normalizes_omega : SuzukiSplitTorus m ≤
    normalizer (omegaOneAmbient (SuzukiRootSubgroup m) : Set (SuzukiMatrixGroup m)) := by
  intro x hx
  apply mem_normalizer_iff.mpr
  intro u
  have hn := suzukiSplitTorus_le_normalizer_root m hx
  have hnorm (y : SuzukiMatrixGroup m)
      (hy : y ∈ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m))) :
      (omegaOneAmbient (SuzukiRootSubgroup m)).map (MulAut.conj y).toMonoidHom ≤
        omegaOneAmbient (SuzukiRootSubgroup m) := by
    rw [map_le_iff_le_comap]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro a ha ha2
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl _
      ((mem_normalizer_iff.mp hy a).mp ha) (by rw [← map_pow, ha2, map_one])
  constructor
  · intro hu
    exact hnorm x hn ⟨u, hu, rfl⟩
  · intro hu
    have hh := hnorm x⁻¹ ((normalizer _).inv_mem hn) ⟨x*u*x⁻¹, hu, rfl⟩
    change x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ ∈ _ at hh
    simpa only [inv_inv, inv_mul_cancel_left, inv_mul_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh


private theorem conj_torus_injective {v : SuzukiMatrixGroup m}
    (hv : v ∈ omegaOneAmbient (SuzukiRootSubgroup m)) (hv1 : v ≠ 1) :
    Function.Injective (fun x : SuzukiSplitTorus m => MulAut.conj (x : SuzukiMatrixGroup m) v) := by
  intro x y h
  have hc : Commute ((y : SuzukiMatrixGroup m)⁻¹ * x) v := by
    have hh := congrArg (fun a : SuzukiMatrixGroup m => (y : SuzukiMatrixGroup m)⁻¹ * a * x) h
    change (y : SuzukiMatrixGroup m)⁻¹ * x * v = v * ((y : SuzukiMatrixGroup m)⁻¹ * x)
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh
  have hr := suzukiRootSubgroup_centralizer_le m hm (omegaOneAmbient_le _ hv) hv1
    (mem_centralizer_singleton_iff.mpr hc.eq)
  have hd := (SuzukiSplitTorus m).mul_mem ((SuzukiSplitTorus m).inv_mem y.property) x.property
  have he := (disjoint_def.mp (suzukiRootSubgroup_disjoint_splitTorus m hm)) hr hd
  exact Subtype.ext (inv_mul_eq_one.mp he).symm

theorem torus_regular {v w : SuzukiMatrixGroup m}
    (hv : v ∈ omegaOneAmbient (SuzukiRootSubgroup m)) (hv1 : v ≠ 1)
    (hw : w ∈ omegaOneAmbient (SuzukiRootSubgroup m)) (hw1 : w ≠ 1) :
    ∃! x : SuzukiSplitTorus m, MulAut.conj (x : SuzukiMatrixGroup m) v = w := by
  classical
  let U := omegaOneAmbient (SuzukiRootSubgroup m)
  let f : SuzukiSplitTorus m → {u : U // u ≠ 1} := fun x =>
    ⟨⟨MulAut.conj (x : SuzukiMatrixGroup m) v,
      (mem_normalizer_iff.mp (torus_normalizes_omega m x.property) v).mp hv⟩,
      fun h => hv1 ((MulAut.conj (x : SuzukiMatrixGroup m)).injective
        ((congrArg Subtype.val h).trans (map_one _).symm))⟩
  have hfi : Function.Injective f := fun _ _ h => conj_torus_injective m hm hv hv1
    (congrArg (fun u : {u : U // u ≠ 1} => (u.val : SuzukiMatrixGroup m)) h)
  have hfc : Nat.card (SuzukiSplitTorus m) = Nat.card {u : U // u ≠ 1} := by
    let : Fintype U := Fintype.ofFinite U
    have hc : Nat.card {u : U // u ≠ 1} = Nat.card U - 1 := by
      simp [Nat.card_eq_fintype_card]
    rw [hc, suzukiSplitTorus_card m hm, omega_card m hm]
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, hfc⟩).2
    ⟨⟨w, hw⟩, fun h => hw1 (congrArg Subtype.val h)⟩
  have hxw : MulAut.conj (x : SuzukiMatrixGroup m) v = w :=
    congrArg (fun u : {u : U // u ≠ 1} => (u.val : SuzukiMatrixGroup m)) hx
  exact ⟨x, hxw, fun y hy => conj_torus_injective m hm hv hv1 (hy.trans hxw.symm)⟩

theorem omega_fixed_eq_bot : omegaOneAmbient (SuzukiRootSubgroup m) ⊓
    centralizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) = ⊥ := by
  have hq : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have : Nontrivial (SuzukiSplitTorus m) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [suzukiSplitTorus_card m hm]; omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : SuzukiSplitTorus m)
  apply eq_bot_iff.mpr
  intro u hu
  apply mem_bot.mpr
  by_contra hu1
  apply hx
  apply conj_torus_injective m hm hu.1 hu1
  have hc := mem_centralizer_iff.mp hu.2 x x.property
  simp only [MulAut.conj_apply, Subgroup.coe_one, one_mul, inv_one, mul_one]
  rw [hc, mul_inv_cancel_right]

theorem omega_commutator :
    ⁅omegaOneAmbient (SuzukiRootSubgroup m), SuzukiSplitTorus m⁆ =
      omegaOneAmbient (SuzukiRootSubgroup m) := by
  let U := omegaOneAmbient (SuzukiRootSubgroup m)
  let := omega_elementary m hm
  have hsolv : Group.IsSolvable U := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hcop : Nat.Coprime (Nat.card (SuzukiSplitTorus m)) (Nat.card U) := by
    rw [suzukiSplitTorus_card m hm, omega_card m hm]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega)) odd_one
  have h := eq_commutator_sup_centralizer_of_solvable_coprime U (SuzukiSplitTorus m)
    (torus_normalizes_omega m) hsolv hcop
  rw [omega_fixed_eq_bot m hm, sup_bot_eq] at h
  exact h.symm

theorem normalizer_coverage {g : SuzukiMatrixGroup m}
    (hg : g ∈ normalizer (omegaOneAmbient (SuzukiRootSubgroup m) : Set (SuzukiMatrixGroup m))) :
    ∃ x : SuzukiSplitTorus m, ∀ u ∈ omegaOneAmbient (SuzukiRootSubgroup m),
      MulAut.conj (x : SuzukiMatrixGroup m) u = MulAut.conj g u := by
  have hU : omegaOneAmbient (SuzukiRootSubgroup m) ≠ ⊥ := by
    intro h
    have hc := omega_card m hm
    rw [h, card_bot] at hc
    have hh := Nat.one_lt_two_pow (show 2*m+1 ≠ 0 by omega)
    omega
  have hgB := suzuki_normalizer_le_borel_of_le_root m hm _ hU (omegaOneAmbient_le _) hg
  rw [suzukiBorelSubgroup_eq_sup] at hgB
  change g ∈ ((SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m : Subgroup _) : Set _) at hgB
  rw [coe_mul_of_right_le_normalizer_left _ _ (suzukiSplitTorus_le_normalizer_root m)] at hgB
  obtain ⟨r, hr, x, hx, rfl⟩ := hgB
  refine ⟨⟨x, hx⟩, ?_⟩
  intro u hu
  have hxu := (mem_normalizer_iff.mp (torus_normalizes_omega m hx) u).mp hu
  have hc := mem_centralizer_iff.mp (omega_centralizes_root m hm hxu) r hr
  change x * u * x⁻¹ = r * x * u * (r * x)⁻¹
  rw [mul_inv_rev]
  calc
    x * u * x⁻¹ = (x * u * x⁻¹) * r * r⁻¹ := by rw [mul_inv_cancel_right]
    _ = r * (x * u * x⁻¹) * r⁻¹ := by rw [hc]
    _ = _ := by group

end CFSG.Quasithin.SuzukiSimpleModel
