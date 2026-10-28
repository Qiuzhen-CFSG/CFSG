module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.Reduction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Centralizers under the contrary hypothesis of Lemma 15.3

Suppose every involution of the point two-core V lies in the original
root A. Cauchy's theorem and A∩D=1 imply V∩D=1. Since V centralizes A,
the pointwise root calculation gives V∩N(L)=A. Normalizer control then
identifies C_V(y)=A for every nonidentity y in J=C_G(L).

A nonidentity torus factor is free on A by Proposition 12.13's proved
centralizer consequence. The involution hypothesis lifts this freeness
to V, including products of that factor with elements of J. Thus every
nonidentity element of K Y, for Y≤J, has centralizer in V contained in A.
These are the actual inputs to the coprime fixed-point and size argument.

Source: GLS IV, Chapter 2, proof of Lemma 15.3, equation (15C),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "K" => residualCommutator M t
local notation "J" => centralizer (L : Set G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

public theorem Context.distinguished_disjoint_pair_source : Disjoint A D := by
  apply disjoint_def.mpr
  intro a ha hd
  by_contra hne
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  have hi : PFAppendixIII.IsInvolution a :=
    ⟨hne, elemPow_eq_one_of_isElementaryAbelian a ha⟩
  have hzA := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp hi
  exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
    d.t_not_mem_M hd hzA

public theorem Context.point_twoCore_disjoint_pair_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) : Disjoint V D := by
  apply disjoint_iff.mpr
  by_contra hne
  let Q := V ⊓ D
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hQ : IsPGroup 2 Q :=
    ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le inf_le_left
  obtain ⟨k, hk, hcard⟩ := hQ.nontrivial_iff_card.mp inferInstance
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  have hi : PFAppendixIII.IsInvolution (v : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp hv).symm Q.subtype Subtype.val_injective
  exact hi.ne_one (disjoint_def.mp d.distinguished_disjoint_pair_source
    (hinv v v.property.1 hi) v.property.2)

public theorem Context.point_twoCore_inf_normalizer_eq_distinguished_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) :
    V ⊓ normalizer (L : Set G) = A := by
  apply le_antisymm
  · intro v hv
    have hs : v ∈ A ⊔ J := d.normalizer_inf_centralizer_eq ▸
      (show v ∈ normalizer (L : Set G) ⊓ centralizer (A : Set G) from
        ⟨hv.2, (d.point_twoCore_le_distinguished_centralizer hv.1).2⟩)
    have hJA : J ≤ normalizer (A : Set G) :=
      (centralizer_le d.distinguished_le).trans (Subgroup.centralizer_le_normalizer _)
    have hp : v ∈ (A : Set G) * (J : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A J hJA]
      exact hs
    obtain ⟨a, ha, j, hj, rfl⟩ := hp
    have hjV : j ∈ V := by
      have hh := (V).mul_mem ((V).inv_mem (d.distinguished_le_point_twoCore ha)) hv.1
      simpa only [inv_mul_cancel_left] using hh
    have hjD := centralizer_residualGenerated_le_pair d.minimal.disconnected
      d.z_mem d.z_mem_M hj
    have hj1 := disjoint_def.mp (d.point_twoCore_disjoint_pair_of_involutions hinv) hjV hjD
    change a * j ∈ A
    rw [hj1, mul_one]
    exact ha
  · exact le_inf d.distinguished_le_point_twoCore (d.distinguished_le.trans (L).le_normalizer)

public theorem Context.point_twoCore_centralizer_eq_distinguished_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A)
    {y : G} (hy : y ∈ J) (hyne : y ≠ 1) :
    V ⊓ centralizer ({y} : Set G) = A := by
  apply le_antisymm
  · intro v hv
    have hvN : v ∈ normalizer (L : Set G) := by
      apply d.normalizer_control_of_le_centralizer (zpowers y) (zpowers_le.mpr hy)
        (by simpa using hyne)
      apply Subgroup.centralizer_le_normalizer
      rw [zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hv.2
    exact d.point_twoCore_inf_normalizer_eq_distinguished_of_involutions hinv ▸
      (show v ∈ V ⊓ normalizer (L : Set G) from ⟨hv.1, hvN⟩)
  · exact le_inf d.distinguished_le_point_twoCore (fun a ha =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy a (d.distinguished_le ha)))

omit d in
private theorem core_centralizer_eq_one_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A)
    {w : G} (hfree : ∀ a ∈ A, Commute w a → a = 1)
    {v : G} (hv : v ∈ V) (hc : Commute w v) : v = 1 := by
  by_contra hvne
  let Q := V ⊓ centralizer ({w} : Set G)
  have hvQ : v ∈ Q := ⟨hv, mem_centralizer_singleton_iff.mpr hc.symm⟩
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he] at hvQ
    exact hvne hvQ
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hQ : IsPGroup 2 Q :=
    ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le inf_le_left
  obtain ⟨k, hk, hcard⟩ := hQ.nontrivial_iff_card.mp inferInstance
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  have hi : PFAppendixIII.IsInvolution (a : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp ha).symm Q.subtype Subtype.val_injective
  exact hi.ne_one (hfree a (hinv a a.property.1 hi)
    (mem_centralizer_singleton_iff.mp a.property.2).symm)

public theorem Context.point_twoCore_torus_product_centralizer_eq_one
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A)
    {k y v : G} (hk : k ∈ K) (hkne : k ≠ 1) (hy : y ∈ J)
    (hv : v ∈ V) (hc : Commute (k * y) v) : v = 1 := by
  apply core_centralizer_eq_one_of_involutions hinv ?_ hv hc
  intro a ha hwa
  by_contra hane
  have hya : Commute y a := (mem_centralizer_iff.mp hy a (d.distinguished_le ha)).symm
  have hka : Commute k a := by
    have hh := hwa.eq
    rw [mul_assoc, hya.eq, ← mul_assoc, ← mul_assoc] at hh
    exact mul_right_cancel hh
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  have haZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp
      ⟨hane, elemPow_eq_one_of_isElementaryAbelian a ha⟩
  have haC : a ∈ centralizerClosure Z k := subset_closure
    ⟨haZ, mem_centralizer_singleton_iff.mpr hka.symm⟩
  rw [d.torus_centralizerClosure_eq_bot hk hkne] at haC
  exact hane haC

public theorem Context.point_twoCore_join_centralizer_le_distinguished
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A)
    (Y : Subgroup G) (hYJ : Y ≤ J) {w : G} (hw : w ∈ K ⊔ Y) (hwne : w ≠ 1) :
    V ⊓ centralizer ({w} : Set G) ≤ A := by
  have hKL : K ≤ L := by rw [d.torus_structure.1]; exact inf_le_right
  have hYK : Y ≤ normalizer (K : Set G) :=
    hYJ.trans ((centralizer_le hKL).trans (Subgroup.centralizer_le_normalizer _))
  have hp : w ∈ (K : Set G) * (Y : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K Y hYK]
    exact hw
  obtain ⟨k, hk, y, hy, rfl⟩ := hp
  intro v hv
  by_cases hk1 : k = 1
  · subst k
    simp only [one_mul] at hwne hv
    exact d.point_twoCore_centralizer_eq_distinguished_of_involutions hinv (hYJ hy) hwne ▸ hv
  · have hv1 := d.point_twoCore_torus_product_centralizer_eq_one hinv hk hk1 (hYJ hy)
      hv.1 (mem_centralizer_singleton_iff.mp hv.2).symm
    exact hv1 ▸ (A).one_mem

end BenderSuzuki.ZD.LinearExclusion
