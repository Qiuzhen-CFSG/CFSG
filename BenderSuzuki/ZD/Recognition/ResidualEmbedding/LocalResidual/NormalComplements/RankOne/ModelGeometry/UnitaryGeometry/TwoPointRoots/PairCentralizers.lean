module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.SpecialCommutators

/-!
# Odd centralizers of unitary involution pairs

The root Sylow group acts regularly away from its fixed isotropic point.
Thus the centralizer of each nonidentity root element preserves that point
and lies in its Borel. Centralizing an outside involution then places the
pair centralizer in the odd two-point torus. Sylow conjugacy treats every
projective Sylow subgroup. For SU₃, Cauchy's theorem and the odd scalar
kernel reduce pair-centralizer oddness to the actual projective image.

Source: GLS4, Chapter 4, Lemma 3.2(b)-(e),(i), used in Chapter 2,
16.2(b3) and 16.4-16.5.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped commutatorElement
namespace BenderSuzuki.ZD.RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups HermitianForm External
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
open scoped LinearAlgebra.Projectivization
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed hJ in
public theorem unitary_projective_root_centralizer (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hz1 : z ≠ 1) :
    centralizer ({z} : Set _) ≤ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨rho, alpha, S, _, _, _, hN, hreg, _⟩ :=
    psu_sylow_normalizer_action J n hn hcard hfixed hJ
  let _ : MulAction (ProjectiveSpecialUnitaryMatrixGroup J)
      {x : ℙ E (Fin 3 → E) // x ∈ {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}} :=
    MulAction.compHom _ rho
  change normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
    MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) alpha at hN
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P S
  let c := MulAut.conj g
  have hm : (P : Subgroup _).map c.toMonoidHom = (S : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hzS : c z ∈ (S : Subgroup _) := hm ▸ mem_map_of_mem c.toMonoidHom hz
  have hzfix : c z • alpha = alpha := by
    have hh : c z ∈ normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).le_normalizer hzS
    rw [hN] at hh
    exact hh
  intro x hx
  have hc : c x * c z = c z * c x := by
    simpa only [map_mul] using congrArg c (mem_centralizer_singleton_iff.mp hx)
  have hfix : c x • alpha = alpha := by
    by_contra hnfix
    have hzbeta : c z • (c x • alpha) = c x • alpha := by
      rw [← mul_smul, ← hc, mul_smul, hzfix]
    obtain ⟨r, _, hu⟩ := hreg (c x • alpha) (c x • alpha) hnfix hnfix
    have he : (⟨c z, hzS⟩ : S) = 1 :=
      (hu ⟨c z, hzS⟩ hzbeta).trans (hu 1 (by simp)).symm
    apply hz1
    apply c.injective
    simpa using congrArg Subtype.val he
  have hxN : c x ∈ normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := hN.symm ▸ hfix
  have hNm : (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map c.toMonoidHom =
      normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    calc
      _ = normalizer (((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map c.toMonoidHom :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := map_equiv_normalizer_eq _ c
      _ = _ := by rw [hm]; rfl
  rw [← hNm] at hxN
  obtain ⟨y, hy, he⟩ := hxN
  exact c.injective he ▸ hy

include hn hcard hfixed hJ in
public theorem unitary_projective_pair_centralizer_odd (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z t : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hz1 : z ≠ 1)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    Odd (Nat.card (centralizer ({z,t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) := by
  let B := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  let D := twoPoint B t
  have hle : centralizer ({z,t} : Set _) ≤ D := by
    intro x hx
    have hxz : x ∈ centralizer ({z} : Set _) :=
      (centralizer_le (by intro y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy])) hx
    have hxt : x * t = t * x :=
      ((mem_centralizer_iff.mp hx) t (by simp)).symm
    have hxB := unitary_projective_root_centralizer J hn hcard hfixed hJ P z hz hz1 hxz
    refine ⟨hxB, x, hxB, ?_⟩
    change t⁻¹ * x * (t⁻¹)⁻¹ = x
    rw [inv_inv, mul_assoc, hxt, inv_mul_cancel_left]
  have hd := (unitary_projective_twoPoint_torus J hn hcard hfixed hJ P t ht htB).2
  have hodd : Odd (Nat.card D) := by
    rw [hd]
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
    have hdvd : Nat.gcd 3 (2 ^ n + 1) ∣ (2 ^ n) ^ 2 - 1 := by
      rw [hfac]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 _) _
    apply Odd.of_dvd_nat _ (Nat.div_dvd_of_dvd hdvd)
    apply Nat.Even.sub_odd (Nat.one_le_pow 2 (2 ^ n) (Nat.one_le_pow n 2 (by decide))) _ odd_one
    have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact he.pow_of_ne_zero (by decide : 2 ≠ 0)
  exact hodd.of_dvd_nat (card_dvd_of_le hle)

include hn hcard hfixed hJ in
public theorem unitary_special_pair_centralizer_odd (P : Sylow 2 J.specialSubgroup)
    (z t : J.specialSubgroup) (hz : z ∈ P) (hzi : IsInvolution z)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    Odd (Nat.card (centralizer ({z,t} : Set J.specialSubgroup))) := by
  let f := J.specialToProjective
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hzn : f z ≠ 1 :=
    (Theory.GroupTheory.involution_map_of_odd_kernel f J.odd_card_specialToProjective_ker hzi).1
  have htn := Theory.GroupTheory.involution_map_of_odd_kernel f J.odd_card_specialToProjective_ker ht
  have htout : f t ∉ normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro hh
    apply htB
    have hm : (normalizer (P : Set J.specialSubgroup)).map f =
        normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      P.normalizer_map_surjective f J.specialToProjective_surjective
    rw [← hm] at hh
    have hk := J.specialToProjective_ker_le_center.trans
      (center_le_normalizer (P : Set J.specialSubgroup))
    have hpre : ((normalizer (P : Set J.specialSubgroup)).map f).comap f =
        normalizer (P : Set J.specialSubgroup) := by rw [comap_map_eq, sup_eq_left.mpr hk]
    rw [← hpre]
    exact hh
  have ho := unitary_projective_pair_centralizer_odd J hn hcard hfixed hJ Q (f z) (f t)
    (mem_map_of_mem f hz) hzn htn htout
  apply Nat.not_even_iff_odd.mp
  intro hev
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({z,t} : Set J.specialSubgroup)) 2 (even_iff_two_dvd.mp hev)
  have hxi : IsInvolution (x : J.specialSubgroup) := by
    have hh := orderOf_eq_prime_iff.mp ((Subgroup.orderOf_coe x).trans hxo)
    exact ⟨hh.2, hh.1⟩
  have hfI := Theory.GroupTheory.involution_map_of_odd_kernel f J.odd_card_specialToProjective_ker hxi
  have hfc : f x ∈ centralizer ({f z, f t} : Set _) := by
    rw [mem_centralizer_iff]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · simpa only [map_mul] using congrArg f ((mem_centralizer_iff.mp x.property) z (by simp))
    · have he : y = f t := Set.mem_singleton_iff.mp hy
      subst y
      simpa only [map_mul] using congrArg f ((mem_centralizer_iff.mp x.property) t (by simp))
  have hd : 2 ∣ Nat.card (centralizer ({f z, f t} : Set _)) := by
    rw [← show orderOf (f x) = 2 from (orderOf_eq_prime_iff).2 ⟨hfI.2, hfI.1⟩]
    exact Subgroup.orderOf_dvd_natCard _ hfc
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)


end BenderSuzuki.ZD.RankOneModelGeometry
