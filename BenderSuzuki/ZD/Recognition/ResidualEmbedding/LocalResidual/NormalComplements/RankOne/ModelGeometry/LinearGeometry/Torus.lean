module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Coordinates
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The marked split torus and generation in binary PSL₂

The simultaneous Sylow/Borel/Weyl coordinates identify the literal intersection
`B ∩ t⁻¹Bt` with the diagonal torus. Its unit parameters prove cyclicity and
order; the Weyl matrix inverts it. Odd order then gives `[D,⟨t⟩] = D`.
The square map on the finite binary field is bijective, so the torus conjugates
any nonidentity root element to all the others. This proves the source's
three-generator equality for the actual chosen involutions.

Source: GLS IV, Chapter 4, Lemma 3.2(c–e,h), used in Chapter 2, Section 16.
The standard torus calculation is extracted from `LocalStructure/LinearBorel.lean`.
-/

public section

open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped Pointwise commutatorElement
namespace BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
variable {G : Type*} [Group G] [Finite G] {n : ℕ}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem torus_eq_pair : Torus F = Borel F ⊓ rightConjugate (Borel F) (weyl F) := by
  rw [Borel, rightConjugate_stabilizer, weyl_inv, weyl_smul_pInf]
  rfl

noncomputable def torusEquivUnits : Torus F ≃* Fˣ :=
  (MulEquiv.subgroupCongr (Torus_eq_range (F := F))).trans
    (MonoidHom.ofInjective (torHom_injective (F := F))).symm

omit [CharP F 2] in
theorem torus_cyclic : IsCyclic (Torus F) :=
  isCyclic_of_injective ((torusEquivUnits (F := F)).toMonoidHom) (torusEquivUnits (F := F)).injective

omit [Finite F] [CharP F 2] in
theorem torus_card : Nat.card (Torus F) = Nat.card F - 1 := by
  rw [Nat.card_congr torusEquivUnits.toEquiv, Nat.card_units]

omit [Finite F] in
theorem torus_inverted {d : SL2 F} (hd : d ∈ Torus F) :
    rightConjugateElem d (weyl F) = d⁻¹ := by
  rw [Torus_eq_range] at hd
  obtain ⟨a, rfl⟩ := hd
  rw [rightConjugateElem, weyl_inv, ← map_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, torHom]

omit [Finite G] in
theorem mem_rightConjugate (B : Subgroup G) (t x : G) :
    x ∈ rightConjugate B t ↔ t * x * t⁻¹ ∈ B := by
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  simp [MulAut.conj_apply]

omit [Finite G] [Finite F] in
/-- The literal two-point subgroup becomes the actual diagonal torus. -/
theorem twoPoint_coordinates (B : Subgroup G) (t : G) (f : G ≃* SL2 F)
    (hB : B.map f.toMonoidHom = Borel F) (ht : f t = weyl F) :
    (twoPoint B t).map f.toMonoidHom = Torus F := by
  have hmem (x : G) : f x ∈ Borel F ↔ x ∈ B := by
    rw [← hB, mem_map_equiv, f.symm_apply_apply]
  ext x
  rw [mem_map_equiv, twoPoint, mem_inf, mem_rightConjugate,
    ← hmem, ← hmem, f.apply_symm_apply, map_mul, map_mul, map_inv, ht,
    f.apply_symm_apply, torus_eq_pair, mem_inf, mem_rightConjugate]

noncomputable def twoPointEquivTorus (B : Subgroup G) (t : G) (f : G ≃* SL2 F)
    (hB : B.map f.toMonoidHom = Borel F) (ht : f t = weyl F) :
    twoPoint B t ≃* Torus F :=
  (f.subgroupMap _).trans (MulEquiv.subgroupCongr (twoPoint_coordinates B t f hB ht))

/-- The two-point subgroup is cyclic of the source order. -/
theorem twoPoint_cyclic_card (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) {t : G} (ht : IsInvolution t)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    IsCyclic (twoPoint (normalizer ((P : Subgroup G) : Set G)) t) ∧
      Nat.card (twoPoint (normalizer ((P : Subgroup G) : Set G)) t) = 2 ^ n - 1 := by
  obtain ⟨f, _, hfB, hft⟩ := exists_marked_coordinates e P ht htB
  let d := twoPointEquivTorus _ t f hfB hft
  let := torus_cyclic (F := BinaryGaloisField n)
  refine ⟨isCyclic_of_injective d.toMonoidHom d.injective, ?_⟩
  rw [Nat.card_congr d.toEquiv, torus_card, card_binaryGaloisField n (by omega)]

/-- The chosen involution inverts the literal two-point subgroup. -/
theorem twoPoint_inverted (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) {t : G} (ht : IsInvolution t)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G))
    {x : G} (hx : x ∈ twoPoint (normalizer ((P : Subgroup G) : Set G)) t) :
    rightConjugateElem x t = x⁻¹ := by
  obtain ⟨f, _, hfB, hft⟩ := exists_marked_coordinates e P ht htB
  have hfx : f x ∈ Torus (BinaryGaloisField n) := by
    rw [← twoPoint_coordinates _ t f hfB hft]
    exact Subgroup.mem_map_of_mem _ hx
  apply f.injective
  change f (t⁻¹ * x * t) = f (x⁻¹)
  rw [map_mul, map_mul, map_inv, map_inv, hft]
  exact torus_inverted hfx

/-- Inversion and odd order give the full subgroup commutator, with Mathlib's convention. -/
theorem commutator_eq_of_inverted (D : Subgroup G) (hodd : Odd (Nat.card D))
    (t : G) (ht : IsInvolution t)
    (hinv : ∀ x ∈ D, rightConjugateElem x t = x⁻¹) : ⁅D, zpowers t⁆ = D := by
  classical
  have he (x : G) (hx : x ∈ D) : ⁅x,t⁆ = x ^ 2 := by
    have hi : t * x * t⁻¹ = x⁻¹ := by simpa [rightConjugateElem, ht.inv_eq_self] using hinv x hx
    calc
      ⁅x,t⁆ = x * (t * x * t⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
      _ = x ^ 2 := by rw [hi, inv_inv, pow_two]
  apply le_antisymm
  · rw [commutator_le]
    intro x hx s hs
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime ht.sq_eq_one ht.ne_one] at hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
    have hklt := Finset.mem_range.mp hk
    interval_cases k
    · simp
    · simp only [pow_one, he x hx]
      exact D.pow_mem hx 2
  · intro x hx
    have hsq : x ^ 2 ∈ ⁅D, zpowers t⁆ := by
      rw [← he x hx]
      exact commutator_mem_commutator hx (mem_zpowers t)
    have hxo : Odd (orderOf x) := hodd.of_dvd_nat (D.orderOf_dvd_natCard hx)
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one x) hxo 1
    rw [pow_one, pow_mul] at hk
    rw [hk]
    exact pow_mem hsq k

/-- The torus is exactly its commutator with the chosen involution. -/
theorem twoPoint_commutator (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) {t : G} (ht : IsInvolution t)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    ⁅twoPoint (normalizer ((P : Subgroup G) : Set G)) t, zpowers t⁆ =
      twoPoint (normalizer ((P : Subgroup G) : Set G)) t := by
  apply commutator_eq_of_inverted _ ?_ t ht (fun _ hx => twoPoint_inverted e P ht htB hx)
  rw [(twoPoint_cyclic_card hn e P ht htB).2]
  have he : Even (2 ^ n) := (Nat.even_pow' hn.ne').mpr (by decide : Even 2)
  exact Nat.Even.sub_odd Nat.one_le_two_pow he odd_one


/-- The diagonal torus conjugates any nonidentity upper root element to every other one. -/
theorem unip_le_of_torus (H : Subgroup (SL2 F)) {z : SL2 F}
    (hz : IsInvolution z) (hzU : z ∈ Unip F) (hzH : z ∈ H) (hT : Torus F ≤ H) :
    Unip F ≤ H := by
  obtain ⟨a, rfl⟩ := (mem_Unip_iff _).mp hzU
  have ha : a ≠ 0 := fun he => hz.ne_one (by rw [he, uni_zero])
  intro x hx
  obtain ⟨b, rfl⟩ := (mem_Unip_iff _).mp hx
  by_cases hb : b = 0
  · simpa only [hb, uni_zero] using H.one_mem
  obtain ⟨c, hc⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := F))) (b / a)
  change c ^ 2 = b / a at hc
  have hc0 : c ≠ 0 := by
    intro hzero
    have : b / a = 0 := by rw [← hc, hzero]; simp
    exact (div_ne_zero hb ha) this
  let d := tor (Units.mk0 c hc0)
  have hd : d ∈ Torus F := by rw [Torus_eq_range]; exact ⟨_, rfl⟩
  have hconj : d * uni a * d⁻¹ = uni b := by
    rw [Borel_conj_uni (Torus_le_Borel hd)]
    change uni (c ^ 2 * a) = uni b
    rw [hc, div_mul_cancel₀ _ ha]
  rw [← hconj]
  exact H.mul_mem (H.mul_mem (hT hd) hzH) (H.inv_mem (hT hd))

/-- The source's three generators give the same root-generated subgroup. -/
theorem marked_generation (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) {z t : G} (hz : IsInvolution z) (hzP : z ∈ P)
    (ht : IsInvolution t) (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    zpowers z ⊔ zpowers t ⊔
      ⁅twoPoint (normalizer ((P : Subgroup G) : Set G)) t, zpowers t⁆ =
        rootGenerated (P : Subgroup G) t := by
  rw [twoPoint_commutator hn e P ht htB, rootGenerated_eq_top e P htB]
  obtain ⟨f, hfU, hfB, hft⟩ := exists_marked_coordinates e P ht htB
  let D := twoPoint (normalizer ((P : Subgroup G) : Set G)) t
  let H := zpowers z ⊔ zpowers t ⊔ D
  have hzH : z ∈ H := (show zpowers z ≤ H from le_sup_left.trans le_sup_left) (mem_zpowers z)
  have hD : D ≤ H := le_sup_right
  have hU : Unip (BinaryGaloisField n) ≤ H.map f.toMonoidHom := by
    apply unip_le_of_torus _
      (BenderSuzuki.IsInvolution.map_of_injective hz f.toMonoidHom f.injective)
    · rw [← hfU]; exact Subgroup.mem_map_of_mem _ hzP
    · exact Subgroup.mem_map_of_mem _ hzH
    · rw [← twoPoint_coordinates _ t f hfB hft]
      exact Subgroup.map_mono hD
  have hPH : (P : Subgroup G) ≤ H := by
    intro x hx
    have hh := hU (show f x ∈ Unip (BinaryGaloisField n) from by
      rw [← hfU]; exact Subgroup.mem_map_of_mem _ hx)
    have hh' := mem_map_equiv.mp hh
    simpa only [f.symm_apply_apply] using hh'
  apply top_unique
  rw [← rootGenerated_eq_top e P htB, rootGenerated, sylow_omega_eq e P]
  exact sup_le hPH (show zpowers t ≤ H from le_sup_right.trans le_sup_left)

end BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
