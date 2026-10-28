module

public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.InnerReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Orbit
public import Theory.SpecificGroups.AlternatingFiveTriangle
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The involution centralizer in the actual J₁ matrix group

The centralizer of the standard involution is isomorphic to C₂ × A₅.
Two explicit words in the certified ATLAS matrices satisfy the (2,3,5)
relations and centralize the involution, giving an injective A₅ homomorphism.
The central involution supplies a commuting C₂ factor; triviality of the
center of A₅ makes the factors disjoint.

For exhaustion, the checked large-prime centralizer certificates and Sylow
conjugacy exclude 7, 11 and 19 from the centralizer order. The certified model
order therefore bounds it by 120, exactly the size of the embedded product.
No distinctness or exact size of the involution-orbit data is assumed.

Source: GLS3, Table 5.3f, the entry `2A : 2 × A₅`, used in
Aschbacher–Smith E.1.14(5), printed p.214. The ATLAS matrix provenance is in
`Model.Basic`. The two candidate words were found by finite search in these
matrices; all required identities are proved here by kernel-checked matrix
arithmetic.
-/

open Subgroup
namespace Janko1.InvolutionCentralizer
open OrderCertificate

private def triangleX : Model := inner4
private def triangleY : Model := ((hz ^ 8 * inner7 : H) : Model) * outer114
private def triangleYMatrix : Mat :=
  !![10, 7, 8, 9, 0, 0, 2;
      3, 0, 3, 1, 4, 4, 7;
      1, 4, 6, 8, 0, 10, 9;
      2, 8, 10, 5, 8, 5, 4;
      10, 7, 7, 9, 9, 9, 0;
      8, 10, 5, 9, 9, 3, 2;
      3, 8, 2, 8, 10, 10, 1]

private theorem image_triangleX : matrixValue triangleX = innerMatrix4 := image_inner4
private theorem image_triangleY : matrixValue triangleY = triangleYMatrix := by
  have coe_image (h : H) : matrixValue (h : Model) = hMatrixValue h := rfl
  rw [triangleY, map_mul, coe_image, map_mul, image_power8, image_inner7, image_outer114]
  decide +kernel

private theorem triangleX_mem : triangleX ∈ subgroup := by
  rw [mem_centralizer_singleton_iff]
  apply matrixValue_injective
  simp only [map_mul, image_triangleX, image_a]
  decide +kernel

private theorem triangleY_mem : triangleY ∈ subgroup := by
  rw [mem_centralizer_singleton_iff]
  apply matrixValue_injective
  simp only [map_mul, image_triangleY, image_a]
  decide +kernel

private theorem triangleX_ne : triangleX ≠ 1 := by
  intro h
  have hm := congrArg matrixValue h
  rw [image_triangleX, map_one] at hm
  exact (by decide +kernel : innerMatrix4 ≠ 1) hm

private theorem triangleX_square : triangleX ^ 2 = 1 := by
  apply matrixValue_injective
  simp only [map_pow, image_triangleX, map_one]
  decide +kernel

private theorem triangleY_cube : triangleY ^ 3 = 1 := by
  apply matrixValue_injective
  simp only [map_pow, image_triangleY, map_one]
  decide +kernel

private theorem triangleXY_fifth : (triangleX * triangleY) ^ 5 = 1 := by
  apply matrixValue_injective
  simp only [map_pow, map_mul, image_triangleX, image_triangleY, map_one]
  decide +kernel

/-- The centralizer contains an actual embedded alternating group on five letters. -/
public theorem exists_injective_alternatingFive :
    ∃ f : alternatingGroup (Fin 5) →* subgroup, Function.Injective f := by
  exact alternatingGroup.exists_injective_hom_of_triangle
    (⟨triangleX, triangleX_mem⟩ : subgroup) (⟨triangleY, triangleY_mem⟩ : subgroup)
    (fun h => triangleX_ne (congrArg Subtype.val h))
    (Subtype.ext triangleX_square) (Subtype.ext triangleY_cube) (Subtype.ext triangleXY_fifth)

private theorem prime_not_dvd_card {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card Model) (r : Model) (hr : orderOf r = p)
    (hno : ∀ t : Model, orderOf t = 2 → ¬ Commute t r) :
    ¬ p ∣ Nat.card subgroup := by
  let : Fact p.Prime := ⟨hp⟩
  intro hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := subgroup) p hd
  have hu' : orderOf (u : Model) = p := by
    simpa only [Subgroup.orderOf_coe] using hu
  obtain ⟨k, g, hg⟩ :=
    PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd hp hsq hu' hr
  have hau : Commute a (u : Model) :=
    (mem_centralizer_singleton_iff.mp u.property).symm
  have ht : orderOf (MulAut.conj g a) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_a]
  apply hno _ ht
  rw [hg]
  exact (hau.pow_right k).map (MulAut.conj g)

private theorem card_le_120 : Nat.card subgroup ≤ 120 := by
  have h7 : ¬ 7 ∣ Nat.card subgroup := prime_not_dvd_card (by decide)
    (by norm_num [card_model]) (a * b) orderOf_ab
    LocalStructure.LargePrimes.no_involution_commutes_seven
  have h11 : ¬ 11 ∣ Nat.card subgroup := prime_not_dvd_card (by decide)
    (by norm_num [card_model]) (OrderCertificate.x * OrderCertificate.y ^ 2)
    OrderCertificate.orderOf_eleven
    LocalStructure.LargePrimes.no_involution_commutes_eleven
  have h19 : ¬ 19 ∣ Nat.card subgroup := prime_not_dvd_card (by decide)
    (by norm_num [card_model]) (a * b * a * b ^ 2) orderOf_abab_sq
    LocalStructure.LargePrimes.no_involution_commutes_nineteen
  have hc7 : Nat.Coprime (Nat.card subgroup) 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7).symm
  have hc11 : Nat.Coprime (Nat.card subgroup) 11 :=
    ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr h11).symm
  have hc19 : Nat.Coprime (Nat.card subgroup) 19 :=
    ((by decide : Nat.Prime 19).coprime_iff_not_dvd.mpr h19).symm
  have hc : Nat.Coprime (Nat.card subgroup) (7 * 11 * 19) :=
    (hc7.mul_right hc11).mul_right hc19
  apply Nat.le_of_dvd (by decide : 0 < 120)
  apply hc.dvd_mul_right.mp
  simpa only [card_model, show 120 * (7 * 11 * 19) = 175560 from rfl] using
    subgroup.card_subgroup_dvd_card

private def centralInvolution : subgroup :=
  ⟨a, mem_centralizer_singleton_iff.mpr rfl⟩

private theorem centralInvolution_mem_center : centralInvolution ∈ center subgroup := by
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)

private theorem centralInvolution_order : orderOf centralInvolution = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_a

private noncomputable def twoEquiv :
    Multiplicative (ZMod 2) ≃* zpowers centralInvolution :=
  mulEquivOfPrimeCardEq (by exact Nat.card_zmod 2)
    ((Nat.card_zpowers centralInvolution).trans centralInvolution_order)

private def cyclicInclusion : zpowers centralInvolution →* subgroup :=
  (zpowers centralInvolution).subtype

private theorem cyclic_commutes (f : alternatingGroup (Fin 5) →* subgroup)
    (z : zpowers centralInvolution) (g : alternatingGroup (Fin 5)) :
    Commute (cyclicInclusion z) (f g) := by
  have hz : (z : subgroup) ∈ center subgroup :=
    zpowers_le.mpr centralInvolution_mem_center z.property
  exact (mem_center_iff.mp hz (f g)).symm

private theorem cyclic_disjoint (f : alternatingGroup (Fin 5) →* subgroup)
    (hf : Function.Injective f) : Disjoint cyclicInclusion.range f.range := by
  apply Subgroup.disjoint_def.mpr
  intro t ht hf'
  obtain ⟨z, rfl⟩ := ht
  obtain ⟨g, hg⟩ := hf'
  have hgcent : g ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro u
    apply hf
    simp only [map_mul, hg]
    exact (cyclic_commutes f z u).symm.eq
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hgcent
  rw [hgcent, map_one] at hg
  exact hg.symm

private noncomputable def equivalenceOfEmbedding
    (f : alternatingGroup (Fin 5) →* subgroup) (hf : Function.Injective f) :
    subgroup ≃* ProductModel := by
  let h := cyclicInclusion.noncommCoprod f (cyclic_commutes f)
  have hi : Function.Injective h :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨Subtype.val_injective, hf, cyclic_disjoint f hf⟩
  have hc : Nat.card (zpowers centralInvolution × alternatingGroup (Fin 5)) = 120 := by
    rw [Nat.card_prod, Nat.card_zpowers, centralInvolution_order, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (MulEquiv.ofBijective h (hi.bijective_of_nat_card_le (hc ▸ card_le_120))).symm.trans
    (twoEquiv.symm.prodCongr (MulEquiv.refl _))

/-- The full product identification of the literal standard-involution centralizer. -/
public noncomputable def productEquiv : subgroup ≃* ProductModel :=
  equivalenceOfEmbedding (Classical.choose exists_injective_alternatingFive)
    (Classical.choose_spec exists_injective_alternatingFive)

/-- The actual centralizer realizes the C₂ × A₅ entry of GLS3 Table 5.3f. -/
public theorem nonempty_productEquiv : Nonempty (subgroup ≃* ProductModel) :=
  ⟨productEquiv⟩

end Janko1.InvolutionCentralizer
