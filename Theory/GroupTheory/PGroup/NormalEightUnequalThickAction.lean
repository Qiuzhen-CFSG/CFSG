module

public import Theory.GroupTheory.PGroup.NormalEightInvolutionLift
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.UnequalThickKernelLifting
public import Theory.GroupTheory.PGroup.UnequalThickFourthRootBound

/-!
# Elementary action bound for thick unequal cyclic factors

Let `D` be normal, abelian and self-centralizing in a finite two-group with
central omega of order four and no normal elementary eight. A normal subgroup
whose cosets modulo `D` have involution representatives fixing fourth roots
is contained in `D`: a nontrivial normal image in `P / D` meets the center,
and the central-coset involution lifting theorem gives a contradiction.

Apply this to first omega of the kernel of conjugation on fourth roots.
If its cosets have involution representatives in that kernel, restriction to
fourth roots detects every elementary conjugation image. This replaces an
assumption that the entire ambient conjugation image is abelian by an explicit
coset-lifting hypothesis. For unequal cyclic factors both of order at least
four, `UnequalThickKernelLifting` supplies that hypothesis and
`UnequalThickFourthRootBound` bounds the restricted image by four. Combining
them gives the same bound for the full elementary conjugation image.

Source: the cyclic lifting arguments of MacWilliams, *On 2-groups with no
normal abelian subgroups of rank 3*, Trans. AMS 150 (1970), §1.2,
DOI 10.1090/S0002-9947-1970-0276324-3, together with the normal-subgroup
central-intersection property of finite p-groups.
-/

open Subgroup

namespace IsPGroup

/-- A normal subgroup with fourth-root-fixing involution representatives modulo
an abelian self-centralizing subgroup is contained in that subgroup. -/
public theorem normal_le_of_involution_cosets_fixing_fourth_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (N : Subgroup P) [N.Normal]
    (hlift : ∀ x ∈ N, ∃ a : P, a ^ 2 = 1 ∧
      x * a⁻¹ ∈ D ∧ ∀ d : D, d ^ 4 = 1 → Commute a (d : P)) : N ≤ D := by
  classical
  by_contra hND
  let q := QuotientGroup.mk' D
  let B := N.map q
  let : B.Normal := inferInstance
  have hBne : B ≠ ⊥ := by
    intro h
    apply hND
    simpa [q] using (map_eq_bot_iff (f := q) N).mp h
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hBne
  let : Fact (IsPGroup 2 (P ⧸ D)) := ⟨hP.to_quotient D⟩
  obtain ⟨b, hbne, hbcenter⟩ := exists_nontrivial_center_mem_normal B (p := 2)
  obtain ⟨x, hx, hxb⟩ := b.property
  obtain ⟨a, ha, hxa, hfix⟩ := hlift x hx
  have hqa : q a = q x := by
    have he : q (x * a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hxa
    exact (mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm
  have hac : a ∈ center P := by
    apply hP.mem_center_of_square_eq_one_of_central_mod_abelian_of_fourth_roots
      hno hZ D a ha _ hfix
    intro g
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * a * g⁻¹ * a⁻¹) = 1
    simp only [map_mul, map_inv, hqa, hxb]
    rw [mem_center_iff.mp hbcenter (q g), mul_inv_cancel_right, mul_inv_cancel]
  have haD := hD (center_le_centralizer _ hac)
  apply hbne
  apply Subtype.ext
  exact hxb.symm.trans (hqa.symm.trans ((QuotientGroup.eq_one_iff _).mpr haD))

/-- Coset lifting in first omega of the fourth-root action kernel detects
all elementary action images. No abelian ambient-action hypothesis is used. -/
public theorem card_conj_image_le_fourth_root_image_of_kernel_involution_cosets
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hlift : ∀ x ∈ (omega₁ (omegaTwoConjugation D).ker (p := 2)).map
        (omegaTwoConjugation D).ker.subtype,
      ∃ a ∈ (omegaTwoConjugation D).ker, a ^ 2 = 1 ∧ x * a⁻¹ ∈ D)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤
      Nat.card ((omegaTwoConjugation D).comp A.subtype).range := by
  let K := (omegaTwoConjugation D).ker
  let O := omega₁ K (p := 2)
  let : O.Characteristic := omega₁_characteristic K
  let N := O.map K.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hND : N ≤ D := by
    apply normal_le_of_involution_cosets_fixing_fourth_roots hP hno hZ D hD N
    intro x hx
    obtain ⟨a, haK, ha, hxa⟩ := hlift x hx
    refine ⟨a, ha, hxa, ?_⟩
    intro d hd
    have hdO : d ∈ omega D (p := 2) 2 := subset_closure (by simpa using hd)
    have he := congrArg (fun t : MulAut (omega D (p := 2) 2) =>
      ((t ⟨d, hdO⟩ : D) : P)) (MonoidHom.mem_ker.mp haK)
    change a * (d : P) * a⁻¹ = (d : P) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  let f := (MulAut.conjNormal : P →* MulAut D).comp A.subtype
  let r := (omegaTwoConjugation D).comp A.subtype
  have hker : r.ker ≤ f.ker := by
    intro a ha
    have haK : (a : P) ∈ K := ha
    have haN : (a : P) ∈ N := by
      refine ⟨⟨a, haK⟩, subset_closure ?_, rfl⟩
      change (⟨(a : P), haK⟩ : K) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    apply MonoidHom.mem_ker.mpr
    ext d
    change (a : P) * (d : P) * (a : P)⁻¹ = (d : P)
    rw [(D.le_centralizer (hND haN) d d.property).symm, mul_inv_cancel_right]
  simpa only [index_ker] using Subgroup.index_antitone hker

/-- An elementary subgroup acts with image of order at most four on a normal
abelian self-centralizing subgroup with unequal cyclic factors, both of order
at least four, under the no-normal-eight and central-omega-four hypotheses. -/
public theorem card_conj_image_le_four_of_unequal_thick_factors
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n m : ℕ) (hm : 2 ≤ m) (hmn : m < n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  exact (card_conj_image_le_fourth_root_image_of_kernel_involution_cosets
    hP hno hZ D hD
    (kernel_involution_cosets_of_unequal_thick_factors hP hno hZ D hD n m hm hmn e)
    A).trans
      (card_omegaTwo_image_le_four_of_unequal_thick_factors hP hno hZ D hD n m hm hmn e A)

end IsPGroup
