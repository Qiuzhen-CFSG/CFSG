module
public import ABG.ChapterII.Section1.WreathedCentralizers
public import ABG.ChapterII.Section1.WreathedCenter

/-!
# Centralizers of elements outside the wreathed base

For an element `g` outside the base `U` of the chosen wreathed presentation,
its centralizer is `center S ⊔ zpowers g`. It is either cyclic or isomorphic
to `C_(2^n) × C_2`. This explicit description supplies the abelian branch
of ABG Chapter II §1 Lemma 3, article p.10, using the coordinates and center
structure from Lemma 2.

A centralizing base element is central. A centralizing outer element differs
from `g` by a central base element, giving the centralizer description. Write
`g² = u^k`. If `k` is odd, `g²` generates the cyclic center, so `g` generates
the centralizer. If `k` is even, multiplying `g` by a suitable central power
produces an outer involution with the same centralizer. Its cyclic subgroup
is disjoint from the center; multiplying the two factors gives a bijective
homomorphism onto the centralizer and hence the required product model.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem center_le_U : Subgroup.center S ≤ P.U := by
  rw [P.center_eq_zpowers, Subgroup.zpowers_le]
  exact (P.mem_U_iff _).mpr ⟨1,1,by simp [u]⟩

public theorem mem_outer_centralizer_iff {g a : S} (hg : g ∉ P.U) :
    a ∈ Subgroup.centralizer ({g} : Set S) ↔
      a ∈ Subgroup.center S ∨ a * g⁻¹ ∈ Subgroup.center S := by
  constructor
  · intro ha
    have hga : Commute g a := (Subgroup.mem_centralizer_singleton_iff.mp ha).symm
    by_cases hau : a ∈ P.U
    · exact Or.inl (P.base_commute_outer_mem_center hau hg hga.symm)
    · exact Or.inr (P.base_commute_outer_mem_center (P.outer_mul_inv_mem_base hau hg) hg
        (hga.symm.mul_left (Commute.refl g).inv_left))
  · rintro (ha | ha)
    · exact Subgroup.center_le_centralizer _ ha
    · have hac : Commute g (a * g⁻¹) := (Subgroup.mem_center_iff.mp ha) g
      have h := hac.mul_right (Commute.refl g)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using h.symm.eq)

public theorem outer_centralizer_eq {g : S} (hg : g ∉ P.U) :
    Subgroup.centralizer ({g} : Set S) = Subgroup.center S ⊔ Subgroup.zpowers g := by
  apply le_antisymm
  · intro a ha
    rcases (P.mem_outer_centralizer_iff hg).mp ha with h | h
    · exact (show Subgroup.center S ≤ _ from le_sup_left) h
    · have h₁ := (show Subgroup.center S ≤ Subgroup.center S ⊔ Subgroup.zpowers g from le_sup_left) h
      have h₂ : g ∈ Subgroup.center S ⊔ Subgroup.zpowers g :=
        (show Subgroup.zpowers g ≤ _ from le_sup_right) (Subgroup.mem_zpowers _)
      simpa using (Subgroup.center S ⊔ Subgroup.zpowers g).mul_mem h₁ h₂
  · exact sup_le (Subgroup.center_le_centralizer _)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl g)))

private theorem involution_zpowers_cases {h a : S} (hsq : h ^ 2 = 1)
    (ha : a ∈ Subgroup.zpowers h) : a = 1 ∨ a = h := by
  rcases Subgroup.mem_zpowers_iff.mp ha with ⟨k,rfl⟩
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · left
    rw [zpow_eq_zpow_emod' k hsq]
    norm_num [hk]
  · right
    rw [zpow_eq_zpow_emod' k hsq]
    norm_num [hk]

private theorem involution_center_disjoint {h : S} (hh : h ∉ P.U) (hsq : h ^ 2 = 1) :
    Disjoint (Subgroup.center S) (Subgroup.zpowers h) := by
  rw [Subgroup.disjoint_def]
  intro a ha hb
  rcases involution_zpowers_cases hsq hb with he | he
  · exact he
  · exact False.elim (hh (P.center_le_U (he ▸ ha)))

private def centerProductMap (h : S) :
    (Subgroup.center S × Subgroup.zpowers h) →*
      Subgroup.centralizer ({h} : Set S) where
  toFun v := ⟨v.1 * v.2, (Subgroup.centralizer ({h} : Set S)).mul_mem
    (Subgroup.center_le_centralizer _ v.1.property)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.refl h)) v.2.property)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' v w := by
    apply Subtype.ext
    change (v.1 * w.1 : S) * (v.2 * w.2) = (v.1 * v.2) * (w.1 * w.2)
    have hc : (v.2 : S) * w.1 = w.1 * v.2 :=
      (Subgroup.mem_center_iff.mp w.1.property) v.2
    calc
      _ = (v.1 : S) * ((w.1 : S) * v.2) * w.2 := by group
      _ = _ := by rw [← hc]; group

private theorem centerProductMap_bijective {h : S} (hh : h ∉ P.U) (hsq : h ^ 2 = 1) :
    Function.Bijective (centerProductMap h) := by
  constructor
  · intro v w hvw
    exact Subgroup.mul_injective_of_disjoint (P.involution_center_disjoint hh hsq)
      (congrArg Subtype.val hvw)
  · intro a
    rcases (P.mem_outer_centralizer_iff hh).mp a.property with ha | ha
    · exact ⟨(⟨a,ha⟩,1), Subtype.ext (by simp [centerProductMap])⟩
    · exact ⟨(⟨(a:S)*h⁻¹,ha⟩,⟨h,Subgroup.mem_zpowers h⟩),
        Subtype.ext (by simp [centerProductMap])⟩

private theorem involution_centralizer_model {h : S} (hh : h ∉ P.U) (hsq : h ^ 2 = 1) :
    Nonempty (Subgroup.centralizer ({h} : Set S) ≃*
      (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) := by
  let := P.center_cyclic
  have hh1 : h ≠ 1 := by intro he; exact hh (he ▸ P.U.one_mem)
  have ho : orderOf h = 2 := orderOf_eq_prime hsq hh1
  let e := MulEquiv.ofBijective (centerProductMap h) (P.centerProductMap_bijective hh hsq)
  let e₁ : Subgroup.center S ≃* Multiplicative (ZMod (2 ^ n)) :=
    mulEquivOfCyclicCardEq (by simpa using P.card_center)
  let e₂ : Subgroup.zpowers h ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by simp [Nat.card_zpowers, ho])
  exact ⟨e.symm.trans (e₁.prodCongr e₂)⟩

private theorem centralizer_mul_central (c g : S) (hc : c ∈ Subgroup.center S) :
    Subgroup.centralizer ({c * g} : Set S) = Subgroup.centralizer ({g} : Set S) := by
  ext a
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have hca := (Subgroup.mem_center_iff.mp hc) a
  constructor
  · intro ha
    apply mul_left_cancel (a := c)
    calc
      _ = a * (c * g) := by rw [← mul_assoc, ← hca, mul_assoc]
      _ = _ := by rw [ha]; group
  · intro ha
    calc
      a * (c * g) = c * (a * g) := by rw [← mul_assoc, hca, mul_assoc]
      _ = _ := by rw [ha]; group

public theorem outer_centralizer_models {g : S} (hg : g ∉ P.U) :
    IsCyclic (Subgroup.centralizer ({g} : Set S)) ∨
      Nonempty (Subgroup.centralizer ({g} : Set S) ≃*
        (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) := by
  rcases P.exists_outer_normal_form hg with ⟨i,j,hgform⟩
  have hsq : g ^ 2 = P.u ^ (i + j) := by rw [← hgform, P.outer_normal_form_square]
  rcases Nat.even_or_odd (i+j) with heven | hodd
  · right
    obtain ⟨k,hk⟩ := heven
    let h := (P.u ^ k)⁻¹ * g
    have hcenter : (P.u ^ k)⁻¹ ∈ Subgroup.center S :=
      (Subgroup.center S).inv_mem ((Subgroup.center S).pow_mem P.u_mem_center k)
    have hh : h ∉ P.U := by
      intro hh
      apply hg
      have hu : P.u ^ k ∈ P.U := P.center_le_U ((Subgroup.center S).pow_mem P.u_mem_center k)
      simpa [h] using P.U.mul_mem hu hh
    have hhsq : h ^ 2 = 1 := by
      have hc : Commute (P.u ^ k)⁻¹ g := ((P.u_commute g).pow_left k).inv_left
      dsimp only [h]
      rw [hc.mul_pow, inv_pow, hsq, hk, pow_add, pow_two]
      simp
    have he : Subgroup.centralizer ({h} : Set S) = Subgroup.centralizer ({g} : Set S) :=
      centralizer_mul_central _ _ hcenter
    rcases P.involution_centralizer_model hh hhsq with ⟨e⟩
    exact ⟨(MulEquiv.subgroupCongr he.symm).trans e⟩
  · left
    have hu : P.u ∈ Subgroup.zpowers g := by
      have hpow : P.u ∈ Subgroup.zpowers (P.u ^ (i+j)) := by
        apply mem_zpowers_pow_iff.mpr
        rw [P.orderOf_u]
        exact hodd.coprime_two_right.pow_right n
      rw [← hsq] at hpow
      exact (Subgroup.zpowers_le.mpr ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) 2)) hpow
    have hz : Subgroup.center S ≤ Subgroup.zpowers g := by
      rw [P.center_eq_zpowers]
      exact Subgroup.zpowers_le.mpr hu
    rw [P.outer_centralizer_eq hg, sup_eq_right.mpr hz]
    infer_instance
end ABG.Wreathed.Presentation
