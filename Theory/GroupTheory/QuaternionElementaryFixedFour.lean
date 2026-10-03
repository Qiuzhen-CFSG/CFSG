module

public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Theory.GroupTheory.QuaternionOuterInvolutionReduction
public import Theory.GroupTheory.QuaternionBothOuterInvolutionFixed
public import Theory.GroupTheory.QuaternionCentralProductInnerOuterFixed
public import Theory.GroupTheory.QuaternionMixedInvolutionFixed
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.QuaternionCentralProductFactors

/-!
# Elementary fixed fours in quaternion core extensions

An outside involution of a self-centralizing normal quaternion central product
with elementary fixed subgroup of order at most four preserves both quaternion
factors and acts outerly on both. Swapping the factors gives a fixed eight;
a mixed inner/outer action gives a nonabelian fixed subgroup. The remaining
case has a fixed four and trivial involution cocycles, so the core acts
transitively on the involutions in the outside coset.

Source: Janko–Thompson, Math. Z. 113 (1970), §4 case (b)(ii), printed p.391.
-/

namespace Subgroup

private theorem elem_of_equiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (h : IsElementaryAbelian 2 A) : IsElementaryAbelian 2 D := by
  let _ := h
  refine { toIsMulCommutative := ⟨⟨fun x y => e.symm.injective ?_⟩⟩, exponent_dvd_p := ?_ }
  · simpa only [map_mul] using (IsMulCommutative.is_comm (M := A)).comm (e.symm x) (e.symm y)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) _

private theorem elementary_fixed_action
    {T H : Type*} [Group T] [Finite T] [Group H] [Finite H]
    (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (hself : centralizer (P : Set T) ≤ P)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : T) (ht : orderOf t = 2) (hout : t ∉ P)
    (hfixed : IsElementaryAbelian 2 (P.subgroupOf (centralizer ({t} : Set T))))
    (hfixed_card : Nat.card (P.subgroupOf (centralizer ({t} : Set T))) ≤ 4) :
    IsElementaryAbelian 2 ((normalConjThrough P e t).toMonoidHom.eqLocus (MonoidHom.id H)) ∧
      Nat.card ((normalConjThrough P e t).toMonoidHom.eqLocus (MonoidHom.id H)) = 4 ∧
      (∀ x : H, x * normalConjThrough P e t x = 1 →
        ∃ p : H, x = p * normalConjThrough P e t p⁻¹) := by
  let a := normalConjThrough P e t
  let E := P.subgroupOf (centralizer ({t} : Set T))
  let F := a.toMonoidHom.eqLocus (MonoidHom.id H)
  have hEq : E.map (centralizer ({t} : Set T)).subtype =
      (P ⊓ centralizer ({t} : Set T) : Subgroup T) := subgroupOf_map_subtype P _
  let g : E ≃* (P ⊓ centralizer ({t} : Set T) : Subgroup T) :=
    (E.equivMapOfInjective (centralizer ({t} : Set T)).subtype
      (centralizer ({t} : Set T)).subtype_injective).trans
      (MulEquiv.subgroupCongr hEq)
  let f : F ≃* (P ⊓ centralizer ({t} : Set T) : Subgroup T) :=
    (F.equivMapOfInjective (P.subtype.comp e.symm.toMonoidHom)
      (P.subtype_injective.comp e.symm.injective)).trans
      (MulEquiv.subgroupCongr (normalConjThrough_fixed_map P e t))
  have hF : IsElementaryAbelian 2 F :=
    elem_of_equiv f.symm (elem_of_equiv g hfixed)
  have hEc : Nat.card E = Nat.card (P ⊓ centralizer ({t} : Set T) : Subgroup T) := by
    rw [← hEq, card_map_of_injective (centralizer ({t} : Set T)).subtype_injective]
  have hFc : Nat.card F ≤ 4 := by
    calc
      Nat.card F = Nat.card (P ⊓ centralizer ({t} : Set T) : Subgroup T) := Nat.card_congr f.toEquiv
      _ = Nat.card E := hEc.symm
      _ ≤ 4 := hfixed_card
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have ha2 : a ^ 2 = 1 := by
    change (normalConjThrough P e t) ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have haouter : ¬ ∃ q : H, a = MulAut.conj q :=
    normalConjThrough_not_inner P e hself t hout
  have himage (D : Subgroup H) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hDle : D ≤ B ⊔ C) : D.map a.toMonoidHom = B ∨ D.map a.toMonoidHom = C := by
    obtain ⟨model⟩ := hD
    apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
    · exact ⟨(a.subgroupMap D).symm.trans model⟩
    · exact (map_mono hDle).trans_eq (by rw [hjoin]; exact map_top_of_surjective _ a.surjective)
  have hBB : B.map a.toMonoidHom = B := by
    rcases himage B hB le_sup_left with hBB | hBC
    · exact hBB
    let θ : B ≃* C := (a.subgroupMap B).trans (MulEquiv.subgroupCongr hBC)
    have hdiag := quaternion_diagonal_eq_fixed_of_involution_swap B C θ hinter hcomm hjoin a ha2
      (fun _ => rfl)
    obtain ⟨model⟩ := hB
    have hdc : Nat.card F = 8 := by
      change Nat.card ((a.toMonoidHom.eqLocus (MonoidHom.id H)) : Subgroup H) = 8
      rw [hdiag]
      exact (quaternion_diagonal_elementary_eight B C model θ hinter hcomm).2.1
    omega
  have hCC : C.map a.toMonoidHom = C := by
    rcases himage C hC le_sup_right with hCB | hCC
    · have hne : B ≠ C := by
        intro hh
        obtain ⟨model⟩ := hB
        have hcard : Nat.card B = 8 := by
          rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
        rw [← hh, inf_idem, hcard] at hinter
        omega
      exact (hne (map_injective a.injective (hBB.trans hCB.symm))).elim
    · exact hCC
  by_cases hBI : ∃ b : B, ∀ x : B, a (x : H) = (b : H)*x*(b : H)⁻¹
  · by_cases hCI : ∃ c : C, ∀ x : C, a (x : H) = (c : H)*x*(c : H)⁻¹
    · exact (haouter (exists_conj_of_inner_on_commuting_factors B C hcomm hjoin a hBI hCI)).elim
    · have hmix := extraspecial_fixed_of_quaternion_mixed_involution C B hC hB
        (by simpa only [sup_comm] using hjoin) (by simpa only [inf_comm] using hinter)
        (fun c hc b hb => (hcomm b hb c hc).symm) a ha2 hCC hBB hCI hBI
      have hcommF : IsMulCommutative F := hF.toIsMulCommutative
      let : IsMulCommutative F := hcommF
      have hbad : IsMulCommutative F := by infer_instance
      exact (by
        let : IsExtraspecial 2 F := hmix
        have hq : Nontrivial (F ⧸ center F) := IsExtraspecial.quotient_nontrivial 2 F
        exact (QuotientGroup.nontrivial_iff.mp inferInstance
          (center_eq_top_iff.mpr hbad)).elim)
  · by_cases hCI : ∃ c : C, ∀ x : C, a (x : H) = (c : H)*x*(c : H)⁻¹
    · have hmix := extraspecial_fixed_of_quaternion_mixed_involution B C hB hC hjoin hinter hcomm
        a ha2 hBB hCC hBI hCI
      let : IsMulCommutative F := hF.toIsMulCommutative
      have hbad : IsMulCommutative F := by infer_instance
      let : IsExtraspecial 2 F := hmix
      have hq : Nontrivial (F ⧸ center F) := IsExtraspecial.quotient_nontrivial 2 F
      exact (QuotientGroup.nontrivial_iff.mp hq
        (center_eq_top_iff.mpr hbad)).elim
    · have houtB : ¬ ∃ b : B, ∀ x : B, a (x : H) = (b : H)*x*(b : H)⁻¹ := hBI
      have houtC : ¬ ∃ c : C, ∀ x : C, a (x : H) = (c : H)*x*(c : H)⁻¹ := hCI
      obtain ⟨helem, hcard, hcocycle⟩ := quaternion_central_product_outer_involution
        B C hB hC hjoin hinter hcomm a ha2 hBB hCC houtB houtC
      exact ⟨helem, hcard, hcocycle⟩

/-- The elementary fixed-core bound selects the fixed four and the single
core orbit of involutions in the outside coset. -/
public theorem quaternion_elementary_fixed_four_and_coset_orbit
    {T H : Type*} [Group T] [Finite T] [Group H] [Finite H]
    (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (hself : centralizer (P : Set T) ≤ P)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : T) (ht : orderOf t = 2) (hout : t ∉ P)
    (hfixed : IsElementaryAbelian 2 (P.subgroupOf (centralizer ({t} : Set T))))
    (hfixed_card : Nat.card (P.subgroupOf (centralizer ({t} : Set T))) ≤ 4) :
    IsElementaryAbelian 2 (P ⊓ centralizer ({t} : Set T) : Subgroup T) ∧
      Nat.card (P ⊓ centralizer ({t} : Set T) : Subgroup T) = 4 ∧
      (∀ u : T, orderOf u = 2 → u * t⁻¹ ∈ P →
        ∃ h : T, h ∈ P ∧ h * t * h⁻¹ = u) := by
  obtain ⟨helem, hcard, horbit⟩ := elementary_fixed_action
    P e hself B C hB hC hjoin hinter hcomm t ht hout hfixed hfixed_card
  obtain ⟨helem', hcard'⟩ := normalConjThrough_fixed_elementary_card P e t 4 helem hcard
  refine ⟨helem', hcard', ?_⟩
  intro u hu hcoset
  obtain ⟨h, hh⟩ := normalConjThrough_involution_orbit P e t
    (by simpa [ht] using pow_orderOf_eq_one t) horbit u
    (by simpa [hu] using pow_orderOf_eq_one u) hcoset
  exact ⟨h, h.property, hh⟩

end Subgroup
