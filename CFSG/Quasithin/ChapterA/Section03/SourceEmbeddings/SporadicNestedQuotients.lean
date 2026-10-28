module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Quasisimple sections in the two surviving large sporadic models

An SQTK C-component with a factor seven and order dividing M₂₄ or J₄
cannot have either nonquasisimple A.3.6 structure. In the natural case,
the order is p²·|SL₂(p)|. The only possible prime p>3 with p² dividing
either sporadic order is eleven, and the resulting order is prime to
seven. In the nilpotent case, seven divides the Fitting subgroup because
the quotient has order 120. Its prescribed Sylow shape then forces 7²
to divide the original order, which is impossible in both carriers.

The noncentral A.3.6 theorem supplies the structural alternatives; central
Fitting subgroup gives quasisimplicity directly. The last theorem applies
the argument through the intrinsic O₂ quotient. Components/Sporadic applies
it to the actual nested components of 12.9.3 and their model isomorphisms.

Source: Aschbacher--Smith A.3.6, pp.43--45, and 12.9.3, pp.858--859;
ATLAS orders of M₂₄ and J₄, certified on the original carriers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNested
open Chapter1.Section02 LocalModels

private theorem square_prime {p : ℕ} (hp : p.Prime) (hl : 3 < p)
    (hd : p ^ 2 ∣ 244823040 ∨ p ^ 2 ∣ 86775571046077562880) : p = 11 := by
  rcases hd with hd | hd
  · have hpd := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
    have he : 244823040 = 2^10*3^3*5*7*11*23 := by norm_num
    rw [he] at hpd
    simp only [hp.dvd_mul, or_assoc] at hpd
    rcases hpd with h | h | h | h | h | h
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h; omega
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h; omega
    all_goals
      have he := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
      subst p
      norm_num at hd
  · have hpd := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
    have he : 86775571046077562880 = 2^21*3^3*5*7*11^3*23*29*31*37*43 := by norm_num
    rw [he] at hpd
    simp only [hp.dvd_mul, or_assoc] at hpd
    rcases hpd with h | h | h | h | h | h | h | h | h | h
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h; omega
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h; omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h
      subst p; norm_num at hd
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
      subst p; norm_num at hd
    · exact Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 11) h
    all_goals
      have he := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
      subst p
      norm_num at hd

private theorem seven_square_free {m : ℕ}
    (hd : m ∣ 244823040 ∨ m ∣ 86775571046077562880) : ¬ 7^2 ∣ m := by
  intro h
  rcases hd with hd | hd
  · have := h.trans hd; norm_num at this
  · have := h.trans hd; norm_num at this

private theorem natural_impossible {A : Type*} [Group A] [Finite A]
    (h : A36Natural A) (h7 : 7 ∣ Nat.card A)
    (hd : Nat.card A ∣ 244823040 ∨ Nat.card A ∣ 86775571046077562880) : False := by
  obtain ⟨p,hp,hl,F,hF,hfin,hcard,v,e,hact⟩ := h.2
  have hc : Nat.card A = p^2 * (p * (p^2-1)) := by
    rw [← (generalizedFitting A).card_mul_index, index_eq_card,
      Nat.card_congr v.toEquiv,Nat.card_congr e.toEquiv,
      GorensteinWalter.sl2_card_formula,hcard]
    change Nat.card (Fin 2 → F) * _ = _
    rw [Nat.card_fun,Nat.card_fin,hcard]
  have hs : p^2 ∣ Nat.card A := by rw [hc]; exact dvd_mul_right _ _
  have he : p = 11 := square_prime hp hl (hd.imp (hs.trans ·) (hs.trans ·))
  rw [hc,he] at h7
  norm_num at h7

private theorem nilpotent_impossible {A : Type*} [Group A] [Finite A]
    (h : A36Nilpotent A) (h7 : 7 ∣ Nat.card A)
    (hd : Nat.card A ∣ 244823040 ∨ Nat.card A ∣ 86775571046077562880) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h.2.2.1
  have hc : Nat.card A = Nat.card (generalizedFitting A) * 120 := by
    rw [← (generalizedFitting A).card_mul_index,index_eq_card,
      Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hcard]
    norm_num
  have hf7 : 7 ∣ Nat.card (generalizedFitting A) :=
    ((by decide : Nat.Prime 7).dvd_mul.mp (hc ▸ h7)).resolve_right (by decide)
  have hs := (h.2.2.2 7 (by decide) hf7).2
  have hsquare : 7^2 ∣ Nat.card (pCore 7 A) := by
    rcases hs with ⟨⟨_,hc⟩,_⟩ | ⟨a,ha,⟨f⟩⟩
    · rw [hc]; exact pow_dvd_pow 7 (by decide : 2 ≤ 1 + 2 * 1)
    · rw [Nat.card_congr f.toEquiv]
      change 7^2 ∣ Nat.card (Fin 2 → ZMod (7^a))
      rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      rw [←pow_mul]
      exact pow_dvd_pow 7 (by omega)
  exact seven_square_free hd (hsquare.trans (pCore 7 A).card_subgroup_dvd_card)

/-- The exceptional nonquasisimple A.3.6 alternatives cannot have a factor
seven and an order dividing either of the two surviving sporadic point models. -/
theorem quasisimple_of_a36_sporadic_order {E : Type*} [Group E] [Finite E]
    {C : Subgroup E} (h : A36Conclusion C) (h7 : 7 ∣ Nat.card C)
    (hd : Nat.card C ∣ 244823040 ∨ Nat.card C ∣ 86775571046077562880) :
    IsQuasisimple C := by
  cases h.1 with
  | simple hc _ _ => exact hc.2
  | cover hc _ _ => exact hc.2
  | natural hn => exact (natural_impossible hn h7 hd).elim
  | nilpotent hn => exact (nilpotent_impossible hn h7 hd).elim

/-- The actual noncentral A.3.6 theorem discharges the classification premise. -/
theorem quasisimple_of_sporadic_order {E : Type*} [Group E] [Finite E]
    {κ : GroupClass} (hsq : IsSQTK κ E) (h2 : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent) (h7 : 7 ∣ Nat.card C)
    (hd : Nat.card C ∣ 244823040 ∨ Nat.card C ∣ 86775571046077562880) :
    IsQuasisimple C := by
  by_cases hf : fittingSubgroup C ≤ center C
  · have hr : solvableRadical C = center C := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
      exact le_solvableRadical (center C) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  · exact quasisimple_of_a36_sporadic_order
      (NoncentralFitting.conclusion_of_noncentral hsq h2 hC hf).1 h7 hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNested

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNested

/-- Apply the order obstruction to the original intrinsic two-core quotient. -/
theorem twoCore_quotient_quasisimple_of_sporadic_order
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    (hsq : IsSQTK κ G) {C : Subgroup G} (hC : C.IsCComponent)
    (h7 : 7 ∣ Nat.card (C ⧸ pCore 2 C))
    (hd : Nat.card (C ⧸ pCore 2 C) ∣ 244823040 ∨
      Nat.card (C ⧸ pCore 2 C) ∣ 86775571046077562880) :
    IsQuasisimple (C ⧸ pCore 2 C) := by
  let Q := C ⧸ pCore 2 C
  have htop : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := C)
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 C))] using
      htop.map_quotient (pCore 2 C)
  have hsqQ := ChapterE.Structure.sqtk_two_quotient (hsq.subgroup C)
    (pCore 2 C) pCore_isPGroup
  have hc : Nat.card (⊤ : Subgroup Q) = Nat.card Q := Nat.card_congr topEquiv.toEquiv
  exact (quasisimple_of_sporadic_order hsqQ (pCore_quotient_pCore_eq_bot 2) hQ
    (hc.symm ▸ h7) (hc.symm ▸ hd)).of_mulEquiv topEquiv

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNested
