module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ElementarySylowEight.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The actual alternating-five subgroup in the adequate B.5 alternatives

With elementary Sylow subgroups of order at most eight, a marked A5 in an
adequate actor is its normal A5 factor. The product alternative is retained:
its other factor is S3. The proof never promotes an arbitrary embedded A5 to
a component before checking the complete alternatives.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem card_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]

private theorem linearTwo_card (h : Bound D) (F : BinaryField)
    (e : D ≃* SL(2,F.Carrier)) :
    Nat.card D = 6 ∨ Nat.card D = 60 ∨ Nat.card D = 504 := by
  have hi := linearTwo_degree_le_three h F e
  have lo := F.degree_pos
  have hc : Nat.card D = 2 ^ F.degree * ((2 ^ F.degree) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq]
  interval_cases hd : F.degree <;> norm_num [hd] at hc ⊢ <;> omega

private theorem factor_card {A : Subgroup D} {U : Subrepresentation ρ}
    (h : Bound D) (c : SourceFactorCase ρ A U) :
    Nat.card A = 6 ∨ Nat.card A = 60 ∨ Nat.card A = 504 := by
  have hb : Bound A := h.of_injective A.subtype A.subtype_injective
  cases c with
  | natural _ hn =>
    cases hn with
    | linearTwo F he =>
      obtain ⟨e⟩ := he
      exact linearTwo_card hb F e.groupEquiv
    | symmetricFive he =>
      obtain ⟨e⟩ := he
      exact (no_symmetric_five (hb.of_surjective e.groupEquiv.toMonoidHom e.groupEquiv.surjective)).elim
    | linearThree F _ he =>
      obtain ⟨e⟩ := he
      exact (no_linearThree hb F e.groupEquiv).elim
  | doubleNatural F _ _ he =>
    obtain ⟨e⟩ := he
    exact (no_linearThree hb F e.groupEquiv).elim
  | exceptional _ he =>
    exact (no_linearThree hb BinaryField.two he.natural.groupEquiv).elim

private theorem perfect_le_of_source {L C : Subgroup D}
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    [Group.IsPerfect C] : C ≤ L := by
  let : L.Normal := by rw [c.fitting_eq]; infer_instance
  have hp : IsPGroup 2 (D ⧸ L) := by
    have ht (he : L = ⊤) : IsPGroup 2 (D ⧸ L) := by
      exact isPGroup_quotient_of_sup_eq_top L ⊥ (IsPGroup.of_subsingleton 2 _)
        (by rw [he]; simp)
    cases c.clause_one with
    | irreducible _ _ _ _ extension =>
      rcases extension with he | ⟨hs,_⟩
      · exact ht he
      · let S : Sylow 2 D := default
        exact isPGroup_quotient_of_sup_eq_top L S S.isPGroup' (hs S)
    | doubleThree _ he _ _ _ => exact ht he
    | naturalDual _ _ he _ => exact ht he
    | repeatedNatural _ _ _ _ _ he _ => exact ht he
  let : Group.IsNilpotent (D ⧸ L) := hp.isNilpotent
  exact le_of_isPerfect_of_solvable_quotient C L

private theorem quasisimple_normal {L C : Subgroup D}
    (h : Bound D) (hq : IsQuasisimple L)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (eC : C ≃* alternatingGroup (Fin 5)) : C.Normal := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  have hCL : C ≤ L := perfect_le_of_source c
  have hcC : Nat.card C = 60 := (Nat.card_congr eC.toEquiv).trans card_five
  have hb : Bound L := h.of_injective L.subtype L.subtype_injective
  have hm := ChapterC.C27Source.SmallModels.model_of_source ρ
    (fun S => (hb.sylow S).2.trans (by decide : 8 ≤ 128)) hq (MulEquiv.refl L) c
  obtain ⟨eL⟩ := smallModel_five hb hm (by
    have hd := card_dvd_of_le hCL
    rw [hcC] at hd
    exact (by decide : 5 ∣ 60).trans hd)
  have hcL : Nat.card L = 60 := (Nat.card_congr eL.toEquiv).trans card_five
  have he : C = L := eq_of_le_of_card_ge hCL (by rw [hcC,hcL])
  rw [he,c.fitting_eq]
  infer_instance

private theorem hom_to_six_trivial {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* alternatingGroup (Fin 5)) (hc : Nat.card B = 6)
    (f : A →* B) (a : A) : f a = 1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup A := e.isSimpleGroup
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hd := card_dvd_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp hb)
    rw [Nat.card_congr e.toEquiv,card_five,hc] at hd
    norm_num at hd
  · exact show a ∈ f.ker from ht ▸ mem_top a

private theorem product_normal {C : Subgroup D} (h : Bound D)
    (c : SourceTwoFactorCase ρ) (eC : C ≃* alternatingGroup (Fin 5)) : C.Normal := by
  have hcC : Nat.card C = 60 := (Nat.card_congr eC.toEquiv).trans card_five
  have hf : 5 ∣ Nat.card D := (by decide : 5 ∣ 60).trans
    (hcC ▸ C.card_subgroup_dvd_card)
  have hb := h.not_sixteen_dvd
  have he := c.product.card_eq
  have hc : (Nat.card c.first = 60 ∧ Nat.card c.second = 6) ∨
      (Nat.card c.first = 6 ∧ Nat.card c.second = 60) := by
    rcases factor_card h c.firstCase with h1 | h1 | h1 <;>
      rcases factor_card h c.secondCase with h2 | h2 | h2
    all_goals first | exact Or.inl ⟨h1,h2⟩ | exact Or.inr ⟨h1,h2⟩ | norm_num [h1,h2,he] at *
  have left_normal (d : SourceTwoFactorCase ρ)
      (h1 : Nat.card d.first = 60) (h2 : Nat.card d.second = 6) : C.Normal := by
    let f := d.product.swap.fst.comp C.subtype
    have hle : C ≤ d.first := by
      rw [←d.product.swap.ker_fst]
      intro x hx
      exact hom_to_six_trivial eC h2 f ⟨x,hx⟩
    have heq : C = d.first := eq_of_le_of_card_ge hle (by rw [hcC,h1])
    rw [heq]
    exact d.product.swap.second_normal
  rcases hc with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact left_normal c h1 h2
  · let f := c.product.fst.comp C.subtype
    have hle : C ≤ c.second := by
      rw [←c.product.ker_fst]
      intro x hx
      exact hom_to_six_trivial eC h1 f ⟨x,hx⟩
    have heq : C = c.second := eq_of_le_of_card_ge hle (by rw [hcC,h2])
    rw [heq]
    exact c.product.second_normal

/-- Every marked A5 in an adequate actor with these actual Sylow bounds is
normal. The A5 times S3 product alternative is included in the proof. -/
theorem normal_of_adequate {C : Subgroup D} (h : Bound D)
    (c : AdequateAlternative ρ) (eC : C ≃* alternatingGroup (Fin 5)) : C.Normal := by
  rcases c with htriv | c
  · let := htriv
    have he : C = ⊤ := Subsingleton.elim _ _
    rw [he]
    infer_instance
  · cases c with
    | quasisimple hq source => exact quasisimple_normal h hq source eC
    | symmetricThree c =>
      have hd := C.card_subgroup_dvd_card
      rw [Nat.card_congr eC.toEquiv,card_five,Nat.card_congr c.equiv.toEquiv] at hd
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hd
    | twoFactors c => exact product_normal h c eC
    | outerSixThree c =>
      have hb := h.of_injective c.first.subtype c.first.subtype_injective
      exact (no_alternating_six (hb.of_surjective c.firstEquiv.toMonoidHom c.firstEquiv.surjective)).elim
    | hyperplane c =>
      exact (no_linearThree (h.of_injective c.first.subtype c.first.subtype_injective)
        BinaryField.two c.firstEquiv).elim

end CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
