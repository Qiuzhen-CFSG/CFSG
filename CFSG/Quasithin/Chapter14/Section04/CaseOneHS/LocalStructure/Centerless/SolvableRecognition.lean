module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableFaithful
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.SquareField

/-!
# Recognizing the original prime-to-three quotient as PSL₃(2)

The actual moving faithful component has a simple subnormal image in
Ke/O₃′(Ke). Apply the existing generic small-component comparisons to every
F.6.18 row, including the additional ambient dihedral and square-field
branches. The quasisimple generalized Fitting subgroup must equal that
image. Its order excludes the larger component rows; the product row is
excluded by its specified outer actions. The remaining whole-component
row has a Sylow subgroup of order eight, excluding A₅ and identifying the
original image and the whole quotient with PSL₃(2).

The application retains the same Ke, reduced orbit module, involution and
canonical faithful component. It does not yet identify the original action
quotient or prove the final module-dimension contradiction.
Source: Aschbacher--Smith 14.3.31, printed p.1003, using F.6.18,
printed pp.309--310 and the earlier 14.3.4 classification.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource
open Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

private theorem small_fitting_top {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.IsSubnormal) (hm : SmallModel N)
    (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤)
    (S : Sylow 2 D) (hS : Nat.card S ≠ 4) :
    N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨he,hs⟩ := fitting_eq_small N hN hm hq
  have htop := he.symm.trans ht
  refine ⟨htop,?_⟩
  rcases hs with hs | hs <;> obtain ⟨e⟩ := hs
  · exact ⟨e.trans Matrix.PSL3Two.equiv⟩
  · have hc : Nat.card D = 60 := by
      let a : D ≃* alternatingGroup (Fin 5) :=
        topEquiv.symm.trans ((MulEquiv.subgroupCongr htop).symm.trans e)
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact (hS (by rw [S.card_eq_multiplicity,hc]; decide +kernel)).elim

private theorem source_small_image_top {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.IsSubnormal) (hm : SmallModel N)
    {A B : Subgroup D} {S : Sylow 2 D} (ha : SourceAlternative A B S)
    (h1 : ¬ Nonempty (S ≃* C 2))
    (h2 : ¬ (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ M : Subgroup D, ∃ _ : M.Normal,
        IsExtraspecial 3 M ∧ Nat.card M = 27 ∧ Monoid.exponent M = 3 ∧
        Nonempty ((D ⧸ M) ≃* E4))) :
    N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
  have hd (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤)
      (hs : Nonempty (S ≃* DihedralGroup 4)) :
      N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
    obtain ⟨e⟩ := hs
    apply small_fitting_top N hN hm hq ht S
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    decide
  rcases ha with (ha | ⟨r⟩) | ⟨r⟩
  · cases ha with
    | one hs _ _ _ => exact (h1 hs).elim
    | two hs => exact (h2 hs).elim
    | three r hs _ _ =>
      obtain ⟨e⟩ := hs
      exact (not_product_row S (by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]) r N hN hm).elim
    | four f hd hc e ht hq _ _ _ =>
      let a : generalizedFitting D ≃* D := (MulEquiv.subgroupCongr ht).trans topEquiv
      exact (not_prime_linear_component N hN hm hq f hd hc (a.trans e)).elim
    | five f hd hc _ e hq _ _ _ =>
      exact (not_prime_linear_component N hN hm hq f hd hc e).elim
    | six _ ht hq hs _ _ => exact hd hq ht hs
    | seven hs hq _ _ _ =>
      apply (not_exceptional_model N hN hm hq _).elim
      exact hs.elim Or.inl (fun h => Or.inr (Or.inl h))
    | eight hs hq _ _ _ =>
      rcases hs with hs | ⟨r⟩
      · exact (not_exceptional_model N hN hm hq (Or.inr (Or.inr (Or.inl hs)))).elim
      · exact (not_field_extension N hN hm hq r.some).elim
    | nine hs hq _ _ _ =>
      apply (not_exceptional_model N hN hm hq _).elim
      exact hs.elim (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | ten _ _ _ _ ht hq hs _ _ =>
      obtain ⟨e⟩ := hs
      have h32 : Nat.card S = 32 := by
        rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
        norm_num [C]
      obtain ⟨he,hm'⟩ := fitting_eq_small N hN hm hq
      let a : D ≃* N := topEquiv.symm.trans (MulEquiv.subgroupCongr (he.symm.trans ht)).symm
      have hdvd := (S : Subgroup D).card_subgroup_dvd_card
      rcases hm' with hh | hh <;> obtain ⟨j⟩ := hh
      · rw [h32,Nat.card_congr (a.trans j).toEquiv,Matrix.PSL3Two.card_SL] at hdvd
        norm_num at hdvd
      · rw [h32,Nat.card_congr (a.trans j).toEquiv,nat_card_alternatingGroup] at hdvd
        norm_num [Nat.factorial] at hdvd
    | eleven r hq _ _ _ =>
      exact (not_degreeThree_component N hN hm hq r.prime_isPrime r.congruence r.model.model).elim
    | twelve e hq _ _ _ =>
      exact (not_exceptional_model N hN hm hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))).elim
    | thirteen _ e hq _ _ _ => exact (not_mathieu_component N hN hm hq e).elim
  · exact hd r.some.quasisimple r.some.component r.some.sylow
  · exact (not_square_field_extension N hN hm r.some).elim

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full F.6.18 comparison identifies the literal prime-to-three quotient
and shows that the selected original faithful component maps onto it. -/
theorem source_solvable_quotient_recognition_with_actor (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      Nonempty ((E ⧸ pPrimeCore 3 E) ≃* Matrix.PSL3Two.PSL) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        ⁅amalgamModule F L K,C⁆ ≠ ⊥ ∧
        (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T ∧
        (C.subgroupOf E).map (QuotientGroup.mk' (pPrimeCore 3 E)) = ⊤ := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,_,_,_,_,hf,hm,h1,⟨S,hS,hrows⟩,_,hn⟩ :=
    source_solvable_source_classification_with_actor d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let p := QuotientGroup.mk' (pPrimeCore 3 E)
  obtain ⟨C,hC,hfaith,hmove,_,hnormal,hmax,hsub,hsmall⟩ :=
    source_amalgam_classified_component d chosen F K classification hr hn
  let N := (C.subgroupOf E).map p
  have hsmall' : SmallModel N := by
    rcases hsmall with ha | ha <;> obtain ⟨a⟩ := ha
    · exact Or.inr (Or.inr ⟨a⟩)
    · exact Or.inr (Or.inl ⟨a.trans Matrix.PSL3Two.equiv.symm⟩)
  have hS1 : ¬ Nonempty (S ≃* FSource.C 2) := by
    rintro ⟨j⟩
    exact h1 ⟨(MulEquiv.subgroupCongr hS).trans j⟩
  have h2 : ¬ (Nonempty ((E ⧸ pPrimeCore 3 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ M : Subgroup (E ⧸ pPrimeCore 3 E), ∃ _ : M.Normal,
        IsExtraspecial 3 M ∧ Nat.card M = 27 ∧ Monoid.exponent M = 3 ∧
        Nonempty (((E ⧸ pPrimeCore 3 E) ⧸ M) ≃* E4)) := by
    rintro (hp | ⟨M,hM,_,hc,_,⟨eM⟩⟩)
    · exact SymmetricThreeTwoCore.characteristic_two_not_symmetric_three_product _ hf hm.some hp
    · let := hM
      have hM3 : IsPGroup 3 M := IsPGroup.of_card (n := 3) hc
      have hQ2 : IsPGroup 2 (_ ⧸ M) := by
        apply (IsPGroup.of_card (n := 2) (G := E4) ?_).of_equiv eM.symm
        simp [E4,FSource.C]
      exact SymmetricThreeTwoCore.characteristic_two_not_three_by_two _ hf hm.some M hM3 hQ2
  obtain ⟨ht,⟨a⟩⟩ := hrows.elim
    (fun h => source_small_image_top N hsub hsmall' h hS1 h2)
    (fun h => source_small_image_top N hsub hsmall' h hS1 h2)
  let j : (E ⧸ pPrimeCore 3 E) ≃* N :=
    topEquiv.symm.trans (MulEquiv.subgroupCongr ht).symm
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,⟨j.trans a⟩,C,hC,hfaith,hmove,hnormal,hmax,ht⟩

/-- The quotient recognition with the original public conclusion. -/
theorem source_solvable_quotient_recognition (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      Nonempty ((E ⧸ pPrimeCore 3 E) ≃* Matrix.PSL3Two.PSL) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        ⁅amalgamModule F L K,C⁆ ≠ ⊥ ∧
        (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T ∧
        (C.subgroupOf E).map (QuotientGroup.mk' (pPrimeCore 3 E)) = ⊤ := by
  obtain ⟨l,e,hl,he,heI,heT,_,_,_,_,_,_,hrest⟩ :=
    source_solvable_quotient_recognition_with_actor d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,hrest⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
