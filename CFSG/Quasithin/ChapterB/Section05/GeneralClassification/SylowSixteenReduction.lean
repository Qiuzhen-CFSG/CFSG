module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors
import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
import Theory.GroupTheory.PrimeRankSquareFree
import Theory.GroupTheory.PrimeRankZero
import Theory.Representation.NormalComponentConstituents
import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image
import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The complete B.5 sieve for the original opposite-normalizer six-space

The literal A₅ offender fixes a nonzero vector. In dimension at most six,
25 does not divide the order of a faithful binary actor. Consequently a
subnormal A₅ is the unique component containing five and is normal in the
whole actor, contradicting irreducibility and that fixed vector. This kills
the two-factor rows and the quasisimple A₅ row. The hyperplane row is excluded
by the Sylow-sixteen bound. The surviving actual offender subgroup has an
A₆, A₇ or cubic A₆ fitting component, or the exact outer A₆–C₃ configuration.
The last configuration is deliberately retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem five_card : Nat.card (alternatingGroup (Fin 5))=60 := by
  rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]

private theorem subgroup_small (small : ∀ S : Sylow 2 D, Nat.card S≤16)
    (A : Subgroup D) (S : Sylow 2 A) : Nat.card S≤16 := by
  obtain ⟨P,hSP⟩ := (S.isPGroup'.map A.subtype).exists_le_sylow
  have hh := (card_le_of_le hSP).trans (small P)
  rwa [card_map_of_injective A.subtype_injective] at hh

private theorem subnormal_five_fixed_zero (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (hd : Module.finrank (ZMod 2) V≤6)
    {C : Subgroup D} (hs : C.IsSubnormal) (eC : C≃*alternatingGroup (Fin 5)) :
    fixedSpace ρ C=⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup C := eC.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  have hz : center C=⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  let : IsQuasisimple C := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : IsComponent D C := ⟨hs,inferInstance⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hrD : primeRank 5 D≤1 := primeRank_le_one_of_square_not_dvd (no_twentyFive hf hd)
  have hCcard : Nat.card C=60 := (Nat.card_congr eC.toEquiv).trans five_card
  have hrC : primeRank 5 C≠0 := by
    intro he
    have hh := (PrimeRank.eq_zero_iff_not_dvd_card (G := C) (p := 5)).mp he
    exact hh (by rw [hCcard]; decide)
  let : C.Normal := hc.normal_of_centerless_of_primeRank hz 5 (by omega)
  apply fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi C
  intro he
  rw [he,card_bot] at hCcard
  omega

private theorem hom_to_six_trivial {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    (e : A≃*alternatingGroup (Fin 5)) (hc : Nat.card E=6) (f : A→*E) (a : A) : f a=1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup A := e.isSimpleGroup
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hh := card_dvd_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp hb)
    rw [Nat.card_congr e.toEquiv,five_card,hc] at hh
    norm_num at hh
  · exact show a∈f.ker from ht ▸ mem_top a

private theorem product_five_subnormal {C : Subgroup D}
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V≤6)
    (small : ∀ S : Sylow 2 D, Nat.card S≤16)
    (c : SourceTwoFactorCase ρ) (eC : C≃*alternatingGroup (Fin 5)) : C.IsSubnormal := by
  have hCcard : Nat.card C=60 := (Nat.card_congr eC.toEquiv).trans five_card
  have hfive : 5∣Nat.card D := (by decide : 5∣60).trans (hCcard ▸ C.card_subgroup_dvd_card)
  have leftSide (F E : Subgroup D) (p : InternalProduct F E)
      (hF : Nat.card F=60 ∨ Nat.card F=120) (hE : Nat.card E=6) : C.IsSubnormal := by
    let f := p.swap.fst.comp C.subtype
    have hCF : C≤F := by
      rw [←p.swap.ker_fst]
      intro x hx
      exact hom_to_six_trivial eC hE f ⟨x,hx⟩
    let : F.Normal := p.swap.second_normal
    rcases hF with hF | hF
    · have heq : C=F := eq_of_le_of_card_ge hCF (by rw [hCcard,hF])
      rw [heq]
      exact (inferInstance : F.Normal).isSubnormal
    · have hh := (C.subgroupOf F).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hCF).toEquiv,hCcard,hF] at hh
      have hindex : (C.subgroupOf F).index=2 :=
        Nat.eq_of_mul_eq_mul_left (by decide : 0<60) hh
      have hn := normal_of_index_eq_two hindex
      exact IsSubnormal.trans hCF hn.isSubnormal (inferInstance : F.Normal).isSubnormal
  rcases twoFactor_card_rows hf hd small hfive c with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact leftSide c.first c.second c.product h1 h2
  · exact leftSide c.second c.first c.product.swap h2 h1

omit [FiniteDimensional (ZMod 2) V] in
private theorem perfect_le_source {L C : Subgroup D}
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) [Group.IsPerfect C] : C≤L := by
  let : L.Normal := by rw [c.fitting_eq]; infer_instance
  have hp : IsPGroup 2 (D ⧸ L) := by
    have topCase (he : L=⊤) : IsPGroup 2 (D ⧸ L) :=
      isPGroup_quotient_of_sup_eq_top L ⊥ (IsPGroup.of_subsingleton 2 _) (by rw [he]; simp)
    cases c.clause_one with
    | irreducible _ _ _ _ extension =>
      rcases extension with he | ⟨hs,_⟩
      · exact topCase he
      · let S : Sylow 2 D := default
        exact isPGroup_quotient_of_sup_eq_top L S S.isPGroup' (hs S)
    | doubleThree _ he _ _ _ => exact topCase he
    | naturalDual _ _ he _ => exact topCase he
    | repeatedNatural _ _ _ _ _ he _ => exact topCase he
  let : Group.IsNilpotent (D ⧸ L) := hp.isNilpotent
  exact le_of_isPerfect_of_solvable_quotient C L

/-- Complete B.5 leaves precisely the three non-A₅ quasisimple markings or
the actual outer A₆–C₃ shape on the literal normal offender subgroup. -/
theorem rows_from_source (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V≤6)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (small : ∀ S : Sylow 2 D, Nat.card S≤16)
    (C : Subgroup D) (hCJ : C≤offenderSubgroup ρ)
    (eC : C≃*alternatingGroup (Fin 5)) (hfix : fixedSpace ρ C≠⊥) :
    let J := offenderSubgroup ρ
    let F := generalizedFitting J
    (IsQuasisimple F ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp J.subtype) F) ∧
      (Nonempty (F≃*alternatingGroup (Fin 6)) ∨
        Nonempty (F≃*alternatingGroup (Fin 7)) ∨
        Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
          Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)))) ∨
      Nonempty (OuterSixThreeShape J) := by
  let J := offenderSubgroup ρ
  let σ := ρ.comp J.subtype
  let CJ := C.subgroupOf J
  let eCJ := (subgroupOfEquivOfLe hCJ).trans eC
  let : J.Normal := offenderSubgroup_normal ρ
  let : ρ.IsIrreducible := hi
  have hcore := Representation.QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible ρ hf
  have adequate := offenderSubgroup_adequateAlternative ρ hf hcore cover
  have hfJ : Function.Injective σ := hf.comp J.subtype_injective
  have smallJ := subgroup_small small J
  have hCJcard : Nat.card CJ=60 := (Nat.card_congr eCJ.toEquiv).trans five_card
  have hfive : 5∣Nat.card J := (by decide : 5∣60).trans (hCJcard ▸ CJ.card_subgroup_dvd_card)
  have notSubnormal (hs : CJ.IsSubnormal) : False :=
    hfix (subnormal_five_fixed_zero ρ hf hi hd
      (IsSubnormal.trans hCJ hs (inferInstance : J.Normal).isSubnormal) eC)
  rcases adequate with htriv | adequate
  · let := htriv
    have hh : Nat.card J=1 := Nat.card_unique
    rw [hh] at hfive
    norm_num at hfive
  · cases adequate with
    | symmetricThree c =>
      rw [Nat.card_congr c.equiv.toEquiv] at hfive
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hfive
    | twoFactors c => exact (notSubnormal (product_five_subnormal σ hfJ hd smallJ c eCJ)).elim
    | hyperplane c => exact (not_hyperplane hfJ hd smallJ hfive c).elim
    | outerSixThree c => exact Or.inr ⟨c⟩
    | quasisimple hq source =>
      let F := generalizedFitting J
      let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      let : Group.IsPerfect CJ :=
        Group.IsPerfect.ofSurjective (f := eCJ.symm.toMonoidHom) eCJ.symm.surjective
      have hCF : CJ≤F := perfect_le_source σ source
      have hfF : Function.Injective (σ.comp F.subtype) := hfJ.comp F.subtype_injective
      have h5F : 5∣Nat.card F := (by decide : 5∣60).trans
        (hCJcard ▸ card_dvd_of_le hCF)
      have rows := quasisimple_source_rows (σ.comp F.subtype) hfF hd
        (subgroup_small smallJ F) h5F hq σ F (MulEquiv.refl F) source
      rcases rows with hA5 | hA6 | hA7 | hTriple
      · obtain ⟨eF⟩ := hA5
        have hFcard : Nat.card F=60 := (Nat.card_congr eF.toEquiv).trans five_card
        have heq : CJ=F := eq_of_le_of_card_ge hCF (by rw [hCJcard,hFcard])
        have hs : CJ.IsSubnormal := by
          rw [heq]
          exact (inferInstance : F.Normal).isSubnormal
        exact (notSubnormal hs).elim
      · exact Or.inl ⟨hq,⟨source⟩,Or.inl hA6⟩
      · exact Or.inl ⟨hq,⟨source⟩,Or.inr (Or.inl hA7)⟩
      · exact Or.inl ⟨hq,⟨source⟩,Or.inr (Or.inr hTriple)⟩

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
