module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FixedAction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Quasisimple
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank.Components
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Residual

/-!
# E-members for positioned outer four-group actors

An outer involution fixing an SL₂ residual would embed SL₂ into its full
ternary orthogonal fixed group. Equal orders would make this an isomorphism,
contradicting the checked PSL₂ component calculation. Thus the original outer
actor survives the actual radical quotient of the residual supplement.

The quasisimple two-extension constructor now proves every E2 clause, including
the local-tau orbit and O²=solvableResidual. Sylow containment gives E0 and the
intrinsic Sylow intersection. The central involution kills one dimension of
the original four-group in the radical quotient, giving the rank-one member.
No local-structure premise remains in `positioned_four_centralizer_isEMemberAt`.

Source: Aschbacher--Smith E.1.1--2, E.1.5 and E.1.14(7), printed pp.209--210,
214; A.3.21(a), p.55. The orthogonal fixed-group comparison uses GLS3 §§2.7, 4.3.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors

private theorem no_sl2_embedding_in_orthogonal
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (hJ : J.conj = 1)
    (f : SL(2,F) →* J.specialSubgroup) (hf : Function.Injective f) : False := by
  have h2 : (2 : F) ≠ 0 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
    ho (by simpa only [pow_one] using hF : Nat.card F = p ^ 1)
  obtain ⟨s⟩ := orthogonal_equiv_split J hJ h2
  let g := s.toMonoidHom.comp f
  have hg : Function.Injective g := s.injective.comp hf
  have hcardSL : Nat.card SL(2,F) = p * (p ^ 2 - 1) := by
    rw [GorensteinWalter.sl2_card_formula, hF]
  have hcardSO : Nat.card (splitOrthogonalForm F).specialSubgroup = p * (p ^ 2 - 1) := by
    rw [card_splitOrthogonal_specialSubgroup h2, hF]
  have hsurj : Function.Surjective g :=
    ((Nat.bijective_iff_injective_and_card g).mpr ⟨hg, hcardSL.trans hcardSO.symm⟩).2
  let e := MulEquiv.ofBijective g ⟨hg, hsurj⟩
  let : IsQuasisimple SL(2,F) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (hF ▸ hl) (MulEquiv.refl _)
  let : IsQuasisimple (splitOrthogonalForm F).specialSubgroup := IsQuasisimple.of_mulEquiv e
  let H : Subgroup (splitOrthogonalForm F).specialSubgroup := ⊤
  let : IsQuasisimple H := IsQuasisimple.of_mulEquiv topEquiv.symm
  obtain ⟨ec⟩ := TernaryOrthogonal.component_equiv_psl2 hp ho hF
    (show IsComponent _ H from ⟨(inferInstance : H.Normal).isSubnormal, inferInstance⟩)
  have he : Nat.card PSL(2,F) = p * (p ^ 2 - 1) := by
    rw [← Nat.card_congr ec.toEquiv, show H = ⊤ from rfl, card_top, hcardSO]
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  rw [he, hF] at hc
  have hpos : 0 < p * (p ^ 2 - 1) := hcardSL ▸ (Nat.card_pos (α := SL(2,F)))
  omega

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- An outer elementary actor in a subgroup with SL₂ residual survives
its radical quotient; the residual is transported through the literal action. -/
public theorem outer_actor_not_le_radical_of_sl2_residual {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (A K : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hout : ¬ A ≤ innerPart F)
    (e : solvableResidual K ≃* SL(2,F)) :
    ¬ A.subgroupOf K ≤ solvableRadical K := by
  let D := solvableResidual K
  let : IsQuasisimple D :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (hF ▸ hl) e
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hcomp : IsComponent K D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  have hDR : ⁅D, solvableRadical K⁆ = ⊥ := by
    rcases hcomp.normal_dichotomy (solvableRadical K) with hle | hc
    · let : Group.IsSolvable D :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
    · exact hc
  intro hA
  have hDA : ⁅D, A.subgroupOf K⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono le_rfl hA).trans hDR.le)
  let : Group.IsNilpotent (graphExtension F ⧸ innerPart F) := (innerPart_quotient F).isNilpotent
  let : Group.IsPerfect (D.map K.subtype) := Group.IsPerfect.map K.subtype
  have hDL : D.map K.subtype ≤ innerPart F := le_of_isPerfect_of_solvable_quotient _ _
  obtain ⟨t, htA, htL⟩ : ∃ t : graphExtension F, t ∈ A ∧ t ∉ innerPart F := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hout
  let j : D →* (centralizer ({t} : Set (graphExtension F))).subgroupOf (innerPart F) :=
    { toFun := fun x => ⟨⟨x.val.val, hDL (mem_map_of_mem K.subtype x.property)⟩,
        mem_centralizer_singleton_iff.mpr (congrArg (fun y : K => (y : graphExtension F))
          ((commutator_eq_bot_iff_le_centralizer.mp hDA) x.property
            (⟨t, hAK htA⟩ : K) htA)).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : graphExtension F)) h))
  obtain ⟨J, hJ, ⟨ef⟩, _⟩ := outer_actor_orthogonal_embedding F hp ho hF A t htA htL
  let ec := innerCentralizerEquivFixed F t
  exact no_sl2_embedding_in_orthogonal hp ho hl hF J hJ
    (ef.toMonoidHom.comp (ec.toMonoidHom.comp (j.comp e.symm.toMonoidHom)))
    (ef.injective.comp (ec.injective.comp (hj.comp e.symm.injective)))

private theorem four_centralizer_isEMemberAt_of_sl2_residual {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F))
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup _))
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2)
    (z : graphExtension F) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (e : solvableResidual (innerCentralizerSupplement F T z) ≃* SL(2,F)) :
    IsEMemberAt 1 (T : Subgroup _) A (innerCentralizerSupplement F T z) := by
  let K := innerCentralizerSupplement F T z
  let D := solvableResidual K
  let := hA
  have hout : ¬ A ≤ innerPart F := by
    intro h
    rw [inf_eq_left.mpr h, hfour] at hinner
    omega
  have hsurvive := outer_actor_not_le_radical_of_sl2_residual F hp ho hl hF A K
    (hAT.trans le_sup_right) hout e
  have hres : pResidual 2 K = solvableResidual K := by
    let C := centralizer ({z} : Set (graphExtension F))
    let R := (solvableResidual C).map C.subtype
    let : Group.IsPerfect R := Group.IsPerfect.map C.subtype
    have hn : C ≤ normalizer (R : Set (graphExtension F)) := by
      have h := (solvableResidual C).le_normalizer_map C.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
    exact pResidual_eq_solvableResidual_of_perfect_sup_twoGroup R T T.isPGroup' (hTz.trans hn)
  let : IsQuasisimple D :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (hF ▸ hl) e
  have hcenter : IsPGroup 2 (center D) :=
    ((GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F (hF ▸ ho)).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker F))).of_equiv
        (centerCongr e).symm
  have hq : IsPGroup 2 (K ⧸ D) :=
    (isPGroup_quotient_pResidual (G := K) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hres)
  exact innerCentralizerSupplement_isEMemberAt F T A hA hfour hAT z hz hzA hTz
    (PSUThreeGeneration.eCaseComponent_of_quasisimple_two_quotient _ A K D hcenter hq hsurvive)

/-- All source E0, E2 and quotient-rank clauses for the actual positioned actor. -/
public theorem positioned_four_centralizer_isEMemberAt {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F))
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup _))
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    IsEMemberAt 1 (T : Subgroup _) A (innerCentralizerSupplement F T z) := by
  obtain ⟨e⟩ := supplement_residual_equiv_sl2 F hp ho hl hF T z hzL hz hTz
  exact four_centralizer_isEMemberAt_of_sl2_residual F hp ho hl hF T A hA hAT
    hfour hinner z hz hzA hTz e

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors
