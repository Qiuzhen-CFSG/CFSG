module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondSolvableExclusion
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The actual prime-to-three quotient of the second amalgam

The proved inequality of the vertex cores excludes the collapsed branch
of F.6.11. Thus the literal quotient by O₃′(Y) retains the two vertices
and their original common Sylow image, and its two-core is trivial.
The order-two overlap in F.6.18(1) is excluded by the same core inequality.
The solvability of O₃′(Y), together with the proved nonsolvability of Y,
makes the quotient nonsolvable as well.

The statement retains the original quotient maps and subgroup embeddings.
It supplies the genuine quotient pair, not an abstract marked model.
Source: Aschbacher--Smith F.6.11, pp.306--307; 13.4.7(3), p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem original_plane_second_prime_quotient
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    let X := A ⊔ B
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Q := Y₂ ⊔ (T : Subgroup G)
    let Y := P ⊔ Q
    let q := QuotientGroup.mk' (pPrimeCore 3 Y)
    let Pp := (P.subgroupOf Y).map q
    let Qp := (Q.subgroupOf Y).map q
    ¬ Group.IsSolvable (Y ⧸ pPrimeCore 3 Y) ∧
      Pp ⊓ Qp = ((T : Subgroup G).subgroupOf Y).map q ∧
      ChapterF.IsGoldschmidtTriple Pp Qp ∧
      pCore 2 (Y ⧸ pPrimeCore 3 Y) = ⊥ ∧
      ¬ Nonempty ((Pp ⊓ Qp : Subgroup _) ≃* Multiplicative (ZMod 2)) := by
  let X := A ⊔ B
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let Y := P ⊔ Q
  have hns := original_plane_second_nonsolvable h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM
  obtain ⟨_,_,_,_,_,hint,hg,_⟩ := original_plane_second_amalgam h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane
  have hcores := (original_plane_second_thompson h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane).2.2.2
  have hci : (P.subgroupOf Y).pCoreIn 2 ≠ (Q.subgroupOf Y).pCoreIn 2 := by
    intro he
    have hm := congrArg (map Y.subtype) he
    rw [pCoreIn_subgroupOf 2 P Y le_sup_left,pCoreIn_subgroupOf 2 Q Y le_sup_right,
      map_subgroupOf_eq_of_le ((P.pCoreIn_le 2).trans le_sup_left),
      map_subgroupOf_eq_of_le ((Q.pCoreIn_le 2).trans le_sup_right)] at hm
    exact hcores hm
  have hprime := hg.primeToThreeCore_dichotomy.resolve_right
    (fun hh => hci (hh.1.trans hh.2.1.symm))
  refine ⟨?_,?_,hprime.2.1,hprime.2.2.1,
    hg.primeToThreeCore_intersection_not_cyclic_two hci⟩
  · intro hq
    exact hns ((Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 Y)).mpr
      ⟨hg.primeToThreeCore_solvable,hq⟩)
  · have hh := hprime.1
    change _ = ((P ⊓ Q).subgroupOf Y).map _ at hh
    rwa [hint] at hh


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
