module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointResidual
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The original triple-six point residual is a normal C-component

The original point-centralizer quotient marking restricts to its perfect
two-residual and passes through the literal ambient embedding. The ambient
normalizer intersected with C_G(t) normalizes the point centralizer and its
characteristic residual. The quasisimple two-core quotient criterion then
makes this residual a normal C-component of that same local intersection.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(3)
and the opening paragraph of the proof of 12.7.5, printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The A5 marking of the actual ambient point residual, induced by the
original point-centralizer quotient and its literal residual inclusion. -/
def tripleSixPointResidualQuotientEquiv (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    (Lt ⧸ pCore 2 Lt) ≃* alternatingGroup (Fin 5) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let R := pResidual 2 C
  let B := R.map C.subtype
  let e := tripleSixPointCentralizerEquiv D a t ht heven
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (C ⧸ pCore 2 C) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let eR : R ≃* solvableResidual C := MulEquiv.subgroupCongr
    (tripleSixPointCentralizerResidual_eq_solvableResidual D a t ht heven)
  let eB : R ≃* B := R.equivMapOfInjective C.subtype C.subtype_injective
  exact ((QuotientGroup.congr _ _ (eB.symm.trans eR)
    (pCore_map_iso 2 (eB.symm.trans eR))).trans
      (solvableResidualPCoreQuotientEquiv 2)).trans e

/-- On an actual residual element, the quotient marking is precisely the
original centralizer marking after the literal residual inclusion. -/
theorem tripleSixPointResidualQuotientEquiv_mk (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (r : pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) :
    tripleSixPointResidualQuotientEquiv D a t ht heven
      (QuotientGroup.mk' _ ⟨r.val, mem_map_of_mem _ r.property⟩) =
        tripleSixPointCentralizerEquiv D a t ht heven (QuotientGroup.mk' _ r.val) := by
  unfold tripleSixPointResidualQuotientEquiv
  let eB := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).equivMapOfInjective
    (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    (K ⊓ centralizer ({(t : G)} : Set G)).subtype_injective
  exact congrArg (fun z => tripleSixPointCentralizerEquiv D a t ht heven
    (QuotientGroup.mk' _ z.val)) (eB.symm_apply_apply r)

/-- The same literal Lt is normal and a C-component in the actual Mt,
and its conjugate span inside Mt is itself. -/
theorem tripleSixPointResidual_component (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    let Mt := normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)
    (Lt.subgroupOf Mt).Normal ∧ (Lt.subgroupOf Mt).IsCComponent ∧
      Nonempty ((Lt ⧸ pCore 2 Lt) ≃* alternatingGroup (Fin 5)) ∧
      conjugateSpanBy Lt Mt = Lt := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let B := (pResidual 2 C).map C.subtype
  let M := normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)
  have hCM : C ≤ M := inf_le_inf K.le_normalizer le_rfl
  have hBM : B ≤ M := (map_subtype_le _).trans hCM
  have hnC : M ≤ normalizer (C : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (centralizer ({(t : G)} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnB : M ≤ normalizer (B : Set G) :=
    hnC.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hnormal : (B.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hnB
  let e := tripleSixPointResidualQuotientEquiv D a t ht heven
  let eBM : B.subgroupOf M ≃* B := subgroupOfEquivOfLe hBM
  let eQ : ((B.subgroupOf M) ⧸ pCore 2 (B.subgroupOf M)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eBM (pCore_map_iso 2 eBM)).trans e
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple ((B.subgroupOf M) ⧸ pCore 2 (B.subgroupOf M)) :=
    IsQuasisimple.of_mulEquiv eQ.symm
  let : Group.IsPerfect B := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect (B.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := eBM.symm.toMonoidHom) eBM.symm.surjective
  have hcomp : (B.subgroupOf M).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
      hnormal.isSubnormal (by
        intro N hN hquot
        let := hN
        let : Group.IsNilpotent ((B.subgroupOf M) ⧸ N) := hquot.isNilpotent
        exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N))
  exact ⟨hnormal, hcomp, ⟨e⟩, le_antisymm (conjugateSpanBy_le le_rfl hnB)
    (le_conjugateSpanBy B M)⟩

end CFSG.Quasithin.Chapter12.Section07
