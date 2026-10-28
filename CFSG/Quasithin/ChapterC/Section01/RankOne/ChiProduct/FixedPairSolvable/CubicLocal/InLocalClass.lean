module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.LocalSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.CubicLocal.Action
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC.GlaubermanNiles
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal
open ChapterB
universe u
/-!
# The cubic local C.1.17 marking

The selected minimal parabolic has a reduced elementary omega module whose
abelian Sylow image is the actual order-three actor.  Its residual commutator
has four elements, so `inLocalClass_of_cubic_four` supplies the literal
natural F₂ marking.  The final equivalence transports that marking through
the original map `B ↪ N`; no equality between the quotient kernel and the
2-core is used.  This is the local C.1.26 input; the ambient C.1.27 lift
still requires a subnormal block over the original full Sylow.
Source: Aschbacher--Smith C.1.17, C.1.26--28, pp.132--134.
-/
variable {G : Type u} [Group G] [Finite G]

theorem selected_inLocalClass
    (_T : Sylow 2 G) (N : Subgroup G) (S : Sylow 2 N)
    (B : Subgroup G) (hBN : B ≤ N)
    (hS : (S : Subgroup N).map N.subtype = B)
    (hSP : IsMinimalParabolicOver S ⊤)
    (hfit : generalizedFitting N = pCore 2 N)
    (hJ : ¬ elementaryAbelianMaxJ (S : Subgroup N) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N))
    (hsolv : Group.IsSolvable (N ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N)))
    (ha : IsMulCommutative ((S : Subgroup N).map
      (QuotientGroup.mk' (centralizer
        (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N))))) :
    InLocalClass (inclusion hBN) := by
  let U : Subgroup N := normalClosure
    (omegaOneCenterAmbient (S : Subgroup N) : Set N)
  have hU : IsPReduced 2 U := by
    dsimp [U]
    exact omegaCenter_normalClosure_reduced S
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let : IsElementaryAbelian 2 U := hU.elementary
  let eS : (S : Subgroup N) →* N := (S : Subgroup N).subtype
  have heV : localV eS = U := by
    rfl
  let C : Subgroup N := localKernel eS
  let q := QuotientGroup.mk' C
  have hJ' : ¬ elementaryAbelianMaxJ (S : Subgroup N) ≤ C := by
    simpa only [C, localKernel, heV, U] using hJ
  have hsolv' : Group.IsSolvable (N ⧸ C) := by
    change Group.IsSolvable (N ⧸ centralizer (U : Set N))
    exact hsolv
  have ha' : IsMulCommutative ((S : Subgroup N).map q) := by
    change IsMulCommutative ((S : Subgroup N).map
      (QuotientGroup.mk' (centralizer (U : Set N))))
    exact ha
  obtain ⟨_, h6, h3, hm⟩ := reduced_abelian_sylow_action S hSP U hU hJ' hsolv' ha'
  have hpc : pCore 2 (N ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hF : generalizedFitting (N ⧸ C) = pResidual 2 (N ⧸ C) :=
    generalizedFitting_eq_residual_of_cubic hpc h3
  let : IsElementaryAbelian 2 (localV eS) := heV ▸ inferInstance
  have hF' : Nat.card (generalizedFitting (LocalStar eS)) = 3 := by
    change Nat.card (generalizedFitting (N ⧸ C)) = 3
    rw [hF]
    exact h3
  have hActor : actorLift eS = pResidual 2 N ⊔ localKernel eS := by
    change (generalizedFitting (N ⧸ C)).comap (QuotientGroup.mk' C) = _
    rw [hF, comap_pResidual_quotient]
  have hmoved : moved eS = ⁅localV eS, pResidual 2 N⁆ := by
    apply Eq.symm
    exact commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans hActor.symm)
      (le_rfl : localKernel eS ≤ centralizer (localV eS : Set N))
      le_normalizer_of_normal
  have hmoved_card : Nat.card (moved eS) = 4 := by
    rw [hmoved, heV]
    exact hm
  have hs : ∃ S' : Sylow 2 N, eS.range = (S' : Subgroup N) ∧
      IsMinimalParabolicOver S' ⊤ := by
    refine ⟨S, ?_, hSP⟩
    exact (S : Subgroup N).range_subtype
  have hlocalS : InLocalClass eS :=
    inLocalClass_of_cubic_four eS (S : Subgroup N).subtype_injective hs hfit hF' hmoved_card
  let j0 : (S : Subgroup N) ≃* (S : Subgroup N).map N.subtype :=
    (S : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective
  let j : (S : Subgroup N) ≃* B := j0.trans (MulEquiv.subgroupCongr hS)
  have hjval (y : (S : Subgroup N)) : (j y : G) = (eS y : G) := by
    change ((j0 y : (S : Subgroup N).map N.subtype) : G) = (eS y : G)
    exact Subgroup.coe_equivMapOfInjective_apply (S : Subgroup N)
      N.subtype N.subtype_injective y
  have hecomp : eS.comp j.symm.toMonoidHom = inclusion hBN := by
    ext x
    change (eS (j.symm x) : G) = (inclusion hBN x : G)
    rw [← hjval]
    exact congrArg (fun z : B => (z : G)) (j.apply_symm_apply x)
  rw [← hecomp]
  exact hlocalS.precomp_equiv j.symm
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal
