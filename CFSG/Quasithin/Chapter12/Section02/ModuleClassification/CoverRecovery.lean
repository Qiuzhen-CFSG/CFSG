module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison
public import Theory.Representation.HexacodeAction.CoverRecognition
public import Theory.Representation.HexacodeAction.ReducedCover
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.CoveringPGroupDescent
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Recovering the original actors in the binary rows

The literal projection from L/O2(L) is a perfect central cover. The known
binary SL3, SL4, SL5 and derived G2 cover calculations kill its kernel.
For the triple-six row the actual center and quotient marking first produce
a commuting identification with HexEvenAutomorphisms; the reduced-cover
theorem then proves injectivity of the original projection.
Source: Aschbacher--Smith A.3.5, I.1.1--4 and 12.2.2, pp.43,407--408,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

include c in
theorem nontrivial : Nontrivial K := by
  by_contra hn
  let : Subsingleton K := not_nontrivial_iff_subsingleton.mp hn
  apply c.irrPlus.not_le_fixedSpace ρ
  intro v _ k
  have hk : k = 1 := Subsingleton.elim _ _
  rw [hk]
  simp

@[expose] noncomputable def modelCover (hq : IsQuasisimple (L ⧸ pCore 2 L))
    {J : Type*} [Group J] (e : K ≃* J) :
    PerfectCentralCovering.Cover (L ⧸ pCore 2 L) J := by
  let := hq
  let := c.nontrivial
  refine ⟨e.toMonoidHom.comp c.projection,e.surjective.comp c.surjective,inferInstance,?_⟩
  intro q hq
  have hz : c.projection q = 1 := e.injective (hq.trans e.map_one.symm)
  rw [← IsQuasisimple.comap_center_of_surjective c.projection c.surjective]
  change c.projection q ∈ center K
  rw [hz]
  exact one_mem _

/-- The binary SL3 covering theorem recovers the given projection, not just
an abstract central-quotient isomorphism. -/
theorem projection_injective_of_linearThree
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Function.Injective c.projection := by
  let E := Matrix.PSL3Two.centralCoverEquiv (c.modelCover hq e)
    (pCore_quotient_pCore_eq_bot 2)
  intro a b hab
  apply E.injective
  change Matrix.PSL3Two.centralCoverEquiv _ _ a = Matrix.PSL3Two.centralCoverEquiv _ _ b
  rw [Matrix.PSL3Two.centralCoverEquiv_apply,Matrix.PSL3Two.centralCoverEquiv_apply]
  exact congrArg e hab

/-- The binary degree-four and degree-five cover calculations remove the
kernel of the literal original action map. -/
theorem projection_injective_of_binaryLinear
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    Function.Injective c.projection := by
  rcases hd with rfl | rfl
  · let p := Atlas.Order20160A8.sl4TwoEquivPSL
    let f := c.modelCover hq (e.trans p)
    let S := Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple S := IsQuasisimple.of_mulEquiv
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm
    let U := universalQuasisimpleCover S
    let m := Matrix.PSL4Two.kernelEquivTwo (ZMod 2) (by simp) (MulEquiv.refl S) U
      (universalQuasisimpleCover_isUniversal S)
    have hm : IsPGroup 2 U.toMonoidHom.ker := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_congr m.toEquiv]; simp)
    have hf := (universalQuasisimpleCover_isUniversal S).injective_of_pGroup_kernel
      hm f.toCovering (pCore_quotient_pCore_eq_bot 2)
    intro a b hab
    apply hf
    exact congrArg (e.trans p) hab
  · let p := Theory.SpecificGroups.PSL5Two.UniversalCover.projectiveEquivSL.symm
    let f := c.modelCover hq (e.trans p)
    have hf := f.injective_of_universalProjection_ker_eq_bot
      Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot
    intro a b hab
    apply hf
    exact congrArg (e.trans p) hab

theorem projection_injective_of_binaryDerivedG2
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Function.Injective c.projection := by
  let f := c.modelCover hq e
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  have hf : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    rw [← pCore_quotient_pCore_eq_bot 2]
    exact le_sSup ⟨inferInstance,hk⟩
  intro x y he
  exact hf (congrArg e he)

/-- The actual triple-cover row supplies the concrete hexacode marking and
its commuting quotient triangle on the original L/O2(L). -/
theorem tripleSix_marking [Finite H]
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (a : TripleSixAction s.action K) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      (∀ q, Atlas.Codes.hexEvenCoordinate (e q) =
        a.quotientEquiv (QuotientGroup.mk' (center K) (c.projection q))) ∧
      Function.Injective c.projection := by
  let := hq
  let := c.nontrivial
  let : IsQuasisimple K := IsQuasisimple.of_surjective c.projection c.surjective
  let f := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : f.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective).trans (QuotientGroup.ker_mk' _)
  have hcard : Nat.card f.ker = 3 := by
    rw [hk,Nat.card_congr a.centerEquiv.toEquiv]
    simp
  obtain ⟨j,hj⟩ := Hexacode.triple_cover_equiv f
    (a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le hcard
  let p := j.toMonoidHom.comp c.projection
  have hp : Function.Injective p := Hexacode.injective_of_surjective_of_twoCore_eq_bot
    (pCore_quotient_pCore_eq_bot 2) p (j.surjective.comp c.surjective)
  refine ⟨MulEquiv.ofBijective p ⟨hp,j.surjective.comp c.surjective⟩,?_,?_⟩
  · intro q
    exact DFunLike.congr_fun hj (c.projection q)
  · intro x y he
    exact hp (congrArg j he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
