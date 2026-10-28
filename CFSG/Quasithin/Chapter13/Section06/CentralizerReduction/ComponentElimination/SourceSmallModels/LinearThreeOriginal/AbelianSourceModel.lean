module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Block
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels

/-!
# The abelian binary MS core in the original linear-three branch

The genuine binary MS hypotheses make an abelian commutator core elementary
and identify its quotient by the component centralizer with one or two natural
SL₃(2) modules. The intrinsic component core centralizes this commutator core,
so it equals the literal source subgroup U=[Z(O₂(K)),K]. We transport the
actual quotient maps to ambient U, retaining a common quotient actor on both
copies. The same centrality proves the checked-center commutator identity.

The proof uses the natural-quotient recognition underlying the abelian
block-or-double theorem, preserving the original binary field coordinates.
It does not require the nonabelian alternatives of C.1.34.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34,
printed pp.136–137, and 13.6.22, printed pp.932–933.
-/

@[expose] public section

open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open BinaryMS MSSourceModels
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {K R : Subgroup J}

private def doubledAction : BinaryLinearThree.Group →*
    MulAut (Multiplicative (BinaryMS.AbelianNaturalVector × BinaryMS.AbelianNaturalVector)) where
  toFun g := ((Matrix.SpecialLinearGroup.toLin' g).prodCongr
    (Matrix.SpecialLinearGroup.toLin' g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    apply Prod.ext <;>
      change Matrix.SpecialLinearGroup.toLin' (1 : BinaryLinearThree.Group) _ = _ <;>
      rw [map_one] <;> rfl
  map_mul' g h := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    apply Prod.ext <;>
      change Matrix.SpecialLinearGroup.toLin' (g*h) _ =
        Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' h _) <;>
      rw [map_mul] <;> rfl

private noncomputable def doubleCoordinates :
    Multiplicative (Fin 2 → BinaryMS.AbelianNaturalVector) ≃*
      Multiplicative (BinaryMS.AbelianNaturalVector × BinaryMS.AbelianNaturalVector) :=
  (LinearEquiv.finTwoArrow (ZMod 2) BinaryMS.AbelianNaturalVector).toAddEquiv.toMultiplicative

private noncomputable def doubledBlockModel (h : Input κ K R)
    (q : AbelianCore.NaturalQuotient h 2) : BlockModuleModel K doubledAction where
  quotientIso := q.quotientEquiv
  moduleIso := q.intrinsicModuleEquiv.trans doubleCoordinates
  intertwining l x := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact q.intrinsicProjection_conjugate l x 0
    · exact q.intrinsicProjection_conjugate l x 1

private theorem component_twoPerfect (h : Input κ K R) : IsPPerfect 2 K := by
  let := h.component.perfect
  intro N hn hq
  let := hn
  have hs : Subsingleton (K ⧸ N) := by
    by_contra! hnt
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hq.isNilpotent
  apply eq_top_iff.mpr
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

private theorem blockU_central_of_naturalQuotient (h : Input κ K R)
    (hc : IsMulCommutative (commutatorCore K)) {m : ℕ}
    (q : AbelianCore.NaturalQuotient h m) :
    blockU K ≤ centralizer (pCore 2 K : Set K) := by
  intro x hx y hy
  apply Subtype.ext
  exact (h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q)
    (h.intrinsicCoreEquiv ⟨x,hx⟩).property y (mem_map_of_mem K.subtype hy)

/-- The source center commutator is the actual ambient MS core. -/
theorem abelian_sourceU_eq_core (h : Input κ K R)
    (hc : IsMulCommutative (commutatorCore K)) :
    sourceU K = commutatorCore K := by
  obtain ⟨m, _, ⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  exact (sourceU_eq_of_central K (component_twoPerfect h)
    (blockU_central_of_naturalQuotient h hc q)).trans h.commutatorCore_eq_internal.symm

/-- The source subgroup is elementary even in the doubled module branch. -/
theorem abelian_sourceU_elementary (h : Input κ K R)
    (hc : IsMulCommutative (commutatorCore K)) :
    IsElementaryAbelian 2 (sourceU K) := by
  rw [abelian_sourceU_eq_core h hc]
  obtain ⟨m, _, ⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  exact h.abelianCore_elementary_of_naturalQuotient hc q

/-- The actual checked quotient map gives the source commutator identity. -/
theorem abelian_sourceZ0_commutator (h : Input κ K R)
    (hc : IsMulCommutative (commutatorCore K))
    (v : J) (hK : K ≤ Gv v) (hv : v ^ 2 = 1) :
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  obtain ⟨m, _, ⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  exact sourceZ0_commutator_of_central K v hK hv (component_twoPerfect h)
    (blockU_central_of_naturalQuotient h hc q)

/-- The abelian MS branch supplies the natural or doubled quotient model on
literal ambient U, with its intrinsic two-core quotient actor retained. -/
theorem abelian_source_models (h : Input κ K R)
    (hc : IsMulCommutative (commutatorCore K)) :
    ∃ e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
        m.actor = linearThreeActor e) ∨
      (∃ m : ConjugationQuotientModel K (sourceU K)
          (BinaryLinearThree.W.prod BinaryLinearThree.W),
        m.actor = linearThreeActor e) := by
  obtain ⟨m, hm, ⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  rw [sourceU_eq_of_central K (component_twoPerfect h)
    (blockU_central_of_naturalQuotient h hc q)]
  rcases hm with rfl | rfl
  · obtain ⟨r, ⟨b⟩, hr⟩ := q.block_model
    exact ⟨b.quotientIso, Or.inl ⟨of_block_model K BinaryLinearThree.W r b hr, rfl⟩⟩
  · refine ⟨q.quotientEquiv, Or.inr ?_⟩
    exact ⟨of_block_model K (BinaryLinearThree.W.prod BinaryLinearThree.W)
      doubledAction (doubledBlockModel h q) (fun _ _ => rfl), rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
