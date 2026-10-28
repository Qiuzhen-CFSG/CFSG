module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsFirst

/-!
# The first terminal residual's original four-letter action

The full support-block preimage maps onto S₄. Its prime-to-three residual
therefore maps onto A₄. The complementary action is trivial, so the
kernel of this four-letter projection embeds in the original O₂(L),
using the central-cover reduction. This retains the literal first block
and supplies the normal-subgroup comparison used to identify L₁ inside K.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)
theorem firstPointResidual_le_pointNormalizer : P.firstPointResidual ≤ P.pointNormalizer :=
  (map_subtype_le _).trans (map_subtype_le _)

theorem firstPointResidual_le_Le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.firstPointResidual ≤ P.Le := by
  rw [P.Le_eq_pointResidual_sup structural escape C]
  exact le_sup_left

def firstFactorPermutation : P.firstPointFactor →* Equiv.Perm (Fin 4) :=
   ((MonoidHom.fst _ _).comp P.pointBlockAction).comp (inclusion (map_subtype_le _))

theorem firstFactorPermutation_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : Function.Surjective P.firstFactorPermutation := by
  intro a
  obtain ⟨n, hn⟩ := P.pointBlockAction_surjective structural escape (a,1)
  refine ⟨⟨n,?_⟩,congrArg Prod.fst hn⟩
  exact mem_map_of_mem P.pointNormalizer.subtype (show n ∈
    (((⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥).comap P.pointBlockAction) by
    change _ ∧ (P.pointBlockAction n).2 = 1
    exact ⟨mem_top _,congrArg Prod.snd hn⟩)

private theorem permFour_primeToResidual : primeToResidual 3 (Equiv.Perm (Fin 4)) =
    alternatingGroup (Fin 4) := by
  apply le_antisymm
  · apply primeToResidual_le
    rw [alternatingGroup.index_eq_two]
    decide
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating,closure_le]
    intro g hg
    exact mem_primeToResidual_of_pow (n := 1) (by
      simpa only [pow_one,Equiv.Perm.IsThreeCycle.orderOf hg] using pow_orderOf_eq_one g)

theorem firstFactorPermutation_residual_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (primeToResidual 3 P.firstPointFactor).map P.firstFactorPermutation =
      alternatingGroup (Fin 4) := by
  rw [map_primeToResidual_of_surjective 3 _
    (P.firstFactorPermutation_surjective structural escape),permFour_primeToResidual]

def firstResidualPermutation : P.firstPointResidual →* Equiv.Perm (Fin 4) :=
   ((MonoidHom.fst _ _).comp P.pointBlockAction).comp
     (inclusion P.firstPointResidual_le_pointNormalizer)

theorem firstResidualPermutation_mem
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (r : P.firstPointResidual) :
    P.firstResidualPermutation r ∈ alternatingGroup (Fin 4) := by
  obtain ⟨x,hx,he⟩ := r.property
  have hm := mem_map_of_mem P.firstFactorPermutation hx
  rw [P.firstFactorPermutation_residual_image structural escape] at hm
  have he' : inclusion P.firstPointResidual_le_pointNormalizer r =
      inclusion (map_subtype_le _) x := Subtype.ext he.symm
  change (P.pointBlockAction (inclusion P.firstPointResidual_le_pointNormalizer r)).1 ∈ _
  rw [he']
  exact hm

def firstResidualProjection
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : P.firstPointResidual →* alternatingGroup (Fin 4) :=
  P.firstResidualPermutation.codRestrict _ (P.firstResidualPermutation_mem structural escape)

theorem firstResidualProjection_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    Function.Surjective (P.firstResidualProjection structural escape) := by
  intro a
  have ha := a.property
  simp only [← P.firstFactorPermutation_residual_image structural escape] at ha
  obtain ⟨x,hx,he⟩ := ha
  refine ⟨⟨x,mem_map_of_mem P.firstPointFactor.subtype hx⟩,Subtype.ext he⟩

theorem firstResidual_second_eq_one (r : P.firstPointResidual) :
    (P.pointBlockAction (inclusion P.firstPointResidual_le_pointNormalizer r)).2 = 1 := by
  have hrF : (r : G) ∈ P.firstPointFactor := map_subtype_le _ r.property
  obtain ⟨n,hn,he⟩ := hrF
  have he' : inclusion P.firstPointResidual_le_pointNormalizer r = n := Subtype.ext he.symm
  rw [he']
  exact hn.2

theorem firstResidualProjection_twoKernel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.firstResidualProjection structural escape).ker := by
  let f := P.firstResidualProjection structural escape
  have hRL : P.firstPointResidual ≤ L :=
    (P.firstPointResidual_le_Le structural escape C).trans ((map_subtype_le _).trans inf_le_left)
  have hπ (r : f.ker) : S.projection (inclusion hRL r.val) = 1 := by
    let n := inclusion P.firstPointResidual_le_pointNormalizer r.val
    have hn : P.pointBlockAction n = 1 := Prod.ext (congrArg Subtype.val r.property)
      (P.firstResidual_second_eq_one r.val)
    have hn' : D.model.pointPermutation P.point n = 1 :=
      (WeightFourLocal.pointEquiv _ P.weight_four).injective (hn.trans (map_one _).symm)
    have hperm : D.model.permutation ⟨n,n.property.1⟩ = 1 := congrArg Subtype.val hn'
    have he := D.component_action (inclusion hRL r.val)
    have hp : (S.projection (inclusion hRL r.val)).val = 1 := he.symm.trans hperm
    exact Subtype.ext hp
  let j : f.ker →* pCore 2 L := ((inclusion hRL).comp f.ker.subtype).codRestrict _
    (fun r => (QuotientGroup.eq_one_iff _).mp
      ((P.twoCoreQuotientEquiv C).injective ((hπ r).trans (map_one _).symm)))
  exact pCore_isPGroup.of_injective j (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => ((x : L) : G)) h)


end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
