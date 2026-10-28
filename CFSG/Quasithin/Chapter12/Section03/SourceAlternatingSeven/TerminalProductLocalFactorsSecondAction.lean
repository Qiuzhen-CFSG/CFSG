module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsFirst

/-!
# The literal three-letter quotient of the second block residual

The three-letter action of the full second block preimage is onto S₃.
Its prime-to-three residual therefore maps onto A₃. The first block acts
trivially, so a kernel element also lies in the kernel of the original
L-to-A₇ projection. The proved cover reduction makes that kernel a
two-group. Conversely every normal two-subgroup has trivial A₃ image,
identifying the kernel with the residual's own two-core.

The quotient equivalence retains the original block permutation map.
Identifying this residual with the published L₂ remains the source
intersection calculation owned by qt-d-1231-terminal-product.
ComponentAnalysis is discharged by qt-d-1231-terminal.
Source: Aschbacher--Smith, paragraphs around 12.3.13, pp.811--812.
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
 theorem secondPointResidual_le_pointNormalizer : P.secondPointResidual ≤ P.pointNormalizer :=
  (map_subtype_le _).trans (map_subtype_le _)

theorem secondPointResidual_le_Le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.secondPointResidual ≤ P.Le := by
  rw [P.Le_eq_pointResidual_sup structural escape C]
  exact le_sup_right

def secondFactorPermutation : P.secondPointFactor →* Equiv.Perm (Fin 3) :=
   ((MonoidHom.snd _ _).comp P.pointBlockAction).comp (inclusion (map_subtype_le _))

theorem secondFactorPermutation_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : Function.Surjective P.secondFactorPermutation := by
  intro a
  obtain ⟨n, hn⟩ := P.pointBlockAction_surjective structural escape (1,a)
  refine ⟨⟨n,?_⟩,congrArg Prod.snd hn⟩
  exact mem_map_of_mem P.pointNormalizer.subtype (show n ∈
    (((⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤).comap P.pointBlockAction) by
    change (P.pointBlockAction n).1 = 1 ∧ _
    exact ⟨congrArg Prod.fst hn,mem_top _⟩)

private theorem permThree_primeToResidual : primeToResidual 3 (Equiv.Perm (Fin 3)) =
    alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply primeToResidual_le
    rw [alternatingGroup.index_eq_two]
    decide
  · apply le_primeToResidual_of_isPGroup
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide

theorem secondFactorPermutation_residual_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (primeToResidual 3 P.secondPointFactor).map P.secondFactorPermutation =
      alternatingGroup (Fin 3) := by
  rw [map_primeToResidual_of_surjective 3 _
    (P.secondFactorPermutation_surjective structural escape),permThree_primeToResidual]

def secondResidualPermutation : P.secondPointResidual →* Equiv.Perm (Fin 3) :=
   ((MonoidHom.snd _ _).comp P.pointBlockAction).comp
     (inclusion P.secondPointResidual_le_pointNormalizer)

theorem secondResidualPermutation_mem
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (r : P.secondPointResidual) :
    P.secondResidualPermutation r ∈ alternatingGroup (Fin 3) := by
  obtain ⟨x,hx,he⟩ := r.property
  have hm := mem_map_of_mem P.secondFactorPermutation hx
  rw [P.secondFactorPermutation_residual_image structural escape] at hm
  have he' : inclusion P.secondPointResidual_le_pointNormalizer r =
      inclusion (map_subtype_le _) x := Subtype.ext he.symm
  change (P.pointBlockAction (inclusion P.secondPointResidual_le_pointNormalizer r)).2 ∈ _
  rw [he']
  exact hm

def secondResidualProjection
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : P.secondPointResidual →* alternatingGroup (Fin 3) :=
  P.secondResidualPermutation.codRestrict _ (P.secondResidualPermutation_mem structural escape)

theorem secondResidualProjection_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    Function.Surjective (P.secondResidualProjection structural escape) := by
  intro a
  have ha := a.property
  simp only [← P.secondFactorPermutation_residual_image structural escape] at ha
  obtain ⟨x,hx,he⟩ := ha
  refine ⟨⟨x,mem_map_of_mem P.secondPointFactor.subtype hx⟩,Subtype.ext he⟩

theorem secondResidual_first_eq_one (r : P.secondPointResidual) :
    (P.pointBlockAction (inclusion P.secondPointResidual_le_pointNormalizer r)).1 = 1 := by
  have hrF : (r : G) ∈ P.secondPointFactor := map_subtype_le _ r.property
  obtain ⟨n,hn,he⟩ := hrF
  have he' : inclusion P.secondPointResidual_le_pointNormalizer r = n := Subtype.ext he.symm
  rw [he']
  exact hn.1

theorem secondResidualProjection_twoKernel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.secondResidualProjection structural escape).ker := by
  let f := P.secondResidualProjection structural escape
  have hRL : P.secondPointResidual ≤ L :=
    (P.secondPointResidual_le_Le structural escape C).trans ((map_subtype_le _).trans inf_le_left)
  have hπ (r : f.ker) : S.projection (inclusion hRL r.val) = 1 := by
    let n := inclusion P.secondPointResidual_le_pointNormalizer r.val
    have hn : P.pointBlockAction n = 1 := Prod.ext (P.secondResidual_first_eq_one r.val)
      (congrArg Subtype.val r.property)
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

theorem secondResidualProjection_ker
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.secondResidualProjection structural escape).ker = pCore 2 P.secondPointResidual := by
  let f := P.secondResidualProjection structural escape
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,P.secondResidualProjection_twoKernel structural escape C⟩
  intro x hx
  have hp : IsPGroup 2 ((pCore 2 P.secondPointResidual).map f) := pCore_isPGroup.map f
  have hx' : f x ∈ (pCore 2 P.secondPointResidual).map f := mem_map_of_mem f hx
  have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨f x,hx'⟩
  have ho : orderOf (f x) ∣ 3 := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
    simpa only [hcard] using orderOf_dvd_natCard (f x)
  have hc' : Nat.Coprime (orderOf (f x)) 3 := by
    rw [← orderOf_injective _ ((pCore 2 P.secondPointResidual).map f).subtype_injective] at hc
    exact hc
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl ho)

def secondResidualQuotientEquiv
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.secondPointResidual ⧸ pCore 2 P.secondPointResidual) ≃* alternatingGroup (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (P.secondResidualProjection_ker structural escape C).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (P.secondResidualProjection_surjective structural escape))

theorem secondResidualQuotientEquiv_apply
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) (r : P.secondPointResidual) :
    P.secondResidualQuotientEquiv structural escape C (QuotientGroup.mk' _ r) =
      P.secondResidualProjection structural escape r := rfl

theorem secondResidual_fixes_support (r : P.secondPointResidual)
    (i : WeightFourLocal.Support (D.model.coordinates P.point).toAdd) :
    D.model.permutation (inclusion inf_le_left
      (inclusion P.secondPointResidual_le_pointNormalizer r)) i = i := by
  have he := P.pointBlockAction_first (inclusion P.secondPointResidual_le_pointNormalizer r) i
  rw [P.secondResidual_first_eq_one] at he
  exact congrArg Subtype.val ((WeightFourLocal.fourLetters _ P.weight_four).injective he).symm


end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
