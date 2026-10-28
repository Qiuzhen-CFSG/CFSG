module
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.CentralizerBound
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action

/-!
# The center of the marked Rudvalis max6 two-core

The actual max6 word subgroup maps onto S₅ with two-core kernel of order 2¹¹.
Its kernel center has at most two elements. The existing normal abelian seed
places a central element in a 128-point candidate list. Six explicit squares
in the two-core preserve orbital features that reduce this list to two points;
the seed centralizer acts freely on a point, giving the cardinal bound.

This is the small-center model fact used to eliminate the Ru row of
Aschbacher–Smith A.3.14 in source 10.2.9, printed pp.750–751. All permutations
and the five-block quotient are the literal max6 generators.
-/

public section
set_option maxRecDepth 30000
namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.OuterNormalizer Rudvalis.OuterNormalizer.InvarianceCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
open CentralizerCertificate

private def letter : Fin 2 → max6 := ![⟨first,first_mem⟩,⟨second,second_mem⟩]
private def letterMap : Fin 2 → Fin 4060 → Fin 4060 := ![firstMap,secondMap]
private def words : Fin 6 → List (Fin 2) :=
  ![[1],[0,0,0,0,0,1],[0,0,0,0,1,0],[0,0,0,1,0,0],[0,0,1,0,0,0],[0,1,0,1,1,1]]
private def product (w : List (Fin 2)) : max6 := (w.map letter).prod
private def productMap (w : List (Fin 2)) (x : Fin 4060) : Fin 4060 :=
  w.foldr (fun i y => letterMap i y) x
private def coreWord (i : Fin 6) : max6 := product (words i) ^ 2
private def coreMap (i : Fin 6) (x : Fin 4060) : Fin 4060 :=
  productMap (words i) (productMap (words i) x)

private theorem productMap_eq (w : List (Fin 2)) (x : Fin 4060) :
    productMap w x = (product w).val.val x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [productMap,List.foldr_cons,product,List.map_cons,List.prod_cons]
    change letterMap i (productMap w x) = (letter i).val.val ((product w).val.val x)
    rw [ih]
    fin_cases i <;> rfl

private theorem coreMap_eq (i : Fin 6) (x : Fin 4060) :
    coreMap i x = (coreWord i).val.val x := by
  simp only [coreMap,productMap_eq,coreWord,pow_two]
  rfl

private theorem letter_action (i : Fin 2) :
    CoreQuotients.max6FiveAction (letter i) =
      (![CoreQuotients.Max6Blocks.cycle,CoreQuotients.Max6Blocks.transposition] :
        Fin 2 → Equiv.Perm (Fin 5)) i := by
  fin_cases i
  · change CoreQuotients.max6FiveAction ⟨first,first_mem⟩ = _
    have he : (⟨first,first_mem⟩ : max6) =
        ⟨max6Generators.1,subset_closure (Set.mem_insert _ _)⟩ := Subtype.ext first_model_eq
    rw [he,CoreQuotients.max6FiveAction_generator0]
    rfl
  · change CoreQuotients.max6FiveAction ⟨second,second_mem⟩ = _
    have he : (⟨second,second_mem⟩ : max6) =
        ⟨max6Generators.2,subset_closure (Set.mem_insert_of_mem _ rfl)⟩ := Subtype.ext second_model_eq
    rw [he,CoreQuotients.max6FiveAction_generator1]
    rfl

private theorem coreWord_mem (i : Fin 6) : coreWord i ∈ pCore 2 max6 := by
  rw [←CoreQuotients.max6FiveAction_ker]
  apply MonoidHom.mem_ker.mpr
  simp only [coreWord,product,map_pow,map_list_prod,List.map_map,Function.comp_def,letter_action]
  revert i
  decide +kernel

private def coreFeature (i : Fin 6) (x : Fin 4060) : Nat :=
  if coreMap i x = x then 1 else if cachedAdj x (coreMap i x) then 2 else 0

set_option maxRecDepth 30000 in
private theorem candidate_core_features (i : Fin 128)
    (h : ∀ k : Fin 6, coreFeature k (candidate i) = coreFeature k 0) :
    candidate i = 0 ∨ candidate i = 3595 := by
  revert i
  decide +kernel

private theorem centralizer_point_injective :
    Function.Injective (fun g : seedCentralizer => centralizerPerm g 0) := by
  have hf (g : seedCentralizer) (h0 : centralizerPerm g 0 = 0) : g = 1 := by
    have hrel := model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.val.val.property
    have ha (x y : Fin 4060) :
        cachedAdj (centralizerPerm g x) (centralizerPerm g y) ↔ cachedAdj x y :=
      (cachedAdj_iff_adj _ _).trans ((hrel x y).trans (cachedAdj_iff_adj _ _).symm)
    have hw (t : Fin 64) (x : Fin 4060) :
        centralizerPerm g (wordMap t x) = wordMap t (centralizerPerm g x) := by
      have h := mem_centralizer_iff.mp g.property
        (⟨seedWord t,seed_le_max6 (seedWord_mem t)⟩ : max6) (seedWord_mem t)
      have hh := congrArg (fun w : max6 => w.val.val x) h
      change (seedWord t).val (centralizerPerm g x) =
        centralizerPerm g ((seedWord t).val x) at hh
      simpa only [wordMap_eq] using hh.symm
    have hc (x : Fin 4060) : color (centralizerPerm g x) = color x := by
      have hfeat (t : Fin 64) : feature t (centralizerPerm g x) = feature t x := by
        have hfix : wordMap t (centralizerPerm g x) = centralizerPerm g x ↔ wordMap t x = x := by
          rw [←hw]
          exact (centralizerPerm g).injective.eq_iff
        have hadj := ha x (wordMap t x)
        rw [hw] at hadj
        simp only [feature,hfix,hadj]
      simp only [color_recipe,hfeat]
    have hp (ts : List (Fin 64)) (x : Fin 4060) :
        profile ts (centralizerPerm g x) = profile ts x := by
      apply List.map_congr_left
      intro t _
      have hh := ha (wordMap t 0) x
      rw [hw,h0] at hh
      exact decide_eq_decide.mpr hh
    have h1 := separate1 _ (hc 1) (hp separatingWords1 1)
    have h2 := separate2 _ (hc 2) (hp separatingWords2 2)
    have hz (x : Fin 4060) : centralizerPerm g (AlignmentData.involutionPerm x) =
        AlignmentData.involutionPerm (centralizerPerm g x) := by
      have h := congrArg (fun w : Model => w.val x)
        (mem_centralizer_singleton_iff.mp (max6_le_centralizer g.val.property))
      change centralizerPerm g (centralInvolution.val x) =
        centralInvolution.val (centralizerPerm g x) at h
      simpa only [centralInvolution_val] using h
    have he : centralizerPerm g = 1 := by
      apply fix_three_eq_one _ hrel hz
      intro x hx
      have he : x = 0 ∨ x = 1 ∨ x = 2 := by
        have hv : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
        rcases hv with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases he with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact he
  intro g h he
  change centralizerPerm g 0 = centralizerPerm h 0 at he
  have hh : centralizerPerm (g⁻¹*h) 0 = 0 := by
    rw [map_mul,map_inv]
    change (centralizerPerm g).symm (centralizerPerm h 0) = 0
    rw [←he]
    exact (centralizerPerm g).symm_apply_apply 0
  exact inv_mul_eq_one.mp (hf _ hh)


private def centerToSeed (z : center (pCore 2 max6)) : seedCentralizer :=
  ⟨z.val.val,by
    intro n hn
    have hc : n ∈ pCore 2 max6 :=
      (show normalSeed ≤ pCore 2 max6 from le_sSup ⟨inferInstance,normalSeed_isPGroup⟩) hn
    exact congrArg (fun x : pCore 2 max6 => x.val)
      (mem_center_iff.mp z.property ⟨n,hc⟩)⟩

private theorem center_color (z : center (pCore 2 max6)) (x : Fin 4060) :
    color (centralizerPerm (centerToSeed z) x) = color x := by
  let g := centerToSeed z
  have hrel := model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.val.val.property
  have ha (x y : Fin 4060) :
      cachedAdj (centralizerPerm g x) (centralizerPerm g y) ↔ cachedAdj x y :=
    (cachedAdj_iff_adj _ _).trans ((hrel x y).trans (cachedAdj_iff_adj _ _).symm)
  have hw (t : Fin 64) (x : Fin 4060) :
      centralizerPerm g (wordMap t x) = wordMap t (centralizerPerm g x) := by
    have h := mem_centralizer_iff.mp g.property
      (⟨seedWord t,seed_le_max6 (seedWord_mem t)⟩ : max6) (seedWord_mem t)
    have hh := congrArg (fun w : max6 => w.val.val x) h
    change (seedWord t).val (centralizerPerm g x) =
      centralizerPerm g ((seedWord t).val x) at hh
    simpa only [wordMap_eq] using hh.symm
  have hfeat (t : Fin 64) : feature t (centralizerPerm g x) = feature t x := by
    have hfix : wordMap t (centralizerPerm g x) = centralizerPerm g x ↔ wordMap t x = x := by
      rw [←hw]
      exact (centralizerPerm g).injective.eq_iff
    have hadj := ha x (wordMap t x)
    rw [hw] at hadj
    simp only [feature,hfix,hadj]
  change color (centralizerPerm g x) = color x
  simp only [color_recipe,hfeat]

private theorem center_core_feature (z : center (pCore 2 max6))
    (i : Fin 6) (x : Fin 4060) :
    coreFeature i (centralizerPerm (centerToSeed z) x) = coreFeature i x := by
  let g := centerToSeed z
  have hrel := model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.val.val.property
  have ha (x y : Fin 4060) :
      cachedAdj (centralizerPerm g x) (centralizerPerm g y) ↔ cachedAdj x y :=
    (cachedAdj_iff_adj _ _).trans ((hrel x y).trans (cachedAdj_iff_adj _ _).symm)
  have hw (x : Fin 4060) :
      centralizerPerm g (coreMap i x) = coreMap i (centralizerPerm g x) := by
    have h := mem_center_iff.mp z.property (⟨coreWord i,coreWord_mem i⟩ : pCore 2 max6)
    have hh := congrArg (fun w : pCore 2 max6 => w.val.val.val x) h
    change (coreWord i).val.val (centralizerPerm g x) =
      centralizerPerm g ((coreWord i).val.val x) at hh
    simpa only [coreMap_eq] using hh.symm
  have hfix : coreMap i (centralizerPerm g x) = centralizerPerm g x ↔ coreMap i x = x := by
    rw [←hw]
    exact (centralizerPerm g).injective.eq_iff
  have hadj := ha x (coreMap i x)
  rw [hw] at hadj
  change coreFeature i (centralizerPerm g x) = coreFeature i x
  simp only [coreFeature,hfix,hadj]

/-- The center of the actual max6 two-core has at most two elements. -/
theorem max6_core_center_card_le_two : Nat.card (center (pCore 2 max6)) ≤ 2 := by
  have hpoints (z : center (pCore 2 max6)) :
      centralizerPerm (centerToSeed z) 0 = 0 ∨
        centralizerPerm (centerToSeed z) 0 = 3595 := by
    have hdec := candidate_decode _ (center_color z 0)
    have hh := candidate_core_features (candidateInverse (centralizerPerm (centerToSeed z) 0))
      (fun i => by rw [hdec]; exact center_core_feature z i 0)
    rwa [hdec] at hh
  let f : center (pCore 2 max6) → ({0,3595} : Finset (Fin 4060)) := fun z =>
    ⟨centralizerPerm (centerToSeed z) 0,by simpa using hpoints z⟩
  have hf : Function.Injective f := by
    intro z w he
    have hp := congrArg Subtype.val he
    have hg := centralizer_point_injective hp
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : seedCentralizer => g.val) hg
  have hb := Nat.card_le_card_of_injective f hf
  have hc : Nat.card ({0,3595} : Finset (Fin 4060)) = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    decide
  rwa [hc] at hb

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
