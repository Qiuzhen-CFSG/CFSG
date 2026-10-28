module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.RadicalImage.Action

/-! Lift the point-local core calculation through the literal outer action.
Source: Aschbacher--Smith 11.5.7, printed pp.781--782. -/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (a : SL(3, E.input.field.Carrier))

def image (A : Subgroup G) : Subgroup (MulAut PSL(3, E.input.field.Carrier)) :=
  (A.subgroupOf (L ⊔ (T : Subgroup G))).map (projectiveAction E m a)

theorem image_normalizes (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    image E m a B ≤ normalizer (image E m a A : Set _) :=
  (map_mono ((comap_mono hn).trans (A.le_normalizer_comap _))).trans (le_normalizer_map _)

theorem core_image_le (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    image E m a (A.pCoreIn 2) ≤ (image E m a A).pCoreIn 2 := by
  let B := A.subgroupOf (L ⊔ (T : Subgroup G))
  let f := (projectiveAction E m a).subgroupMap B
  have hn : ((pCore 2 B).map f).Normal :=
    Normal.map inferInstance f ((projectiveAction E m a).subgroupMap_surjective B)
  have h : (pCore 2 B).map f ≤ pCore 2 (image E m a A) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hh := map_mono (f := (image E m a A).subtype) h
  change ((pCore 2 B).map f).map (B.map (projectiveAction E m a)).subtype ≤
    (B.map (projectiveAction E m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((projectiveAction E m a).comp B.subtype) ≤ _ at hh
  rw [← Subgroup.map_map] at hh
  change ((A.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map _ ≤ _
  rwa [← pCoreIn_subgroupOf 2 A (L ⊔ (T : Subgroup G)) hA]

private theorem coreQuotient_center_eq_bot (n : NaturalPair E) :
    center (E.K ⧸ pCore 2 E.K) = ⊥ := by
  apply (center _).eq_bot_iff_forall.mpr
  intro z hz
  apply n.actor.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot]
  apply mem_center_iff.mpr
  intro b
  obtain ⟨c,rfl⟩ := n.actor.surjective b
  simpa only [map_mul] using congrArg n.actor (mem_center_iff.mp hz c)

/-- The scalar projective kernel on K is a two-group, because K/O₂(K)
is centerless. No centerlessness of the full SL₃ quotient is used. -/
theorem component_kernel_le_core (n : NaturalPair E) (hKL : E.K ≤ L)
    (k : E.K) (hk : projectiveAction E m a (inclusion (hKL.trans le_sup_left) k) = 1) :
    k ∈ pCore 2 E.K := by
  have hc := projectiveAction_kernel_centralizes E m a _ hk
  apply (QuotientGroup.eq_one_iff k).mp
  apply mem_bot.mp
  rw [← coreQuotient_center_eq_bot E n]
  apply mem_center_iff.mpr
  intro x
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) x
  have hcomm : ⁅k,j⁆ ∈ pCore 2 E.K := by
    have ha : (⁅k,j⁆ : E.K).val ∈ E.K.pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 hKL
        ⟨(⁅k,j⁆ : E.K).property,coreQuotientCentralizer_commutator hc (hKL j.property)⟩
    obtain ⟨u,hu,he⟩ := ha
    exact (Subtype.ext he : u = ⁅k,j⁆) ▸ hu
  have he := (QuotientGroup.eq_one_iff (N := pCore 2 E.K) ⁅k,j⁆).mpr hcomm
  change QuotientGroup.mk' (pCore 2 E.K) ⁅k,j⁆ = 1 at he
  rw [map_commutatorElement] at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- The original W=O₂(K) maps onto the full core of the actual projective K image. -/
theorem closure_image_core (n : NaturalPair E) (hKL : E.K ≤ L)
    (hWK : E.W = E.K.pCoreIn 2) :
    image E m a E.W = (image E m a E.K).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := E.K.subgroupOf M
  let f := (projectiveAction E m a).subgroupMap B
  have hk : f.ker ≤ pCore 2 B := by
    let e : B ≃* E.K := subgroupOfEquivOfLe (hKL.trans le_sup_left)
    rw [← pCore_map_iso 2 e.symm]
    intro x hx
    refine ⟨e x,component_kernel_le_core E m a n hKL (e x) ?_,?_⟩
    · exact congrArg Subtype.val hx
    · exact e.symm_apply_apply x
  have he := f.comap_pCore_of_ker_isPGroup
    ((projectiveAction E m a).subgroupMap_surjective B) (pCore_isPGroup.to_le hk)
  have hm : (pCore 2 B).map f = pCore 2 (image E m a E.K) := by
    rw [← he,map_comap_eq_self_of_surjective ((projectiveAction E m a).subgroupMap_surjective B)]
    rfl
  have hh := congrArg (Subgroup.map (image E m a E.K).subtype) hm
  change ((pCore 2 B).map f).map (B.map (projectiveAction E m a)).subtype =
    (B.map (projectiveAction E m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((projectiveAction E m a).comp B.subtype) = _ at hh
  rw [← Subgroup.map_map] at hh
  change ((E.W.subgroupOf M).map (projectiveAction E m a)) = _
  rw [hWK, ← pCoreIn_subgroupOf 2 E.K M (hKL.trans le_sup_left)]
  exact hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
