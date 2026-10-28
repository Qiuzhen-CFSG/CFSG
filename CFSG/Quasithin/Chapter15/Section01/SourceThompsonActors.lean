module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonMovement
public import CFSG.Quasithin.ChapterD.Section02.RankDeficit
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The actual chosen Thompson actors

B.2.4 is applied inside the original selected subgroup, with the kernel of
its literal conjugation map identified with the actual module centralizer.
The subgroup-of carrier equivalence transports the fixed codimension to
Aut_M(V). Quadratic and cubic ratio two then make every nontrivial Thompson
actor of rank at most two an order-two starred actor.

Source: Aschbacher--Smith 15.1.13(3), printed p.1091. The classified action
rank bound and the nonexceptional cubic ratio are retained explicitly, so the
proper chosen module is never replaced by the full local module.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped ENNReal IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

theorem chosen_thompson_actor_codimension_bound
    (T M V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hTM : T ≤ M) (hVM : V ≤ T) (hn : M ≤ normalizer (V : Set G))
    (hA : A ∈ ChapterB.thompsonFamily T 1)
    (hne : (A.subgroupOf M).map (actionHom M V hn).rangeRestrict ≠ ⊥) :
    fixedCodim (imageRepresentation M V hn)
      ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) ≤
        rank ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) + 1 := by
  let U := V.subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (hVM.trans hTM)
  let f := (actionHom M V hn).rangeRestrict
  have hAM : A ≤ M := hA.1.trans hTM
  have hAi : A.subgroupOf M ∈ ChapterB.thompsonFamily (T.subgroupOf M) 1 := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective M.subtype M.subtype_injective _ _ 1).mp
    simpa only [map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le hTM] using hA
  let : IsElementaryAbelian 2 (A.subgroupOf M) := hAi.2.1
  have hker : f.ker = centralizer (U : Set M) := by
    change (actionHom M V hn).rangeRestrict.ker = centralizer (U : Set M)
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext m
    constructor
    · intro h u hu
      apply Subtype.ext
      exact h u hu
    · intro h v hv
      exact congrArg M.subtype (h ⟨v,(hVM.trans hTM) hv⟩ hv)
  have hAj := (ChapterB.mem_thompsonFamily_iff_rank _ _ _).mp hAi
  have hb := ChapterB.lemma_B_2_4_1 (T.subgroupOf M) U (A.subgroupOf M)
    (subgroupOf_mono M hVM) hAi.1 1 (by
      change Nat.log 2 (Nat.card (A.subgroupOf M)) = ChapterB.twoRank (T.subgroupOf M) - 1
      omega) f hker hne
  let x : Additive U ≃ₗ[ZMod 2] Additive V :=
    { (subgroupOfEquivOfLe (hVM.trans hTM)).toAdditive with
      map_smul' := ZMod.map_smul (subgroupOfEquivOfLe (hVM.trans hTM)).toAdditive }
  have hx : ∀ g v, x (normalRepresentation U g v) = imageRepresentation M V hn (f g) (x v) :=
    fun _ _ => rfl
  have hc := fixedCodim_map_equivariant (normalRepresentation U)
    (imageRepresentation M V hn) f x hx (A.subgroupOf M)
  rw [normalRepresentation_fixedCodim_eq_rank_difference] at hc
  change fixedCodim (imageRepresentation M V hn) ((A.subgroupOf M).map f) ≤
    Nat.log 2 (Nat.card ((A.subgroupOf M).map f)) + 1
  omega
theorem chosen_sylow_thompson_actors
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    (hq : quadraticRatio (imageRepresentation M V hn) = 2)
    (hhat : cubicRatio (imageRepresentation M V hn) = 2)
    (hrank : ∀ E : Subgroup (internalActionImage M V hn), IsElementaryTwo E → rank E ≤ 2) :
    ∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
      B ≠ ⊥ → Nat.card B = 2 ∧ rank B = 1 ∧
        fixedCodim (imageRepresentation M V hn) B = 2 ∧
        B ∈ QhatStar (imageRepresentation M V hn) := by
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hn
  let := IsElementaryAbelian.subgroupOf hVM (p := 2)
  have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal (T.subtype hTM)
  have hVT : V ≤ (T : Subgroup G) := by
    simpa only [map_subgroupOf_eq_of_le hVM,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  intro A hA B hB
  let := hA.2.1
  let := IsElementaryAbelian.subgroupOf (hA.1.trans hTM) (p := 2)
  have he : IsElementaryTwo B := ⟨hB,IsElementaryAbelian.map _⟩
  exact rank_one_starred_of_rank_deficit _ hq hhat he (hrank B he)
    (chosen_thompson_actor_codimension_bound _ _ _ _ hTM hVT hn hA hB)

theorem chosen_thompson_image_ne_bot
    (T M V : Subgroup G) (hTM : T ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ T 1⁆ ≠ ⊥) :
    ((ChapterB.thompsonJ T 1).subgroupOf M).map (actionHom M V hn).rangeRestrict ≠ ⊥ := by
  intro he
  have hk := (Subgroup.map_eq_bot_iff _).mp he
  have hc : ChapterB.thompsonJ T 1 ≤ centralizer (V : Set G) := by
    intro j hj
    have hmj : j ∈ M := hTM (ChapterB.thompsonJ_le _ _ hj)
    have hh := hk (show (⟨j,hmj⟩ : M) ∈ (ChapterB.thompsonJ T 1).subgroupOf M from hj)
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker] at hh
    exact hh
  exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hc))

theorem chosen_thompson_image_le_Jhat
    (T M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hTM : T ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hstar : ∀ A ∈ ChapterB.thompsonFamily T 1,
      let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
      B ≠ ⊥ → B ∈ QhatStar (imageRepresentation M V hn)) :
    ((ChapterB.thompsonJ T 1).subgroupOf M).map (actionHom M V hn).rangeRestrict ≤
      (T.subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn) := by
  let f := (actionHom M V hn).rangeRestrict
  let K := Jhat (imageRepresentation M V hn)
  have hj : ChapterB.thompsonJ T 1 ≤ (K.comap f).map M.subtype := by
    apply sSup_le
    intro A hA a ha
    have hB : (A.subgroupOf M).map f ≤ K := by
      by_cases he : (A.subgroupOf M).map f = ⊥
      · rw [he]; exact bot_le
      · exact le_sSup (hstar A hA he)
    exact ⟨⟨a,hTM (hA.1 ha)⟩,hB (mem_map_of_mem f ha),rfl⟩
  refine le_inf (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le T 1))) ?_
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨x,hx,hxg⟩ := hj hg
  have he : x = g := Subtype.ext hxg
  change f g ∈ K
  change f x ∈ K at hx
  rwa [he] at hx

theorem PreparedChosenModule.thompson_actors
    (T : Sylow 2 G) {M V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V)
    (hhat : letI := h.elementary; cubicRatio (imageRepresentation M V h.normalized) = 2)
    (hrank : ∀ E : Subgroup (internalActionImage M V h.normalized), IsElementaryTwo E → rank E ≤ 2) :
    letI := h.elementary
    (∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      let B := (A.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict
      B ≠ ⊥ → Nat.card B = 2 ∧ B ∈ QhatStar (imageRepresentation M V h.normalized)) ∧
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict ≤
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ⊓
        Jhat (imageRepresentation M V h.normalized) := by
  let := h.elementary
  have ha := chosen_sylow_thompson_actors T hTM h.le_selected h.normalized h.quadratic_ratio hhat hrank
  exact ⟨fun A hA hB => ⟨(ha A hA hB).1,(ha A hA hB).2.2.2⟩,
    chosen_thompson_image_le_Jhat _ _ _ hTM h.normalized (fun A hA hB => (ha A hA hB).2.2.2)⟩
/-- The original source supplies the nonzero image in the starred-generated core.
The two remaining numerical premises are exactly the classified source15.1.7
rank bound and the nonexceptional source15.1.8 cubic ratio. -/
theorem PreparedChosenModule.thompson_nontrivial_in_Jhat
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
        centralizer ((pResidual 2 H).map H.subtype : Set G))
    (hhat : letI := h.elementary; cubicRatio (imageRepresentation M V h.normalized) = 2)
    (hrank : ∀ E : Subgroup (internalActionImage M V h.normalized), IsElementaryTwo E → rank E ≤ 2) :
    letI := h.elementary
    let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict
    J ≠ ⊥ ∧ J ≤ ((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict ⊓ Jhat (imageRepresentation M V h.normalized) := by
  let := h.elementary
  refine ⟨chosen_thompson_image_ne_bot _ _ _ hM.1.2 h.normalized ?_,
    (h.thompson_actors T hM.1.2 hhat hrank).2⟩
  exact source_chosen_thompson_one_moves hG T hempty hM hmany hJ
    h.le_selected h.nontrivial h.normalized h.seed_span h.quadratic_ratio hres

end CFSG.Quasithin.Chapter15.Section01
