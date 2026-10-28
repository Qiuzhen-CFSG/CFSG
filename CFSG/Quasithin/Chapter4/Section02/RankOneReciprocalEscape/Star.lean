module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Placement
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# The literal star image in the reciprocal configuration

The other conjugate is normal in the original intersection. Its image is
therefore normal in the same intersection's star image. The source kernel
is solvable, so this perfect subgroup remains nonsolvable and keeps its
simple two-core quotient under the actual map. Cyclic Sylow transfer carries
the required odd-prime rank bound to the star component. The final theorem
constructs these data from the original failure of residual uniqueness;
it does not yet assert the terminal Suzuki model contradiction.

Source: Aschbacher--Smith, conclusion of 4.2.10 and proof of 4.2.5, p.610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

omit [Finite G] in
/-- A normal subgroup of the original intersection stays normal in its
literal star image, without changing quotient maps. -/
theorem star_normal_of_intersection_normalizes
    (K R M J : Subgroup G) (hJ : J ≤ M ⊓ K)
    (hn : M ⊓ K ≤ normalizer (J : Set G)) :
    ((starImage K R J).subgroupOf (starM K R M)).Normal := by
  let D := K ⊔ R
  let q := QuotientGroup.mk' (starKernel K R)
  have hJK : J ≤ D := hJ.trans inf_le_right |>.trans le_sup_left
  apply normal_subgroupOf_of_le_normalizer
  change ((M ⊓ K).subgroupOf D).map q ≤ normalizer _
  apply le_trans (map_mono ?_) ((J.subgroupOf D).le_normalizer_map q)
  rw [←subgroupOf_normalizer_eq hJK]
  exact comap_mono hn

/-- The source star kernel is solvable, so a nonsolvable subgroup of
its actual component remains nonsolvable in the original quotient. -/
theorem starImage_not_isSolvable_of_source
    {H R M K J : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hJK : J ≤ K) (hJ : ¬ Group.IsSolvable J) :
    ¬ Group.IsSolvable (starImage K R J) := by
  intro hs
  let := hs
  let D := K ⊔ R
  let q := QuotientGroup.mk' (starKernel K R)
  let e := subgroupOfEquivOfLe (hJK.trans (show K ≤ D from le_sup_left))
  let f : J →* starImage K R J :=
    (q.subgroupMap (J.subgroupOf D)).comp e.symm.toMonoidHom
  let k : f.ker →* (toStarImage K R).ker :=
    { toFun := fun x => ⟨inclusion hJK x.val, by
        apply Subtype.ext
        exact congrArg (fun z : starImage K R J => (z : StarQuotient K R))
          (show f x.val = 1 from x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : (toStarImage K R).ker => (z.val : G)) hxy))
  let : Group.IsSolvable (toStarImage K R).ker :=
    ChapterC.C27Source.toStarImage_ker_solvable_from_source h
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk
  exact hJ (Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype]))

omit [Finite G] in
/-- The original quotient map restricted to a subgroup of the component. -/
@[expose] def starSubgroupMap (K R J : Subgroup G) (hJK : J ≤ K) :
    J →* starImage K R J :=
  ((QuotientGroup.mk' (starKernel K R)).subgroupMap
    (J.subgroupOf (K ⊔ R))).comp
      (subgroupOfEquivOfLe (hJK.trans le_sup_left)).symm.toMonoidHom

omit [Finite G] in
theorem starSubgroupMap_surjective (K R J : Subgroup G) (hJK : J ≤ K) :
    Function.Surjective (starSubgroupMap K R J hJK) :=
  ((QuotientGroup.mk' (starKernel K R)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (hJK.trans le_sup_left)).symm.surjective

/-- The solvable kernel bound restricts to the literal subgroup map. -/
theorem starSubgroupMap_ker_solvable
    {H R M K J : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hJK : J ≤ K) : Group.IsSolvable (starSubgroupMap K R J hJK).ker := by
  let f := starSubgroupMap K R J hJK
  let k : f.ker →* (toStarImage K R).ker :=
    { toFun := fun x => ⟨inclusion hJK x.val, by
        apply Subtype.ext
        exact congrArg (fun z : starImage K R J => (z : StarQuotient K R))
          (show f x.val = 1 from x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : (toStarImage K R).ker => (z.val : G)) hxy))
  let : Group.IsSolvable (toStarImage K R).ker :=
    ChapterC.C27Source.toStarImage_ker_solvable_from_source h
  exact Group.isSolvable_of_isSolvable_injective hk

/-- The actual star map preserves the simple two-core quotient, with its
representative formula. -/
theorem starSubgroupMap_coreQuotient_equiv
    {H R M K J : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hJK : J ≤ K) [Group.IsPerfect J] [IsSimpleGroup (J ⧸ pCore 2 J)] :
    ∃ e : (J ⧸ pCore 2 J) ≃*
        ((starImage K R J) ⧸ pCore 2 (starImage K R J)),
      ∀ j : J, e (QuotientGroup.mk' (pCore 2 J) j) =
        QuotientGroup.mk' (pCore 2 (starImage K R J)) (starSubgroupMap K R J hJK j) := by
  let : Group.IsSolvable (starSubgroupMap K R J hJK).ker :=
    starSubgroupMap_ker_solvable h hJK
  exact ⟨PerfectCoreTwoExtension.solvableKernelQuotientEquiv _
    (starSubgroupMap_surjective K R J hJK),fun _ => rfl⟩

/-- On the actual other conjugate, passing to the reversed star quotient
retains the original simple two-core quotient. -/
theorem reciprocal_star_core_quotient {L H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hM : IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)))
    (hd : ReciprocalData L H) [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)]
    (K : Subgroup (normalizer (L : Set G))) (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hfK : generalizedFitting K = pCore 2 K)
    (hout : ¬ K ≤ H.subgroupOf (normalizer (L : Set G)))
    (hmoved : ¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
      pCore 2 (normalizer (L : Set G)))
    (t : H) (ht : (t : G) ∉ normalizer (L : Set G)) :
    let B := K.map (normalizer (L : Set G)).subtype
    let E := L.map (MulAut.conj (t : G)).toMonoidHom
    Nonempty (((starImage B (H.pCoreIn 2) E) ⧸
      pCore 2 (starImage B (H.pCoreIn 2) E)) ≃* (L ⧸ pCore 2 L)) := by
  let B := K.map (normalizer (L : Set G)).subtype
  let E := L.map (MulAut.conj (t : G)).toMonoidHom
  have hEB : E ≤ B := reciprocal_conjugate_le_component hH hM hd K hK hout hmoved t ht
  let c : E ≃* L :=
    (L.equivMapOfInjective (MulAut.conj (t : G)).toMonoidHom
      (MulAut.conj (t : G)).injective).symm
  let q : (E ⧸ pCore 2 E) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := c.symm.toMonoidHom) c.symm.surjective
  have hz := reciprocal_coreQuotient_center_eq_bot hH hd
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsSimpleGroup (E ⧸ pCore 2 E) := q.isSimpleGroup
  obtain ⟨e,_⟩ := starSubgroupMap_coreQuotient_equiv
    (reciprocal_source_input hd K hK hfK hout) hEB
  exact ⟨e.symm.trans q⟩


/-- The odd-prime rank-one bound passes to the literal star component.
Cyclic Sylow transfer avoids any assumption about the star kernel. -/
theorem star_component_odd_rank_le_one (K R : Subgroup G)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : primeRank p K ≤ 1) :
    primeRank p (starImage K R K) ≤ 1 := by
  let P : Sylow p K := Classical.choice inferInstance
  exact P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one ho hr)
    (starSubgroupMap K R K le_rfl) (starSubgroupMap_surjective K R K le_rfl)

/-- Source 4.2.10 on the unchanged witnesses, together with relative
normality of the literal star image needed by the terminal model argument. -/
@[expose] def ReciprocalPlacementCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H →
      ReciprocalData L H ∧
      twoFittingCore (normalizer (L : Set G)) ≤ H.subgroupOf (normalizer (L : Set G)) ∧
      center (L ⧸ pCore 2 L) = ⊥ ∧
      ∃ K : Subgroup (normalizer (L : Set G)),
        K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        generalizedFitting K = pCore 2 K ∧ ¬ K ≤ H.subgroupOf (normalizer (L : Set G)) ∧
        (¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
          pCore 2 (normalizer (L : Set G))) ∧ K.Normal ∧
        (∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card L → primeRank p K = 1) ∧
        ∀ t : H, (t : G) ∉ normalizer (L : Set G) →
          let B := K.map (normalizer (L : Set G)).subtype
          let E := L.map (MulAut.conj (t : G)).toMonoidHom
          E ≤ B ⊓ H ∧ (E.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
          ((starImage B (H.pCoreIn 2) E).subgroupOf
            (starM B (H.pCoreIn 2) (H ⊓ normalizer (L : Set G)))).Normal ∧
          ¬ Group.IsSolvable (starImage B (H.pCoreIn 2) E) ∧
          Nonempty (((starImage B (H.pCoreIn 2) E) ⧸
            pCore 2 (starImage B (H.pCoreIn 2) E)) ≃* (L ⧸ pCore 2 L)) ∧
          ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card (starImage B (H.pCoreIn 2) E) →
            primeRank p (starImage B (H.pCoreIn 2) B) ≤ 1)

/-- Ambient selection proves the full reciprocal placement conclusions;
there are no component-containment or normality callbacks. -/
theorem reciprocal_placement_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalPlacementCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_normal_case_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hd,hfit,hz,K,hK,hq,hfK,hout,hmoved,hn,hrank⟩ := hr hf
  let := h.quasisimple
  let := hq
  let := hn
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  refine ⟨hd,hfit,hz,K,hK,hq,hfK,hout,hmoved,hn,?_,?_⟩
  · exact reciprocal_component_odd_rank_eq_one hw.2.2.2.2.2.2.1.sqtk
      (h.simpleQTKE.twoLocal_sqtk hM.1.1) hd K hK hout hmoved
  intro t ht
  have hle := reciprocal_conjugate_le_component hw.2.2.2.2.2.2.1.sqtk
    (h.simpleQTKE.twoLocal_sqtk hM.1.1) hd K hK hout hmoved t ht
  have hLH : L ≤ H := hd.1 ▸ (map_subtype_le _).trans inf_le_right
  have hEH : L.map (MulAut.conj (t : G)).toMonoidHom ≤ H := by
    rintro _ ⟨l,hl,rfl⟩
    exact H.mul_mem (H.mul_mem t.property (hLH hl)) (H.inv_mem t.property)
  have hEN := reciprocal_conjugate_normalizer hd t
  refine ⟨le_inf hle hEH,normal_subgroupOf_of_le_normalizer hEN,?_,?_,?_,?_⟩
  · exact star_normal_of_intersection_normalizes _ _ _ _
      (le_inf (le_inf hEH (hle.trans (map_subtype_le _))) hle) (inf_le_left.trans hEN)
  · let E := L.map (MulAut.conj (t : G)).toMonoidHom
    let e : L ≃* E := L.equivMapOfInjective (MulAut.conj (t : G)).toMonoidHom
      (MulAut.conj (t : G)).injective
    let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
    let : Nontrivial (L ⧸ pCore 2 L) :=
      (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
    let : Nontrivial L := (QuotientGroup.mk'_surjective (pCore 2 L)).nontrivial
    let : Nontrivial E := e.symm.surjective.nontrivial
    let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact starImage_not_isSolvable_of_source (reciprocal_source_input hd K hK hfK hout)
      hle (Group.IsPerfect.not_isSolvable E)
  · exact reciprocal_star_core_quotient hw.2.2.2.2.2.2.1.sqtk
      (h.simpleQTKE.twoLocal_sqtk hM.1.1) hd K hK hfK hout hmoved t ht
  · intro p hp ho hpE
    let : Fact p.Prime := ⟨hp⟩
    let B := K.map (normalizer (L : Set G)).subtype
    let E := L.map (MulAut.conj (t : G)).toMonoidHom
    have hpL : p ∣ Nat.card L := by
      have hd := hpE.trans (card_dvd_of_surjective
        (starSubgroupMap B (H.pCoreIn 2) E hle)
        (starSubgroupMap_surjective B (H.pCoreIn 2) E hle))
      rwa [card_map_of_injective (MulAut.conj (t : G)).injective] at hd
    let ek : K ≃* B := K.equivMapOfInjective (normalizer (L : Set G)).subtype
      (normalizer (L : Set G)).subtype_injective
    have hrB : primeRank p B ≤ 1 := by
      rw [← primeRank_equiv p ek]
      exact hrank p hp ho hpL
    exact star_component_odd_rank_le_one B (H.pCoreIn 2) ho hrB


end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
