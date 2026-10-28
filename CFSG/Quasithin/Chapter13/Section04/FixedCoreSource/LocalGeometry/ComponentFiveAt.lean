module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentPointAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSmallAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFive

/-!
# The selected A₅ moved module with guarded earlier inputs

Small-quotient minimality identifies the whole moved omega orbit with a
chosen module. The earlier A₅ clause marks that same subgroup as the deleted
five-point permutation module. Its actual point centralizer supplies a cubic,
is a {2,3}-group, and has the Thompson and Baumann subgroups of O₂(K).
For ordinary original L, this gives L₁ ≤ K and both the reciprocal residual
and point-parabolic identities.

The proof specializes Nonsolvable/ComponentFive using only Structural1222At
at this G,T. ComponentFiveBlockAt consumes the original L₁T and its literal
point radical; ComponentCoveredFiveAt handles the covered original row.
The five-dimensional original V and all quotient maps are retained.
Source: Aschbacher--Smith 13.4.10(1--2), printed pp.907--908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

omit [Finite G] in
private theorem five_core_coordinates
    {U : Subgroup G} (DK : ChosenModule T K U)
    (hmodel : Chapter6.Source.IsConjugationModel K U Chapter6.Source.a5Module) :
    ∃ q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5),
      ∃ e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)),
        ∀ (k : K) (v : U),
          (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
            BinaryPermutation.coreRepresentation (Fin 5)
              (q (QuotientGroup.mk' (pCore 2 K) k)).val (e v).toAdd := by
  obtain ⟨q,e,he⟩ := hmodel
  let a := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let e0 := e.trans a.symm.toAddEquiv.toMultiplicative
  refine ⟨q,e0,?_⟩
  intro k v
  have hh : e.symm (Multiplicative.ofAdd
      (Chapter6.Source.a5Module (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)) =
        U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v :=
    Subtype.ext (he k v)
  have heq := congrArg (fun w : U => (e w).toAdd) hh
  simp only [e.apply_symm_apply] at heq
  apply a.injective
  change a (a.symm (e (U.normalizerMonoidHom _ v)).toAdd) =
    a (BinaryPermutation.coreRepresentation (Fin 5)
      (q (QuotientGroup.mk' (pCore 2 K) k)).val (a.symm (e v).toAdd))
  rw [a.apply_symm_apply,BinaryPermutation.coreEquivNatural_equivariant,a.apply_symm_apply]
  exact heq.symm

/-- The genuine earlier A₅ clause marks the entire moved omega orbit. -/
theorem component_five_marking_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      ∃ q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5),
        ∃ e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)),
          ∀ (k : K) (v : U),
            (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
              BinaryPermutation.coreRepresentation (Fin 5)
                (q (QuotientGroup.mk' (pCore 2 K) k)).val (e v).toAdd := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hcard : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨⟨DK⟩,_⟩ := component_chosen_of_small_quotient_at h₀ h structural m hzT hz1
    hKz h1332 hHN hKM hfK (Or.inl hcard)
  exact ⟨DK,five_core_coordinates DK (modules h₀ K hfK ⟨eK⟩ U DK)⟩

/-- The actual reciprocal point centralizer has a cubic and the Thompson and Baumann subgroups of O₂(K). -/
theorem five_component_reciprocal_structure_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    let C := K ⊓ normalizer (L : Set G)
    3 ∣ Nat.card C ∧ IsPiGroup twoThreePrimes C ∧
      elementaryAbelianMaxJ (C.pCoreIn 2) = elementaryAbelianMaxJ (K.pCoreIn 2) ∧
      ChapterB.baumann (C.pCoreIn 2) = ChapterB.baumann (K.pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann (C.pCoreIn 2) : Set G) ≤ normalizer (L : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,q0,e,he⟩ := component_five_marking_at h₀ h structural D m
    h1332 modules hzT hz1 hKz hHN hKM hfK eK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  let Ui := U.subgroupOf K
  let := DK.elementary
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer DK.normalizes
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.comap_of_injective K.subtype K.subtype_injective U
  let ei : Ui ≃* U := subgroupOfEquivOfLe hUK
  let eU := ei.trans e
  let q := q0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := q0.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ q0.injective,QuotientGroup.ker_mk']
  have heU (k : K) (v : Ui) : (eU (MulAut.conjNormal k v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q k).val (eU v).toAdd := by
    change (e (ei (MulAut.conjNormal k v))).toAdd = _
    have hei : ei (MulAut.conjNormal k v) =
        U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ (ei v) := Subtype.ext rfl
    rw [hei]
    exact he k (ei v)
  obtain ⟨w,hw,_,hX⟩ := component_fixed_generator_point_overgroup_at
    h₀ h structural m hzT hz1 hKz hTK hKM
  have hC : K ⊓ centralizer ({m.constant.val} : Set G) =
      K ⊓ centralizer ({w.val} : Set G) := by
    have hh := congrArg (fun B : Subgroup G => K ⊓ B) hX
    simpa only [←inf_assoc,
      inf_eq_left.mpr (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)] using hh
  let wi : Ui := ei.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg ei hh)
  have hpoint := ChapterB.AlternatingFivePoint.point_centralizer_cubic Ui q hq hk eU heU wi hwi
  have hb := ChapterB.AlternatingFivePoint.point_baumann Ui q hk eU heU wi
  let C := centralizer ({wi.val} : Set K)
  have hCm : C.map K.subtype = K ⊓ normalizer (L : Set G) := by
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh)),hC]
    ext k
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hk,hc⟩
      exact ⟨⟨k,hk⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hm := congrArg (fun A : Subgroup K => A.map K.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map K.subtype = (ChapterB.baumann (pCore 2 K)).map K.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective K.subtype K.subtype_injective,
    baumann_map_injective K.subtype K.subtype_injective,
    map_pCoreIn_of_injective 2 C K.subtype K.subtype_injective,hCm] at hm
  have hj := congrArg (fun A : Subgroup K => A.map K.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map K.subtype =
    (elementaryAbelianMaxJ (pCore 2 K)).map K.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    map_pCoreIn_of_injective 2 C K.subtype K.subtype_injective,hCm] at hj
  change ChapterB.baumann ((K ⊓ normalizer (L : Set G)).pCoreIn 2) =
    ChapterB.baumann (K.pCoreIn 2) at hm
  refine ⟨?_,?_,hj,hm,?_⟩
  · rw [←hCm,card_map_of_injective K.subtype_injective]
    exact hpoint.1
  · rw [←hCm]
    exact hpoint.2.of_surjective (K.subtype.subgroupMap C) (K.subtype.subgroupMap_surjective C)
  · rw [hm]
    intro hbound
    exact hKM ((K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
        ((normalizer_le_normalizer_baumann (K.pCoreIn 2)).trans hbound))

/-- Construct L₁ containment, reciprocal residual equality and the actual point centralizer in KT. -/
theorem ordinary_five_component_residuals_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Solvable.firstCentralizerResidual L z.val ≤ K ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
        w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
        Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
          (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨hc,h23,_,_,_⟩ := five_component_reciprocal_structure_at h₀ h structural D m
    h1332 modules hzT hz1 hKz hHN hKM hfK eK
  have hJK := ordinary_firstResidual_le_of_reciprocal_cubic_at h structural D m eL z hzL hKz hHN hc
  have hr := component_reciprocal_residual_of_containment_at h structural m z.val hKz hHN eL hJK
  refine ⟨hJK,hr,?_⟩
  have hTK := (h1332 K hfK).1
  obtain ⟨w,hw,hTw,hX⟩ := component_fixed_generator_point_overgroup_at h₀ h structural m hzT hz1 hKz hTK hKM
  have hC : K ⊓ normalizer (L : Set G) = K ⊓ centralizer ({w.val} : Set G) := by
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    ext k
    exact ⟨fun hk => ⟨hk.1,(hX.le ⟨mem_sup_left hk.1,hk.2⟩).2⟩,
      fun hk => ⟨hk.1,(hX.ge ⟨mem_sup_left hk.1,hk.2⟩).2⟩⟩
  rw [hC] at h23
  rw [Solvable.firstCentralizerResidual_eq,
    fixed_generator_centralizer_at h structural D m ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh)),hC,
    ←twoResidual_eq_primeToResidual_three h23] at hr
  refine ⟨w,hw,hTw,?_⟩
  rw [←hr]
  exact embedded_pointResidual_sup_sylow T K hTK w.val hTw

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
