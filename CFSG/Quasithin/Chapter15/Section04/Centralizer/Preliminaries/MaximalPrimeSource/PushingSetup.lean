module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.IntersectionSetup
public import Theory.GroupTheory.PCoreImage

/-!
# The literal pushing-up setup from the intersection argument

A.4.4 identifies R = O₂(M ∩ H) with O₂(M). Maximal two-locality gives
N_G(R)=M, so the relative normalizer in H is M ∩ H. Characteristic
normalizers transport through the actual subgroup equivalence. The
normal closure of R inside M ∩ H is R itself, supplying its Sylow clause.
Characteristic two also gives the constrained-Fitting-preimage premise
of C.2.6, with every intrinsic core embedded in the ambient group.

Source: Aschbacher–Smith, printed p.1157, proof of 15.4.3(1);
A.4.4 on p.58 and Hypothesis C.2.3 on p.144.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A maximal two-local is the full normalizer of its nontrivial two-core. -/
theorem maximal_twoLocal_core_normalizer {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    normalizer (M.pCoreIn 2 : Set G) = M := by
  have hn : M ≤ normalizer (M.pCoreIn 2 : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  exact (hM.eq_of_le ⟨M.pCoreIn 2, Chapter1.mem_H_of_isTwoLocal hM.1,
    isPGroup_pCoreIn 2 M, rfl⟩ hn).symm

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

omit [Finite G] in
/-- Restrict the characteristic-normalizer construction using the actual
subgroup equivalence, not a centralizer in its place. -/
theorem characteristicNormalizerIn_restrict {H R I : Subgroup G}
    (hRH : R ≤ H) (hcontrol : ChapterA.Section04.characteristicNormalizerIn H R ≤ I) :
    (R.subgroupOf H).characteristicNormalizerClosure ≤ I.subgroupOf H := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hne
  let e := subgroupOfEquivOfLe hRH
  let D := C.map e.toMonoidHom
  let _ := hC
  let _ : D.Characteristic := characteristic_map_equiv e C
  have hD : D ≠ ⊥ := fun he => hne ((C.map_eq_bot_iff_of_injective e.injective).mp he)
  have he : (C.map (R.subgroupOf H).subtype).map H.subtype = D.map R.subtype := by
    rw [map_map, map_map]
    rfl
  intro g hg
  have hgN : (g : G) ∈ normalizer (D.map R.subtype : Set G) := by
    rw [← he]
    exact (C.map (R.subgroupOf H).subtype).le_normalizer_map H.subtype
      (mem_map.mpr ⟨g, hg, rfl⟩)
  apply hcontrol
  have hle : H ⊓ normalizer (D.map R.subtype : Set G) ≤
      ChapterA.Section04.characteristicNormalizerIn H R :=
    le_iSup_of_le D (le_iSup_of_le (inferInstance : D.Characteristic)
      (le_iSup_of_le hD le_rfl))
  exact hle ⟨g.property, hgN⟩

/-- A.4.4 supplies every C.2.3 premise. In particular R is normal in I,
so its normal closure is taken inside I and is just R. -/
theorem pushingUp_of_intersection {M H A : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hcore : M.pCoreIn 2 ≤ A) (hAI : A ≤ M ⊓ H)
    (ha : ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage M A)) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      H ((M ⊓ H).pCoreIn 2) (M ⊓ H) := by
  let I := M ⊓ H
  let R := I.pCoreIn 2
  have he : M.pCoreIn 2 = R := ChapterA.Section04.lemma_A_4_4_1 M H A hcore hAI ha
  have hRI : R ≤ I := pCoreIn_le 2 I
  have hRH : R ≤ H := hRI.trans inf_le_right
  have hn : normalizer (R : Set G) = M := by rw [← he]; exact maximal_twoLocal_core_normalizer hM
  have hne : R ≠ ⊥ := he ▸ Chapter1.mem_H_of_isTwoLocal hM.1
  have hcontrol := ChapterA.Section04.lemma_A_4_4_2 M H A hcore hAI ha hM
  have hnormal : (R.subgroupOf I).Normal := by
    change ((I.pCoreIn 2).subgroupOf I).Normal
    rw [pCoreIn, subgroupOf, comap_map_eq_self_of_injective I.subtype_injective]
    infer_instance
  refine ⟨hH, hRH, inf_le_right, ⟨?_, ?_⟩,
    characteristicNormalizerIn_restrict hRH hcontrol, ?_⟩
  · intro hb
    change R.subgroupOf H = ⊥ at hb
    apply hne
    simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using congrArg (map H.subtype) hb
  · apply map_injective H.subtype_injective
    change ((normalizer (R.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = (R.subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hRH]
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      ← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype, hn,
      inf_comm M H]
    exact congrArg (pCoreIn 2) (inf_comm H M)
  · let _ := hnormal
    rw [normalClosure_eq_self, map_subgroupOf_eq_of_le hRI]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 I, le_rfl,
      fun U _ hRU hUR => le_antisymm hUR hRU⟩

omit [Finite G] in
/-- The Fitting preimage is normal in its source overgroup. -/
theorem twoFittingPreimage_normal (M : Subgroup G) :
    ((twoFittingPreimage M).subgroupOf M).Normal := by
  rw [twoFittingPreimage, subgroupOf,
    comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

/-- The constrained-preimage premise of C.2.6 follows from characteristic
two; all intrinsic cores are embedded back into the same ambient group. -/
theorem twoFittingPreimage_generalizedFitting {M : Subgroup G}
    (hM : M ∈ Chapter1.He G) (hs : Group.IsSolvable M) :
    (generalizedFitting (twoFittingPreimage M)).map (twoFittingPreimage M).subtype =
      M.pCoreIn 2 := by
  let K := twoFittingPreimage M
  have hKM : K ≤ M := map_subtype_le _
  have hn : M ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKM).mp (twoFittingPreimage_normal M)
  have hRK : M.pCoreIn 2 ≤ K := by
    dsimp only [K]
    rw [twoFittingPreimage_eq_generalized M hs]
    exact ChapterA.Section04.twoCore_le_fittingPreimage M
  have he : K.pCoreIn 2 = M.pCoreIn 2 := le_antisymm
    (pCoreIn_mono_of_normalizes hKM hn)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) hRK
      (hKM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))))
  have hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hKM)).mp
      (subnormal_core_selfCentralizing (Chapter1.mem_He_iff.mp hM) _
        (twoFittingPreimage_normal M).isSubnormal)
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2 hc]
  exact he

/-- The actual selected X discharges the A.4.4 and C.2.3 hypotheses. -/
theorem source_pushingUp_setup (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M H : Subgroup G} (hM : IsMaximalTwoLocal M) (hH : IsMaximalTwoLocal H)
    (hXM : X ⊔ (T : Subgroup G) ≤ M) (hXH : X ⊔ (T : Subgroup G) ≤ H)
    (hNH : normalizer (X : Set G) ≤ H) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      H ((M ⊓ H).pCoreIn 2) (M ⊓ H) := by
  let : Fact (pCore 2 X).index.Prime := ⟨hX.2.2.2.1⟩
  have hXF := (source_iterated_core_containment T h h42 hX hp hmax hM hXM).1.trans
    (twoPrimePreimage_le_twoFittingPreimage (pCore 2 X).index M)
  have hYM := (normalizerResidual_bounds T hX hXF hNH).2
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTM := le_sup_right.trans hXM
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  exact pushingUp_of_intersection hM (h.simpleQTKE.twoLocal_sqtk hH.1)
    (A := normalizerResidual M X ⊔ M.pCoreIn 2) le_sup_right
    (sup_le hYM (le_inf (pCoreIn_le 2 M) (hcoreT.trans (le_sup_right.trans hXH))))
    (normalizerResidual_intersectionAlternative T hX hXM
      ((h42 T h).solvable M hM (le_sup_right.trans hXM)) hXF)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
