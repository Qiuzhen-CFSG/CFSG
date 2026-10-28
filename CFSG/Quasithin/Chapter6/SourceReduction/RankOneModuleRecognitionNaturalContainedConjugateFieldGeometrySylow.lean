module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryThompson
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.DisjointConjugateCenter
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Sylow and characteristic-two control for the field fixed space

The module centralizers for different ambient Sylows are conjugate inside
C_G(B), so E.6.1 controls the normalizer of their Thompson subgroups.
The field-plane offender exclusion identifies J(N_P(U)) and J(C_P(U))
with J(C_P(B)). Relative Sylow promotion then gives the full normalizer
and centralizer Sylows. A nontrivial central fixed point of B lies in U;
source 1.1.4(3) supplies characteristic two.

Source: Aschbacher–Smith, 6.1.14(1–2), printed pp.670–671.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem sylow_module_centralizer (P : Sylow 2 G) (B : Subgroup G)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ S : Sylow 2 (centralizer (B : Set G)),
      (S : Subgroup (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype =
        (P : Subgroup G) ⊓ centralizer (B : Set G) := by
  let N := normalizer (B : Set G)
  let C := (centralizer (B : Set G)).subgroupOf N
  obtain ⟨S, hS⟩ := (P.subtype hPB).exists_subgroupOf_eq_of_normal C
  let e : C ≃* centralizer (B : Set G) :=
    subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (B : Set G))
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup C).map e.toMonoidHom).map _ = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨hs, s.property⟩
  · rintro ⟨hxP, hxC⟩
    let s : C := ⟨⟨x, Subgroup.centralizer_le_normalizer (B : Set G) hxC⟩, hxC⟩
    exact ⟨e s, ⟨s, hxP, rfl⟩, rfl⟩

theorem field_sylow_kernel_thompson_normalizer
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M B : Subgroup G}
    (hE : ChapterE.Section06.HypothesisE61 κ T M B)
    (P : Sylow 2 G) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G)) :
    normalizer (elementaryAbelianMaxJ
      ((P : Subgroup G) ⊓ centralizer (B : Set G)) : Set G) ≤ M := by
  let Q := ChapterE.Section06.sylowCentralizer (T : Subgroup G) B
  have hp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hj : normalizer (elementaryAbelianMaxJ Q : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal hE.unique
      (hp.to_le (sSup_le fun A hA => hA.1))
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q hp hE.sylowCentralizer_ne_bot)
      (inf_le_right.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  obtain ⟨R, hR⟩ := hE.sylow_centralizer
  change _ = Q at hR
  obtain ⟨S, hS⟩ := sylow_module_centralizer P B hPB
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer (B : Set G)) R S
  have he : Q.map (MulAut.conj (c : G)).toMonoidHom =
      (P : Subgroup G) ⊓ centralizer (B : Set G) := by
    rw [← hR, ← hS, ← hc]
    ext x
    constructor
    · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨c * r * c⁻¹, ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨r, hr, heq⟩, rfl⟩
      refine ⟨(r : G), ⟨r, hr, rfl⟩, ?_⟩
      exact congrArg Subtype.val heq
  have hm := map_mono (f := (MulAut.conj (c : G)).toMonoidHom) hj
  rw [map_equiv_normalizer_eq, ← elementaryAbelianMaxJ_map_equiv, he] at hm
  exact hm.trans (le_of_eq (mem_normalizer_iff_map_conj_eq.mp
    (M.le_normalizer (hE.centralizer_le c.property))))

/-- The arranged Sylow in N_M(U) is Sylow in the full normalizer, and
its centralizer intersection is Sylow in C_G(U). -/
theorem field_fixedSpace_sylow_control
    {κ : GroupClass.{u}} {T : Sylow 2 G} {L M B U : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 B]
    (hE : ChapterE.Section06.HypothesisE61 κ T M B)
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hML : M ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (P : Sylow 2 G) (hBP : B ≤ P)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (hSyl : ∃ R : Sylow 2 (M ⊓ normalizer (U : Set G) : Subgroup G),
      (R : Subgroup (M ⊓ normalizer (U : Set G) : Subgroup G)).map
        (M ⊓ normalizer (U : Set G)).subtype =
          (P : Subgroup G) ⊓ normalizer (U : Set G)) :
    normalizer (elementaryAbelianMaxJ
      ((P : Subgroup G) ⊓ normalizer (U : Set G)) : Set G) ≤ M ∧
    normalizer (elementaryAbelianMaxJ
      ((P : Subgroup G) ⊓ centralizer (U : Set G)) : Set G) ≤ M ∧
    (∃ R : Sylow 2 (normalizer (U : Set G)),
      (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype =
        (P : Subgroup G) ⊓ normalizer (U : Set G)) ∧
    (∃ R : Sylow 2 (centralizer (U : Set G)),
      (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (P : Subgroup G) ⊓ centralizer (U : Set G)) := by
  have hUB : U ≤ B := by
    obtain ⟨_, _, _, hU, _⟩ := hfield
    exact hU.le.trans inf_le_left
  have hCBU : centralizer (B : Set G) ≤ centralizer (U : Set G) := centralizer_le hUB
  have hBCU : B ≤ centralizer (U : Set G) := B.le_centralizer.trans hCBU
  have hBNU := hBCU.trans (Subgroup.centralizer_le_normalizer _)
  have hcontrol (S : Subgroup G) (hBS : B ≤ S) (hSP : S ≤ P)
      (hSU : S ≤ normalizer (U : Set G))
      (hQ : S ⊓ centralizer (B : Set G) = (P : Subgroup G) ⊓ centralizer (B : Set G)) :
      normalizer (elementaryAbelianMaxJ S : Set G) ≤ M := by
    rw [(field_fixedSpace_thompson_centralizes hn hnatural
      (hE.normalizer_le.trans hML) hfield hUne S hBS (hSP.trans hPB) hSU).2, hQ]
    exact field_sylow_kernel_thompson_normalizer hE P hPB
  have hN : normalizer (elementaryAbelianMaxJ
      ((P : Subgroup G) ⊓ normalizer (U : Set G)) : Set G) ≤ M := by
    apply hcontrol _ (le_inf hBP hBNU) inf_le_left inf_le_right
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _ (hCBU hx.2)⟩, hx.2⟩⟩
  have hC : normalizer (elementaryAbelianMaxJ
      ((P : Subgroup G) ⊓ centralizer (U : Set G)) : Set G) ≤ M := by
    apply hcontrol _ (le_inf hBP hBCU) inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hCBU hx.2⟩, hx.2⟩⟩
  have hfull := exists_sylow_eq_of_relative_normalizer_le hSyl inf_le_right
    (le_inf (inf_le_right.trans
      ((normalizer_le_normalizer_elementaryAbelianMaxJ _).trans hN)) inf_le_left)
  refine ⟨hN, hC, hfull, ?_⟩
  obtain ⟨R, hR⟩ := hfull
  let H := normalizer (U : Set G)
  let C := (centralizer (U : Set G)).subgroupOf H
  obtain ⟨S, hS⟩ := R.exists_subgroupOf_eq_of_normal C
  let e : C ≃* centralizer (U : Set G) :=
    subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (U : Set G))
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup C).map e.toMonoidHom).map _ = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
    have hh := hR ▸ mem_map_of_mem H.subtype hs
    exact ⟨hh.1, s.property⟩
  · rintro ⟨hxP, hxC⟩
    let s : C := ⟨⟨x, Subgroup.centralizer_le_normalizer (U : Set G) hxC⟩, hxC⟩
    have hs : (s : H) ∈ R := by
      apply (mem_map_iff_mem H.subtype_injective).mp
      rw [hR]
      exact ⟨hxP, Subgroup.centralizer_le_normalizer (U : Set G) hxC⟩
    exact ⟨e s, ⟨s, hs, rfl⟩, rfl⟩

/-- A central fixed point of the normal elementary module lies in U,
so source 1.1.4(3) gives characteristic two for its full normalizer. -/
theorem field_fixedSpace_even_local
    {L B U : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 B]
    (P : Sylow 2 G) (hEven : IsEvenCharacteristicAt P)
    (hBP : B ≤ P) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L (P : Subgroup G) B U n)
    (hUne : U ≠ ⊥) :
    normalizer (U : Set G) ∈ Chapter1.He G ∧
      centralizer (U : Set G) ∈ Chapter1.He G ∧
      generalizedFitting (normalizer (U : Set G)) =
        pCore 2 (normalizer (U : Set G)) := by
  obtain ⟨t, htP, _, hU, _⟩ := hfield
  have hUB : U ≤ B := hU.le.trans inf_le_left
  have hpU : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 B).to_le hUB
  have hBne : B ≠ ⊥ := fun he => hUne (bot_unique (he ▸ hUB))
  have hmeet := inf_centerIn_ne_bot P.isPGroup' hBne hBP hPB
  have hle : B ⊓ centerIn (P : Subgroup G) ≤
      (center (P : Subgroup G)).map (P : Subgroup G).subtype ⊓ U := by
    intro b hb
    have hz := hb.2
    rw [centerIn_eq_map_center] at hz
    refine ⟨hz, ?_⟩
    rw [hU]
    refine ⟨hb.1, mem_centralizer_singleton_iff.mpr ?_⟩
    obtain ⟨z, hz, rfl⟩ := hz
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t, htP⟩).symm
  have hN := (Chapter1.lemma_1_1_4_3 P hEven hUne hpU
    (fun he => hmeet (bot_unique (he ▸ hle)))).2.2
  refine ⟨hN, ?_, generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hN)⟩
  have hC := pCoreIn_selfCentralizing_centralizer hN hpU U.le_normalizer
  change centralizer (U : Set G) ⊓ centralizer ((centralizer (U : Set G)).pCoreIn 2 : Set G) ≤
    (centralizer (U : Set G)).pCoreIn 2
  simpa only [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer (U : Set G))] using hC

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
