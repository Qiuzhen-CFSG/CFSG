module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerOmegaSplitting
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedLine
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A fixed-line route to the surviving-block normalizer

For a short component the chosen Irr⁺ subgroup is exactly U(L): its full
commutator equation places it in U(L), and the short normal-layer dichotomy
rules out a proper noncentral submodule. If C_V(L) has order two and C_V(T)
has order at most four, the source omega splitting and the disjointness of
conjugate centralizers imply Ω₁Z(T) ≤ V. Fixed-line weak closure under the
original NoEscape hypothesis then forces N_G(T) ≤ N_G(L).

This specialized route uses hypotheses already present at the 12.2.16
consumer. It does not identify V with the omega-generated module in advance.
The numerical model bounds are discharged in the nonalternating completion module.
Source: Aschbacher–Smith 3.3.7(4), 3.3.27(1), pp.587,600; 12.2.16, p.800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The original chosen module equals the intrinsic short commutator layer. -/
theorem chosen_eq_blockU (D : ChosenModule T L V) (hb : ChapterC.IsShort L) :
    V = (ChapterC.blockU L).map L.subtype := by
  have hV : V ≤ (ChapterC.blockU L).map L.subtype := by
    rw [block_module_eq_commutator]
    exact D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl)
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  have hVi : V.subgroupOf L ≤ ChapterC.blockU L := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hV hx
    exact (Subtype.ext he : y = x) ▸ hy
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy hb
      (V.subgroupOf L) hVi with hc | he
  · have hv : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      exact congrArg Subtype.val (mem_center_iff.mp
        (hc (show (⟨v, D.le_component hv⟩ : L) ∈ V.subgroupOf L from hv)) ⟨l, hl⟩)
    exact (D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hv))).elim
  · have hm := congrArg (map L.subtype) he
    rwa [map_subgroupOf_eq_of_le D.le_component] at hm

/-- The literal reducible normalizer consumer from its two fixed-space bounds. -/
theorem sylow_normalizer_le_of_small_fixed_spaces
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hb : ChapterC.IsShort L)
    (hfixed : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2)
    (hsmall : Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 4) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let C := V ⊓ centralizer (L : Set G)
  obtain ⟨zi,hzi,hunique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hfixed
  let z : G := zi
  have hz : z ∈ C := zi.property
  have hz1 : z ≠ 1 := fun he => hzi (Subtype.ext he)
  have hfix : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hw hc
    by_cases he : w = 1
    · exact Or.inl he
    · exact Or.inr (congrArg Subtype.val (hunique ⟨w,hw,hc⟩
        (fun hh => he (congrArg Subtype.val hh))))
  by_contra hescape
  let E := omegaCenterIn (T : Subgroup G)
  let A := V ⊓ E
  let F := E ⊓ centralizer (L : Set G)
  have hzE : z ∈ E := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨D.le_sylow hz.1, ?_, ?_⟩
    · intro t ht
      exact (mem_centralizer_singleton_iff.mp
        (normalizer_centralizes_fixed_line h D structural hz.1 hz1 hz.2 hfix
          (D.sylow_normalizes_component ht)))
    · let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian z hz.1
  have hF : blockOmegaModule T L ⊓ centralizer (L ⊔ (T : Subgroup G) : Subgroup G) = F := by
    apply le_antisymm
    · rintro x ⟨hx,hc⟩
      refine ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨blockOmegaModule_le_sylow h hx,
        centralizer_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) hc, ?_⟩,centralizer_le (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hc⟩
      let := blockOmegaModule_elementary h
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    · rintro x ⟨hx,hc⟩
      refine ⟨omegaCenter_le_blockOmegaModule hx, ?_⟩
      have hy : L ⊔ (T : Subgroup G) ≤ centralizer ({x} : Set G) :=
        sup_le
          (fun l hl => mem_centralizer_singleton_iff.mpr (hc l hl))
          (fun t ht => mem_centralizer_singleton_iff.mpr
            (((mem_omegaCenterIn_iff _ _).mp hx).2.1 t ht))
      intro y hyH
      exact mem_centralizer_singleton_iff.mp (hy hyH)
  have hs : E = A ⊔ F := by
    simpa only [← chosen_eq_blockU D hb, hF] using omegaCenter_split_blockU h D hescape hb
  have hAC : Nat.card (A ⊓ F : Subgroup G) = 2 := by
    have he : A ⊓ F = C := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · intro w hw
        rcases hfix w hw.1 hw.2 with rfl | rfl
        · exact one_mem _
        · exact ⟨⟨hz.1,hzE⟩,hzE,hz.2⟩
    exact he ▸ hfixed
  have hAsmall : Nat.card A ≤ 4 := (card_le_of_le (inf_le_inf_left V
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1))).trans hsmall
  obtain ⟨d,hd,hout⟩ := SetLike.not_le_iff_exists.mp hescape
  let f := (MulAut.conj d).toMonoidHom
  have hEd : E.map f = E := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G) hd)
  have hFd : F.map f ≤ E := (map_mono (show F ≤ E from inf_le_left)).trans hEd.le
  have hdis : F ⊓ F.map f = ⊥ := by
    apply bot_unique
    apply le_trans (inf_le_inf ?_ (map_mono ?_))
      (sylow_centralizer_disjoint_conjugate h D hd hout).le
    all_goals exact le_inf (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx.1).1) inf_le_right
  have hn (B J : Subgroup G) (hB : B ≤ E) (hJ : J ≤ E) : J ≤ normalizer (B : Set G) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro b hb j hj
    have hbT := ((mem_omegaCenterIn_iff _ _).mp (hB hb)).1
    exact (((mem_omegaCenterIn_iff _ _).mp (hJ hj)).2.1 b hbT).symm
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A F
    (hn A F inf_le_right inf_le_left)
  rw [hAC,←hs] at hprod
  have hFbound : Nat.card F * Nat.card F ≤ Nat.card E := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F (F.map f)
      (hn F (F.map f) inf_le_left hFd)
    rw [card_map_of_injective (MulAut.conj d).injective,hdis,card_bot,one_mul] at hc
    exact hc.le.trans (card_le_of_le (sup_le inf_le_left hFd))
  have hFsmall : Nat.card F ≤ 2 := by
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith
  have hFA : F ≤ A := by
    have he : A ⊓ F = F := eq_of_le_of_card_ge inf_le_right (hFsmall.trans_eq hAC.symm)
    exact he ▸ inf_le_left
  have hEV : E ≤ V := by rw [hs]; exact sup_le inf_le_left (hFA.trans inf_le_left)
  exact hescape (normalizer_le_of_fixed_line_in_omega h D structural hnone
    hz.1 hz1 hz.2 hfix (T : Subgroup G) hzE hEV)
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
