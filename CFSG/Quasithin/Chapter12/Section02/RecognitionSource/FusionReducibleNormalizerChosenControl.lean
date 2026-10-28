module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionEight
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerFixedLine

/-!
# Normalizer control from the original chosen-module fixed spaces

B.5.1(2), applied to the faithful reduced action, puts [R₂(LT),L] in V
when the Sylow normalizer escapes and C_V(L) is nonzero. The normal closure
of Ω₁Z(T) lies in R₂(LT). Its Sylow-fixed splitting therefore gives
Ω₁Z(T) = (V ∩ Ω₁Z(T)) C_{Ω₁Z(T)}(L).

If |C_V(L)|=2 and |C_V(T)|≤4, disjointness of the two conjugate fixed
subgroups bounds the latter factor by two. Thus Ω₁Z(T)≤V, and weak closure
of the original fixed involution contradicts escape. No short-block or
canonical-module identification is assumed.

Source: Aschbacher–Smith B.5.1(2), B.2.13–14, and 12.2.16,
printed pp.99,78,799–800. This supplies the normalizer premise of the
original reducible fusion rows; final assembly stays in qt-d-12213-fusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source omega module splits inside the chosen module and its fixed subgroup. -/
theorem omegaCenter_split_chosen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) =
      (V ⊓ omegaCenterIn (T : Subgroup G)) ⊔
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let Z := Stellmacher.omegaOneCenterAmbient (P : Subgroup H)
  let W := normalClosure (Z : Set H)
  let E := omegaCenterIn (T : Subgroup G)
  let F := E ⊓ centralizer (L : Set G)
  have hWR : blockOmegaModule T L ≤ (ReducedModule H).map H.subtype :=
    map_mono (omegaCenter_normalClosure_reduced P (join_characteristicTwo h)).le_reducedPSubgroup
  have hm : ⁅blockOmegaModule T L, H⁆ ≤ V := by
    rw [blockOmegaModule_commutator_join D]
    exact (commutator_mono hWR le_rfl).trans
      (reduced_commutator_le_chosen_of_escape h D structural hne hescape)
  have hc : (center H).map H.subtype ≤ centralizer (H : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hF : (W ⊓ center H).map H.subtype ≤ F := by
    rintro _ ⟨x,⟨hx,hxc⟩,rfl⟩
    have hxW : (x:G) ∈ blockOmegaModule T L := mem_map_of_mem _ hx
    have hxC := hc (mem_map_of_mem H.subtype hxc)
    refine ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨blockOmegaModule_le_sylow h hxW,
      centralizer_le (show (T : Subgroup G) ≤ H from le_sup_right) hxC, ?_⟩,
      centralizer_le (show L ≤ H from le_sup_left) hxC⟩
    let := blockOmegaModule_elementary h
    exact elemPow_eq_one_of_isElementaryAbelian (x:G) hxW
  have hW : blockOmegaModule T L ≤ V ⊔ F := by
    have hs := congrArg (Subgroup.map H.subtype)
      (omegaCenter_subgroup_normalClosure_split P (join_characteristicTwo h) Z le_rfl)
    rw [Subgroup.map_sup, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hs
    exact hs.le.trans (sup_le_sup hm hF)
  have hVF : V ≤ normalizer (F : Set G) := by
    apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact (show F ≤ centralizer (T : Set G) from fun _ hx =>
      ((mem_omegaCenterIn_iff _ _).mp hx.1).2.1).trans (centralizer_le D.le_sylow)
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
  intro z hz
  have hzW : z ∈ V ⊔ F := hW (omegaCenter_le_blockOmegaModule hz)
  have hzprod : z ∈ (V : Set G) * (F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V F hVF]
    exact hzW
  obtain ⟨v,hv,f,hf,rfl⟩ := hzprod
  have hvE : v ∈ E := by
    have he := E.mul_mem hz (E.inv_mem hf.1)
    simpa only [mul_inv_cancel_right] using he
  exact mul_mem_sup ⟨hv,hvE⟩ hf

/-- Fixed-space bounds on the literal chosen V imply Sylow-normalizer control. -/
theorem sylow_normalizer_le_of_chosen_fixed_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
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
  have hs : E = A ⊔ F := by
    have hne : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
      intro he
      rw [he, card_bot] at hfixed
      omega
    exact omegaCenter_split_chosen h D structural hne hescape
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
