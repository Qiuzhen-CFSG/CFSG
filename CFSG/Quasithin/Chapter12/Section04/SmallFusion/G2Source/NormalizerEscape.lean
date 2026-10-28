module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Normalizer
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Setup

/-!
# The central four-group in an escaping binary G₂ configuration

The Weyl cover bounds the fixed subgroup of the original component by two
and the Sylow-fixed subgroup by four. Under failure of Sylow-normalizer
control, the source omega splitting and disjoint conjugate centralizers force
the entire central omega subgroup into the chosen module, with order four.
This step uses neither global TI nor the NoEscape hypothesis.

The final application retains an actual odd-order normalizer subgroup and
an escaping conjugator. Its two fixed lines span this same central four-group,
which lies in both conjugate chosen modules. The terminal exclusion of this
configuration remains a separate source obligation.

Source: Aschbacher--Smith 3.3.7(4), 3.3.27(1) and B.4.6, printed
pp.587,600 and 88--90; applied to the original 12.4 binary Weyl marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem omega_geometry_of_fixed_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hfixed : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2)
    (hsmall : Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 4)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) ≤ V ∧
      Nat.card (omegaCenterIn (T : Subgroup G)) = 4 := by
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
  let E := omegaCenterIn (T : Subgroup G)
  let A := V ⊓ E
  let F := E ⊓ centralizer (L : Set G)
  have hzE : z ∈ E := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨D.le_sylow hz.1, ?_, ?_⟩
    · intro t ht
      exact (mem_centralizer_singleton_iff.mp
        (normalizer_centralizes_fixed_line_at h D structural hz.1 hz1 hz.2 hfix
          (D.sylow_normalizes_component ht)))
    · let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian z hz.1
  have hs : E = A ⊔ F := by
    have hne : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
      intro he
      rw [he, card_bot] at hfixed
      omega
    exact omegaCenter_split_chosen_at h D structural hne hescape
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
  have hAE : A = E := inf_eq_right.mpr hEV
  have hFc : Nat.card F = 2 := by
    rwa [inf_eq_right.mpr hFA] at hAC
  rw [hFc] at hFbound
  rw [hAE] at hAsmall
  exact ⟨hEV, le_antisymm hAsmall hFbound⟩

/-- The escaping Weyl row has its entire central four-group in the literal V. -/
theorem omega_geometry_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) ≤ V ∧
      Nat.card (omegaCenterIn (T : Subgroup G)) = 4 := by
  let p := Atlas.G2.Natural.OrthogonalCover.projection (ZMod 2)
  have hp := Atlas.G2.Natural.OrthogonalCover.projection_isCover (ZMod 2)
  let ec := chosenCentralEquiv_of_cover D e p hp.1
    (by rw [Atlas.G2.Natural.OrthogonalCover.projection_ker,
      Atlas.G2.Natural.OrthogonalCover.fixed_eq_scalarLine])
  have hc := fixed_card_eq_two D e hne
  exact omega_geometry_of_fixed_bounds h D structural hc
    (ChosenCover.sylow_fixed_card_le_four D ec hc
      Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two) hescape

/-- An odd escaping actor moves the fixed line to a complementary line in the
literal central four-group. Both chosen modules contain that same four-group. -/
theorem exists_odd_escape_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let E := omegaCenterIn (T : Subgroup G)
    let F := V ⊓ centralizer (L : Set G)
    ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
      (T : Subgroup G) ⊔ A = normalizer (T : Set G) ∧
      ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
        Nat.card E = 4 ∧
        F ⊓ F.map (MulAut.conj d).toMonoidHom = ⊥ ∧
        E = F ⊔ F.map (MulAut.conj d).toMonoidHom ∧
        E ≤ V ⊓ V.map (MulAut.conj d).toMonoidHom ∧
        V.map (MulAut.conj d).toMonoidHom ≠ V := by
  dsimp only
  let E := omegaCenterIn (T : Subgroup G)
  let F := V ⊓ centralizer (L : Set G)
  obtain ⟨hEV, hEcard⟩ := omega_geometry_of_escape h D structural e hne hescape
  obtain ⟨z, _, hgen, _, hNV, hzE, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  have hFE : F ≤ E := by
    change V ⊓ centralizer (L : Set G) ≤ omegaCenterIn (T : Subgroup G)
    rw [hgen, omegaCenterIn_eq_omegaOneAmbient]
    exact zpowers_le_of_mem hzE
  obtain ⟨A, hAN, ho, hjoin, _⟩ := exists_odd_normalizer_complement T
  have hA : ¬ A ≤ normalizer (L : Set G) := by
    intro ha
    exact hescape (hjoin ▸ sup_le D.sylow_normalizes_component ha)
  obtain ⟨d, hdA, hout⟩ := SetLike.not_le_iff_exists.mp hA
  have hd := hAN hdA
  let f := (MulAut.conj d).toMonoidHom
  have hEd : E.map f = E := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G) hd)
  have hFd : F.map f ≤ E := (map_mono hFE).trans hEd.le
  have hdis : F ⊓ F.map f = ⊥ := by
    apply bot_unique
    apply le_trans (inf_le_inf ?_ (map_mono ?_))
      (sylow_centralizer_disjoint_conjugate h D hd hout).le
    all_goals exact inf_le_inf_right _ D.le_sylow
  have hnorm : F.map f ≤ normalizer (F : Set G) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro b hb j hj
    have hbT := ((mem_omegaCenterIn_iff _ _).mp (hFE hb)).1
    exact (((mem_omegaCenterIn_iff _ _).mp (hFd hj)).2.1 b hbT).symm
  have hproduct := card_mul_eq_card_inf_mul_card_sup_of_normalizes F (F.map f) hnorm
  have hFcard : Nat.card F = 2 := fixed_card_eq_two D e hne
  rw [card_map_of_injective (MulAut.conj d).injective, hdis, card_bot,
    one_mul, hFcard] at hproduct
  have hspan : E = F ⊔ F.map f := (eq_of_le_of_card_ge (sup_le hFE hFd)
    (by rw [hEcard]; exact hproduct.le)).symm
  have hEVd : E ≤ V.map f := hEd ▸ map_mono hEV
  refine ⟨A, hAN, ho, hjoin, d, hdA, hout, hEcard, hdis, hspan,
    le_inf hEV hEVd, ?_⟩
  intro he
  exact hout (hNV ▸ mem_normalizer_iff_map_conj_eq.mpr he)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
