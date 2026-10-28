module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpaceMarking


/-!
# The conjugate line in the field-escape argument

E.3.10 puts a whole noncentralizing conjugate normalizing B in the binary
A₂ family. Semilinearity forces this image into the actual natural SL₂
layer, and the exact corank formula makes its order that of a Sylow
subgroup. Sylow lifting identifies its commutator with an L-conjugate of
the original fixed line. Inverse conjugation gives the line in 6.1.14(5)
without assuming mutual normalization.

Source: Aschbacher–Smith, 6.1.10(3), 6.1.12 and 6.1.14(5), pp.670–671.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open NaturalAction
variable {G : Type*} [Group G] [Finite G] {L B A : Subgroup G}
  [IsElementaryAbelian 2 B] {n : ℕ}

/-- An A₂ image of full natural rank fills a Sylow of the actual SL₂ image. -/
theorem natural_A2_maximal_offender
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hA : ChapterE.inducedAutomizer B A ∈
      ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation B) 2)
    (hcard : Nat.card (ChapterE.inducedAutomizer B A) = 2 ^ n) :
    IsOffender (ChapterE.automizerRepresentation B) (ChapterE.inducedAutomizer B A) := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j, E, hE⟩ := marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let I := ChapterE.inducedAutomizer B A
  let ρ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hρ : Function.Injective ρ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, ρ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE, E.apply_symm_apply]
  have hfix (D : Subgroup (ChapterE.Automizer B)) (v : Additive B) :
      E v ∈ fixedSpace ρ D ↔ v ∈ fixedSpace (ChapterE.automizerRepresentation B) D := by
    constructor
    · intro hv a
      apply E.injective
      change E (ChapterE.automizerRepresentation B a v) = E v
      have hh := hv a
      change E (ChapterE.automizerRepresentation B a (E.symm (E v))) = E v at hh
      simpa only [E.symm_apply_apply] using hh
    · intro hv a
      change E (ChapterE.automizerRepresentation B a (E.symm (E v))) = E v
      rw [E.symm_apply_apply]
      exact congrArg E (hv a)
  have hI : I ∈ ChapterE.fixedSpaceFamily ρ 2 := by
    refine ⟨hA.1, hA.2.1, ?_⟩
    intro D hDI hidx
    ext v
    obtain ⟨w, rfl⟩ := E.surjective v
    rw [hfix, hfix, hA.2.2 D hDI hidx]
  let : C.Normal := induced_normal hNL
  have hlin := fixedSpaceFamily_two_fieldLinear ρ hI (fun a =>
    Representation.SL2NaturalOffenders.normalizer_semilinear C j ρ hnat a)
  have hIC : I ≤ C := by
    intro a ha
    exact Representation.SL2NaturalOffenders.mem_of_linear_square_one C j ρ hρ hnat
      (letI := hI.2.1.2; elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
      (hlin a ha)
  have hp : IsPGroup 2 (I.subgroupOf C) := hI.2.1.2.isPGroup.comap_subtype
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hIP : I ≤ (P : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hIC]
    exact map_mono hP
  have heq : I = (P : Subgroup C).map C.subtype := eq_of_le_of_card_ge hIP (by
    rw [card_map_of_injective C.subtype_injective,
      Representation.SL2NaturalOffenders.sylow_card C j P, hF]
    exact hcard.ge)
  have hoff := Representation.SL2NaturalOffenders.Ratios.sylowImage_offender C j ρ hnat P
  rw [← heq] at hoff
  have hb := hoff.map_equivariant ρ (ChapterE.automizerRepresentation B)
    (MonoidHom.id _) Function.injective_id E.symm (by
      intro a v
      change E.symm (E (ChapterE.automizerRepresentation B a (E.symm v))) = _
      rw [E.symm_apply_apply]
      rfl)
  simpa only [map_id] using hb

/-- A whole noncentralizing conjugate normalizing B is an A₂ actor of full
natural rank, hence an offender even without mutual normalization. -/
theorem conjugate_offender_of_normalizes
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hs : ChapterE.globalS B = n)
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ normalizer (B : Set G))
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    IsOffender (ChapterE.automizerRepresentation B)
      (ChapterE.inducedAutomizer B (B.map (MulAut.conj g).toMonoidHom)) := by
  have hcor : ChapterE.subgroupCorank (B.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom) = 0 := by
    simp [ChapterE.subgroupCorank]
  have hcomm : ⁅B, B.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hA := (ChapterE.inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS
    g (le_inf le_rfl hg) (by rw [hcor, hs]; exact_mod_cast (show 0 < n by omega)) hcomm).2
  rw [hs, ENat.toNat_natCast, hcor, Nat.sub_zero] at hA
  have hA2 := ChapterE.fixedSpaceFamily_mono _ (by decide) hn hA
  have hc := conjugate_action_corank_eq_of_rank_bound B hs
    (NaturalAction.elementaryActionRankBound hn hnatural hNL) g hg hnon
  apply natural_A2_maximal_offender hnatural hNL hA2
  rw [hA2.2.1.card_eq_two_pow_rank, ChapterE.rank_inducedAutomizer _ _ hg, hc]

/-- Without mutual normalization, the commutator is still a conjugate of
the Sylow line of the normalized natural module. -/
theorem conjugate_commutator_line_of_normalizes
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hs : ChapterE.globalS B = n)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ normalizer (B : Set G))
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    ∃ l ∈ L, ⁅B, B.map (MulAut.conj g).toMonoidHom⁆ =
      (B ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)).map
        (MulAut.conj l).toMonoidHom := by
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  obtain ⟨P, hP⟩ := offender_lifts_sylow hn hnatural hNL
    (conjugate_offender_of_normalizes hn hnatural hNL hs g hg hnon)
  obtain ⟨l, hl, he⟩ := sylow_line_orbit T hTL hLB P
  refine ⟨l, hl, ?_⟩
  rw [commutator_eq_of_induced_eq hg ((map_subtype_le _).trans hLB) hP,
    (hnatural.sylow_fixed_geometry P).2, he]

/-- Pull back the one-sided action to B and then conjugate its fixed line
forward. This is the literal line identification in source 6.1.14(5). -/
theorem inverse_conjugate_commutator_line
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hs : ChapterE.globalS B = n)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (g : G) (hg : B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    ∃ x : G, ⁅B.map (MulAut.conj g).toMonoidHom, B⁆ =
      (B ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)).map
        (MulAut.conj x).toMonoidHom := by
  obtain ⟨l, _, he⟩ := conjugate_commutator_line_of_normalizes hn hnatural hNL hs T hTL
    g⁻¹ (fusion_inverse_normalizes hg) (fusion_inverse_noncentralizing hnon)
  have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) he
  have hb := fusion_map_conj_inverse B g⁻¹
  simp only [inv_inv] at hb
  rw [map_commutator, hb, fusion_map_conj_mul] at hh
  exact ⟨g * l, hh⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
