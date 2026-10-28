module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerOmegaSplitting
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSixFixedResidual
/-!
# Constructing the alternating-six local residual coordinates

In an escaping configuration Ω₁Z(T) cannot centralize L. The source-module
splitting therefore supplies a Sylow-fixed element of U(L) surviving the
central quotient. All such elements map into its unique natural fixed line.
The intrinsic central-kernel comparison identifies the two-residual of
C_L(C_U(T)) with the natural-line residual, and transports it back to the
literal X=O²(C_L(Ω₁Z(T))) in LT. One conjugation of the same six-letter
quotient puts X's image on the first four letters.

Both possible orders of U(L) are covered without an identification with
the chosen Chapter 12 module V. The terminal application uses these coordinates
in FusionReducibleNormalizerBlockCentralizerAlternatingComplete.
Source: Aschbacher–Smith 3.3.25–31, printed pp.599–602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Escape forces the original central omega to be moved by L. -/
theorem omegaCenter_not_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) := by
  intro hc
  apply blockOmegaModule_not_centralizes h D hescape
  let H := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hz : Stellmacher.omegaOneCenterAmbient (P : Subgroup H) ≤
      centralizer (A : Set H) := by
    intro z hz l hl
    apply Subtype.ext
    have hzG : (z : G) ∈ omegaCenterIn (T : Subgroup G) := by
      have he : (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)).map H.subtype =
          omegaCenterIn (T : Subgroup G) := by
        rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
          Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
        rfl
      rw [← he]
      exact mem_map_of_mem H.subtype hz
    exact hc hzG l hl
  have hw := map_mono (f := H.subtype) (normalClosure_le_normal hz)
  have hcmap := map_centralizer_le_centralizer_image A H.subtype
  change (centralizer (A : Set H)).map H.subtype ≤ centralizer (A.map H.subtype : Set G) at hcmap
  rw [show A.map H.subtype = L from map_subgroupOf_eq_of_le le_sup_left] at hcmap
  exact hw.trans hcmap

/-- Sylow-fixed vectors survive the central quotient of the intrinsic block layer. -/
theorem exists_sylow_fixed_blockU_not_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    ∃ u : ChapterC.blockU L, (u.val : G) ∈ centralizer (T : Set G) ∧
      u ∉ ChapterC.blockFixed L := by
  by_contra hn
  push Not at hn
  apply omegaCenter_not_centralizes h D hescape
  apply le_centralizer_iff.mp
  rw [← inf_eq_left]
  rw [omega_local_centralizer_eq_blockU h D hescape hb,
    blockU_inf_omegaCenter_eq_sylow_fixed h D hescape hb]
  apply inf_eq_left.mpr
  intro l hl u hu
  obtain ⟨u, huU, rfl⟩ := hu.1
  have hc : u ∈ center L := hn ⟨u,huU⟩ hu.2
  exact (congrArg Subtype.val (mem_center_iff.mp hc ⟨l,hl⟩)).symm

open ChapterC.AlternatingSixBlockAction BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The natural image of the actual Sylow-fixed layer spans one nonzero line. -/
theorem alternating_six_fixed_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsAlternatingBlock L 6)
    {ρ : Actor →* MulAut (Multiplicative Vector)} (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = naturalRepresentation (Fin 6) g v.toAdd) :
    ∃ v : Vector, v ≠ 0 ∧
      (∃ u : ChapterC.blockU L, (u.val : G) ∈ centralizer (T : Set G) ∧ modulePoint m u = v) ∧
      (∀ u : ChapterC.blockU L, (u.val : G) ∈ centralizer (T : Set G) →
        modulePoint m u ∈ Submodule.span (ZMod 2) {v}) := by
  let H := L ⊔ (T : Subgroup G)
  let q := joinPermutation D.sylow_normalizes_component m hρ
  let P : Sylow 2 q.range := (T.subtype le_sup_right).mapSurjective q.rangeRestrict_surjective
  have hP : (P : Subgroup q.range).map q.range.subtype = ((T : Subgroup G).subgroupOf H).map q := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, map_map]
    rfl
  have hA : alternatingGroup (Fin 6) ≤ q.range := by
    rw [← joinPermutation_component_image D.sylow_normalizes_component m hρ]
    exact map_le_range (f := q) (H := L.subgroupOf H)
  have hf (u : ChapterC.blockU L) (hu : (u.val : G) ∈ centralizer (T : Set G)) :
      ∀ x ∈ (P : Subgroup q.range).map q.range.subtype,
        naturalRepresentation (Fin 6) x (modulePoint m u) = modulePoint m u := by
    rw [hP]
    rintro _ ⟨t,ht,rfl⟩
    rw [show naturalRepresentation (Fin 6) (q t) (modulePoint m u) =
      modulePoint m (MulAut.characteristic (ChapterC.blockU L)
        (joinAutomorphisms D.sylow_normalizes_component t) u) from
          joinPermutation_module D.sylow_normalizes_component m hρ t u]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    rw [joinAutomorphisms_blockU_coe, hu t ht, mul_inv_cancel_right]
  obtain ⟨u, hu, hnu⟩ := exists_sylow_fixed_blockU_not_fixed h D hescape hb.2.1
  have hv : modulePoint m u ≠ 0 := by
    intro he
    apply hnu
    apply (QuotientGroup.eq_one_iff u).mp
    apply m.moduleIso.injective
    exact (Multiplicative.toAdd.injective he).trans m.moduleIso.map_one.symm
  exact ⟨modulePoint m u, hv, ⟨u,hu,rfl⟩, fun w hw =>
    NaturalGeometry.fixed_vectors_le_span q.range hA P _ hv (hf u hu) _ (hf w hw)⟩

/-- The literal local residual has a first-four-letter A₄ image after one
simultaneous conjugation of the six-letter quotient. -/
theorem alternating_six_residual_image_conjugate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsAlternatingBlock L 6)
    {ρ : Actor →* MulAut (Multiplicative Vector)} (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = naturalRepresentation (Fin 6) g v.toAdd) :
    ∃ g : S, (((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (joinPermutation D.sylow_normalizes_component m hρ)).map (MulAut.conj g).toMonoidHom = K := by
  let H := L ⊔ (T : Subgroup G)
  let E := ChapterC.blockU L ⊓ (centralizer (T : Set G)).comap L.subtype
  let C := centralizer (E : Set L)
  let E₀ := (ChapterC.blockU L).map L.subtype ⊓ centralizer (T : Set G)
  have hE : E.map L.subtype = E₀ := by
    ext u
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨mem_map_of_mem L.subtype hu.1,hu.2⟩
    · rintro ⟨⟨u,hu,rfl⟩,hc⟩
      exact ⟨u,⟨hu,hc⟩,rfl⟩
  have hC : C.map L.subtype = L ⊓ centralizer (E₀ : Set G) := by
    ext l
    constructor
    · rintro ⟨l,hl,rfl⟩
      refine ⟨l.property, ?_⟩
      rw [←hE]
      rintro _ ⟨e,he,rfl⟩
      exact congrArg Subtype.val (hl e he)
    · rintro ⟨hl,hc⟩
      refine ⟨⟨l,hl⟩,?_,rfl⟩
      intro e he
      apply Subtype.ext
      apply hc
      rw [←hE]
      exact mem_map_of_mem L.subtype he
  have hX : blockLocalResidual T L = ((pResidual 2 C).map C.subtype).map L.subtype := by
    rw [map_embedded_pResidual, hC, blockLocalResidual_eq_sylow_fixed_blockU h D hescape hb.2.1]
  have hinc (R : Subgroup L) : (R.map L.subtype).subgroupOf H = R.map (inclusion (show L ≤ H from le_sup_left)) := by
    ext x
    constructor
    · rintro ⟨r,hr,he⟩
      exact ⟨r,hr,Subtype.ext he⟩
    · rintro ⟨r,hr,rfl⟩
      exact mem_map_of_mem L.subtype hr
  have hq : (joinPermutation D.sylow_normalizes_component m hρ).comp
      (inclusion (show L ≤ H from le_sup_left)) = componentPermutation m := by
    apply MonoidHom.ext
    intro l
    exact joinPermutation_component D.sylow_normalizes_component m hρ l
  rw [hX,hinc,map_map,hq]
  obtain ⟨v,hv,⟨u,hu,huv⟩,hfixed⟩ := alternating_six_fixed_line h D hescape hb m hρ
  exact centralizer_residual_image_conjugate m hρ hb.2.1 E inf_le_left v hv
    ⟨u,⟨u.property,hu⟩,huv⟩ (fun w hw => hfixed w hw.2)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
