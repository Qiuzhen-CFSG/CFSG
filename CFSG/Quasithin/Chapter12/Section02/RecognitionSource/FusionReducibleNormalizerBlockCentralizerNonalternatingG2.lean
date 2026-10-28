module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalG2
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerOmegaSplitting
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2FixedResidual
public import Theory.Frattini.Intersection

/-!
# G₂(2) surviving-block centralizer control

The concrete G₂(2)′ residual fixer is transported to the actual block quotient.
A Sylow-normalized automorphism fixing the local residual is therefore trivial
on the quotient by O₂(L). The kernel of the literal LT action is a two-group,
so each conjugate of C_T(L) lies in O₂(LT). This is the local endpoint used by
the source’s disjoint-conjugate argument at 3.3.27. The core Frattini bound
then proves that C_T(L) is elementary abelian, and the final theorem assembles
these clauses with the actual odd moving element. The G₂ terminal
factorization and the L₃(2) branch remain with the source assembly owner
qt-d-12216-normalizer-block-centralizer.

Source: Aschbacher–Smith 3.3.25(2) and 3.3.27, printed pp.599–600.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem component_sylow (D : ChosenModule T L V) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨R, hR⟩ := (T.subtype le_sup_right).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S, (S.is_maximal' T.isPGroup'.comap_subtype ?_).symm⟩
  rintro _ ⟨r,hr,rfl⟩
  rw [hR] at hr
  exact hr

/-- The literal residual centralizer inside T lies in O₂(LT) in the G₂ row. -/
theorem g2Two_sylow_centralizer_localResidual_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) :
    (T : Subgroup G) ⊓ centralizer (blockLocalResidual T L : Set G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨S,hS⟩ := component_sylow D
  obtain ⟨m⟩ := hb.natural_model
  obtain ⟨m,hm⟩ := ChapterC.G2BlockAction.exists_aligned_model m S
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
    rw [map_embedded_pResidual, hC, blockLocalResidual_eq_sylow_fixed_blockU h D hescape hb.short]
  have hES : E ≤ centralizer (S : Set L) := by
    intro e he s hs
    apply Subtype.ext
    change s ∈ (S : Subgroup L) at hs
    rw [hS] at hs
    exact he.2 s hs
  rintro x ⟨hxT,hxC⟩
  let a := L.normalizerMonoidHom ⟨x,D.sylow_normalizes_component hxT⟩
  have haS : (S : Subgroup L).map a.toMonoidHom = S := by
    apply eq_of_le_of_card_ge ?_ (by
      have he : Nat.card ((S : Subgroup L).map a.toMonoidHom) = Nat.card (S : Subgroup L) :=
        card_map_of_injective (f := a.toMonoidHom) a.injective
      exact he.ge)
    rintro _ ⟨s,hs,rfl⟩
    rw [hS] at hs ⊢
    exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hxT hs)
      ((T : Subgroup G).inv_mem hxT)
  have haC : ∀ c ∈ (pResidual 2 C).map C.subtype, a c = c := by
    intro c hc
    apply Subtype.ext
    change x * (c : G) * x⁻¹ = c
    have hcX : (c : G) ∈ blockLocalResidual T L := by
      rw [hX]
      exact mem_map_of_mem L.subtype hc
    rw [← hxC c hcX, mul_inv_cancel_right]
  have ha := ChapterC.G2BlockAction.quotientAction_eq_one_of_centralizer_residual
    m S hm E inf_le_left hES a haS haC
  exact ChapterC.G2BlockAction.mem_core_of_joinAction_eq_one
    D.sylow_normalizes_component m ⟨x,mem_sup_right hxT⟩ ha

/-- Every Sylow-normalizer conjugate of the original Sylow centralizer lies
in the actual local two-core in the G₂ row. -/
theorem g2Two_conjugate_sylow_centralizer_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) {d : G} (hd : d ∈ normalizer (T : Set G)) :
    ((T : Subgroup G) ⊓ centralizer (L : Set G)).map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let X := blockLocalResidual T L
  have hXL : X ≤ L := (map_subtype_le _).trans inf_le_left
  have hdX : d ∈ normalizer (X : Set G) :=
    ((blockLocalInvariance_of_g2Two h D hfixed hb).1 (Or.inr hb)).1 hd
  have hdc : d ∈ normalizer (centralizer (X : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer X hdX
  apply le_trans ?_ (g2Two_sylow_centralizer_localResidual_le_core h D hescape hb)
  apply le_inf
  · have hh := map_mono (f := (MulAut.conj d).toMonoidHom)
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ T)
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp hd)
  · have hh := map_mono (f := (MulAut.conj d).toMonoidHom)
      ((inf_le_right : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G)).trans
        (centralizer_le hXL))
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp hdc)

/-- Source 3.3.27(2) in the G₂ row: disjoint conjugates and C.1.13(a)
kill the Frattini subgroup of the original Sylow centralizer. -/
theorem g2Two_sylow_centralizer_frattini_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) :
    frattini ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) = ⊥ := by
  obtain ⟨d,hd,hout⟩ := SetLike.not_le_iff_exists.mp hescape
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let f := (MulAut.conj d).toMonoidHom
  have hdis := sylow_centralizer_disjoint_conjugate h D hd hout
  have hCQ := g2Two_conjugate_sylow_centralizer_le_core h D hfixed hescape hb hd
  have hPhi : (frattini (C.map f)).map (C.map f).subtype = ⊥ := by
    apply bot_unique
    exact (le_inf
      ((frattini_image_le_of_le hCQ (isPGroup_pCoreIn 2 _)).trans
        (local_core_frattini_le_sylow_centralizer D hb.short))
      (map_subtype_le _)).trans hdis.le
  rw [frattini_image_map C f (MulAut.conj d).injective] at hPhi
  exact ((frattini C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    (((frattini C).map C.subtype).map_eq_bot_iff_of_injective (MulAut.conj d).injective |>.mp hPhi)

/-- The original Sylow centralizer is elementary abelian in the G₂ row. -/
theorem g2Two_sylow_centralizer_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) :
    IsElementaryAbelian 2 ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : Fact (IsPGroup 2 C) := ⟨T.isPGroup'.to_le inf_le_left⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (g2Two_sylow_centralizer_frattini_eq_bot h D hfixed hescape hb)

/-- The original G₂ source supplies a moving element together with all
centralizer clauses of 3.3.27, using the literal block layer and local core. -/
theorem g2Two_source_movement_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) :
    let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
    IsElementaryAbelian 2 C ∧
      ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
        ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
          ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ≤
            (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          C ⊓ C.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ ∧
          C.map (MulAut.conj d⁻¹).toMonoidHom ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  refine ⟨g2Two_sylow_centralizer_elementary h D hfixed hescape hb, ?_⟩
  obtain ⟨_,A,hA,ho,_,_,d,hd,hout,hmove,hdis⟩ :=
    source_block_movement h D hfixed hescape (Or.inr (Or.inl hb))
  exact ⟨A,hA,ho,d,hd,hout,hmove,hdis,
    g2Two_conjugate_sylow_centralizer_le_core h D hfixed hescape hb
      ((normalizer (T : Set G)).inv_mem (hA hd))⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
