module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.EarlierModule
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.LocalFactors

/-!
# The Thompson-center geometry actually used by 15.4.19

The central-space argument uses C_E(X), where E is the Thompson omega-center.
Baumann's alpha decomposition gives its complement directly. This route does
not identify C_E(X) with the fixed part of the entire two-core omega-center,
which is a stronger statement of 15.4.12(5). It retains the original modules,
Baumann subgroup and pairs, and supplies the literal central-space consumer.
Source: Aschbacher--Smith, 15.4.19, printed pp.1162--1163, and B.2.18.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
open TwoFactors TwoFactors.SourceFactors
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M M₁ M₂ X Y : Subgroup G}

/-- The actual whole-module conclusions needed in 15.4.19. -/
structure ThompsonGeometry (T : Sylow 2 G) (M X : Subgroup G) : Prop where
  sylow : ∃ P : Sylow 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G),
    (P : Subgroup (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G)).map
      (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G).subtype =
        ChapterB.baumann (T : Subgroup G)
  moved_le_baumann : movedModule (T : Subgroup G) M X ≤ ChapterB.baumann (T : Subgroup G)
  moved_fixed : movedModule (T : Subgroup G) M X ⊓ centralizer (X : Set G) = ⊥
  disjoint : Disjoint
    (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G))
    (movedModule (T : Subgroup G) M X)
  decomposition :
    (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) ⊔
      (movedModule (T : Subgroup G) M X ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G)) =
        ChapterB.thompsonAlpha (T : Subgroup G)
  index : (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
    (ChapterB.thompsonAlpha (T : Subgroup G)) = 4

private theorem thompson_le_baumann (T : Subgroup G) :
    ChapterB.thompsonJ T 0 ≤ ChapterB.baumann T := by
  refine le_inf (ChapterB.thompsonJ_le _ _) ?_
  intro j hj a ha
  rw [ChapterB.thompsonAlpha_eq] at ha
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj |>.symm

/-- The exact alpha split suffices for the central geometry; no assertion
about the larger fixed summand is necessary. -/
theorem thompsonGeometry_of_alpha (h : Input K T M X 2)
    (hsylow : ∃ P : Sylow 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G),
      (P : Subgroup (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G)).map
        (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G).subtype =
          ChapterB.baumann (T : Subgroup G))
    (he : IsElementaryAbelian 2
      (ChapterB.thompsonAlpha (T : Subgroup G) ⊔ movedModule (T : Subgroup G) M X : Subgroup G))
    (halpha : ChapterB.thompsonAlpha (T : Subgroup G) =
      (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) ⊔
        (movedModule (T : Subgroup G) M X ⊓ centralizer (ChapterB.thompsonJ (T : Subgroup G) 0 : Set G)))
    (hcard : Nat.card (movedModule (T : Subgroup G) M X ⊓
      centralizer (ChapterB.thompsonJ (T : Subgroup G) 0 : Set G) : Subgroup G) = 4) :
    ThompsonGeometry T M X := by
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let W := movedModule (T : Subgroup G) M X
  let J := ChapterB.thompsonJ (T : Subgroup G) 0
  let S := ChapterB.baumann (T : Subgroup G)
  let C := E ⊓ centralizer (X : Set G)
  let F := W ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 2 (E ⊔ W : Subgroup G) := he
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  have hWS : W ≤ S := by
    refine le_inf hWT ?_
    intro w hw e he
    exact setLike_mul_comm (mem_sup_left he : e ∈ E ⊔ W) (mem_sup_right hw)
  have hFE : F ≤ E := le_sup_right.trans_eq halpha.symm
  have hFS : F ≤ centralizer (S : Set G) := by
    apply le_centralizer_iff.mp
    exact (show S ≤ centralizer (E : Set G) from inf_le_right).trans (centralizer_le hFE)
  have hF : W ⊓ centralizer (S : Set G) = F :=
    le_antisymm (inf_le_inf_left W (centralizer_le (thompson_le_baumann _)))
      (le_inf inf_le_left hFS)
  have hfree := EarlierModule.moved_fixed_eq_bot h
  have hd : Disjoint C W := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro w hw
    exact hfree.le ⟨hw.2,hw.1.2⟩
  have hn : F ≤ normalizer (C : Set G) := by
    apply le_trans _ (centralizer_le_normalizer (C : Set G))
    intro f hf c hc
    exact setLike_mul_comm
      (mem_sup_left hc.1 : c ∈ E ⊔ W) (mem_sup_right hf.1)
  have hCF : Nat.card (C ⊔ F : Subgroup G) = Nat.card C * 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C F hn (hd.mono_right inf_le_left)]
    exact congrArg (Nat.card C * ·) hcard
  have hi : C.relIndex E = 4 := by
    have hci := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left] at hci
    have hcE : Nat.card E = Nat.card C * 4 := by
      rw [show E = C ⊔ F from halpha]
      exact hCF
    rw [hcE] at hci
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hci
  refine ⟨hsylow, hWS, hfree, hd, ?_, hi⟩
  exact (congrArg (C ⊔ ·) hF).trans halpha.symm


/-- Original whole-module source conclusions imply every factor action input
used by the central fixed-space argument, for any subgroup of the stabilizer. -/
theorem Pair.factor_actions_thompson (p : Pair T M X) (h : Input K T M X 2)
    (earlier : ThompsonGeometry T M X) {U : Subgroup G} (hUT : U ≤ T)
    (hn : U ≤ normalizer (p.quotient.factor false : Set G)) :
    let L := p.quotient.factor
    let V := p.quotient.moduleFactor
    let E := ChapterB.thompsonAlpha (T : Subgroup G)
    let S := ChapterB.baumann (T : Subgroup G)
    let C := E ⊓ centralizer ((L false ⊔ L true : Subgroup G) : Set G)
    (∀ i, V i ≤ S) ∧ (∀ i, U ≤ normalizer (V i : Set G)) ∧
    (∀ i, V i ≠ ⊥) ∧ V false ≤ centralizer (V true : Set G) ∧
    Disjoint (V false) (V true) ∧ Disjoint C (V false ⊔ V true) ∧
    C ⊔ ((V false ⊔ V true) ⊓ centralizer (S : Set G)) = E ∧
    C.relIndex E = 4 ∧ (∀ i, V (!i) ≤ centralizer (L i : Set G)) ∧
    (V false ⊔ V true) ⊓ centralizer ((L false ⊔ L true : Subgroup G) : Set G) = ⊥ := by
  have hWS := earlier.moved_le_baumann
  have hfree := earlier.moved_fixed
  let W := movedModule (T : Subgroup G) M X
  let S := ChapterB.baumann (T : Subgroup G)
  have hjoin : p.quotient.moduleFactor false ⊔ p.quotient.moduleFactor true = W := p.module_join
  have hViW (i) : p.quotient.moduleFactor i ≤ W := by
    exact (show p.quotient.moduleFactor i ≤ p.quotient.moduleFactor false ⊔ p.quotient.moduleFactor true from by
      cases i
      · exact le_sup_left
      · exact le_sup_right).trans_eq hjoin
  have hnL := p.normalizes h.sylow_le hUT hn
  have hnormV : M ≤ normalizer (localV (T : Subgroup G) M : Set G) :=
    localV_normalized (T : Subgroup G) M
  have hVL : X ≤ normalizer (localV (T : Subgroup G) M : Set G) :=
    le_trans h.member_le hnormV
  dsimp only
  refine ⟨fun i => (hViW i).trans hWS, ?_, ?_, ?_, p.module_disjoint, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact commutator_factors_normalized ((hUT.trans h.sylow_le).trans
      hnormV) (hnL i)
  · intro i hb
    have hc := p.module_card i
    rw [hb, card_bot] at hc
    omega
  · let := h.moved_elementary
    intro a ha b hb
    exact setLike_mul_comm (hViW true hb) (hViW false ha)
  · rw [p.quotient.factor_generate h, p.module_join]
    exact earlier.disjoint
  · rw [p.quotient.factor_generate h, p.module_join]
    exact earlier.decomposition
  · rw [p.quotient.factor_generate h]
    exact earlier.index
  · intro i
    cases i
    · apply factor_centralizes_sibling_module (Y₁ := p.quotient.factor true)
      · rw [sup_comm, p.quotient.factor_generate h]
        exact hVL
      · rw [sup_comm, p.quotient.factor_generate h]
        exact p.quotient.factor_normalized h true
      · exact p.module_disjoint.symm
    · apply factor_centralizes_sibling_module (Y₁ := p.quotient.factor false)
      · rw [p.quotient.factor_generate h]
        exact hVL
      · rw [p.quotient.factor_generate h]
        exact p.quotient.factor_normalized h false
      · exact p.module_disjoint
  · rw [p.quotient.factor_generate h, p.module_join]
    exact hfree



/-- The literal same-pair application. Retaining the two Pair witnesses lets
the later Sylow argument reuse their original quotient maps and permutations. -/
theorem source_geometry_conclusions_thompson
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (earlierX : ThompsonGeometry T M₁ X) (earlierY : ThompsonGeometry T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    Conclusions (geometry pX pY) := by
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx, hM₁]
  have hm₂ : d.M₂ = M₂ := by change normalizer (d.wholeY : Set G) = M₂; rw [hy, hM₂]
  have hSX : ChapterB.baumann (d.T : Subgroup G) ≤ normalizer (d.X false : Set G) := pX.baumann false
  have hSY : ChapterB.baumann (d.T : Subgroup G) ≤ normalizer (d.Y false : Set G) := pY.baumann false
  have hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀ := le_inf (le_inf inf_le_left hSX) hSY
  have hTX : (d.T : Subgroup G) ≤ d.M₁ := hm₁.symm ▸ hX.sylow_le
  have hTY : (d.T : Subgroup G) ≤ d.M₂ := hm₂.symm ▸ hY.sylow_le
  have hgenX (i) : d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G) := by
    rw [hx]
    exact pX.factor_join_sylow hX i
  have hgenY (i) : d.Y i ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G) := by
    rw [hy]
    exact pY.factor_join_sylow hY i
  have huX : ∀ M : Subgroup G, IsMaximalTwoLocal M → d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁ := by
    simpa only [hx, hm₁, ht] using huniqueX
  have huY : ∀ M : Subgroup G, IsMaximalTwoLocal M → d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂ := by
    simpa only [hy, hm₂, ht] using huniqueY
  have hz : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G) := rfl
  have hcz : d.Z ⊓ centralizer (d.wholeX : Set G) ≠ ⊥ := by rw [hx]; exact hCZ
  have hnX₀ : d.T₀ ≤ normalizer (pX.quotient.factor false : Set G) := inf_le_left.trans inf_le_right
  have hnY₀ : d.T₀ ≤ normalizer (pY.quotient.factor false : Set G) := inf_le_right
  have haX := pX.factor_actions_thompson hX earlierX d.T₀_le_T hnX₀
  have haY := pY.factor_actions_thompson hY earlierY d.T₀_le_T hnY₀
  obtain ⟨houtX, houtY, hgeom⟩ := central_geometry_from_factor_actions d hz hZcard hcz hS
    hTX hTY (hm₁.symm ▸ hX.maximal) (hm₂.symm ▸ hY.maximal) hgenX hgenY huX huY
    (by simpa only [hm₁, hm₂] using hne) (fun side => by cases side; exact haX; exact haY)
  have hnX (i) : d.T₀ ≤ normalizer (d.X i : Set G) := by
    have hpair := pX.quotient.action
    intro t ht
    let m : M₁ := ⟨t, hX.sylow_le (d.T₀_le_T ht)⟩
    have hf : hpair.permutation m false = false := hpair.distinct
      ((hpair.conjugation m false).symm.trans (mem_normalizer_iff_map_conj_eq.mp (hnX₀ ht)))
    have hi : hpair.permutation m i = i := by
      cases i
      · exact hf
      · cases he : hpair.permutation m true
        · exact False.elim (Bool.false_ne_true ((hpair.permutation m).injective (hf.trans he.symm)))
        · rfl
    exact mem_normalizer_iff_map_conj_eq.mpr ((hpair.conjugation m i).trans (congrArg d.X hi))
  have hPs : ∃ P : Sylow 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G),
      (P : Subgroup (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G)).map
        (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G).subtype =
          ChapterB.baumann (d.T : Subgroup G) := by
    rw [hx, ht]
    exact earlierX.sylow
  obtain ⟨P, hP⟩ := hPs
  have hindices := factor_intersections_from_source_quotients d hS hnX
    (fun i => pX.quotient.factor_quotient_card i) P hP hTY houtX
  exact ⟨houtX, houtY, hgeom, hindices.1, hindices.2.1, hindices.2.2⟩

/-- Construct the raw source Geometry and prove every clause of 15.4.19,
uniformly in both factor choices, with the literal triple intersections.
The retained source assumptions are the genuine preceding 15.4.12 and 15.4.14
outputs; the actual pair and all its module/action hypotheses are constructed. -/
theorem source_lemma_15_4_19_thompson
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (earlierX : ThompsonGeometry T M₁ X) (earlierY : ThompsonGeometry T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    ∃ d : Source.Geometry G,
      d.T = T ∧ d.wholeX = X ∧ d.wholeY = Y ∧ d.M₁ = M₁ ∧ d.M₂ = M₂ ∧
      d.J = ChapterB.thompsonJ (T : Subgroup G) 0 ∧
      d.Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      d.VM₁ = localV T M₁ ∧ d.VM₂ = localV T M₂ ∧ Conclusions d := by
  obtain ⟨pX⟩ := exists_pair hX
  obtain ⟨pY⟩ := exists_pair hY
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  refine ⟨d, rfl, hx, hy, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change normalizer (d.wholeX : Set G) = M₁
    rw [hx, hM₁]
  · change normalizer (d.wholeY : Set G) = M₂
    rw [hy, hM₂]
  · exact source_geometry_conclusions_thompson hX hY pX pY earlierX earlierY hM₁ hM₂ huniqueX huniqueY hne hZcard hCZ


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
