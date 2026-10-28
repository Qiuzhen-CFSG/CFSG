module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction.FiveNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction.QuotientLift
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveNormalAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

public import Theory.GroupTheory.ElementaryThompsonRelative
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# Odd actors on the actual alternating-five block

The original moved-component identity gives J(S) ≤ N(L). Restricting S
to N(L) preserves all its maximum elementary subgroups and hence J(S).
The genuine five-point module forces an odd involution in the Thompson
image: otherwise the offender theorem makes that entire image trivial,
contradicting [L,J(S)]=L. The inner Sylow four-group normalizes this image,
so its normalizer is a two-group by the finite permutation calculation.
A two-perfect actor normalizing J(S) therefore fixes the module. The
cohomology correction lifts fixation to the full block, retaining every
central two-cover and without assuming that S normalizes L.

Source: Aschbacher--Smith B.3.2(4), C.1.13(c), and15.1.21(ii), pp.83,125,1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {A : Type*} [Group A] [Finite A]
private theorem thompson_le_kernel_of_even_thompson_action
    {n : ℕ} (hn : n = 5 ∨ n = 7) (W Q : Subgroup A) [W.Normal] [IsElementaryAbelian 2 W]
    (hWQ : W ≤ Q) (f : A →* Equiv.Perm (Fin n))
    (hker : f.ker = centralizer (W : Set A))
    (E : W ≃* Multiplicative (BinaryPermutation.core (Fin n)))
    (hE : ∀ a w, (E (MulAut.conjNormal a w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin n) (f a) (E w).toAdd)
    (heven : (elementaryAbelianMaxJ Q).map f ≤ alternatingGroup (Fin n)) :
    elementaryAbelianMaxJ Q ≤ f.ker := by
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hk : q.ker = centralizer (W : Set A) := by
    rw [MonoidHom.ker_rangeRestrict,hker]
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin n) :=
    LinearEquiv.ofBijective (E.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) E.bijective
  have he (a : f.range) (w : Additive W) :
      e (ρ a w) = BinaryPermutation.coreRepresentation (Fin n) a.val (e w) := by
    obtain ⟨a,rfl⟩ := hq a
    have hconj : (ρ (q a) w).toMul = MulAut.conjNormal a w.toMul :=
      Subtype.ext (NormalElementaryQuotient.representation_apply W q hq hk a w)
    change (E (ρ (q a) w).toMul).toAdd =
      BinaryPermutation.coreRepresentation (Fin n) (f a) (E w.toMul).toAdd
    rw [hconj,hE]
  apply sSup_le
  intro B hB
  apply (map_eq_bot_iff B).mp
  by_contra hne
  have hne' : B.map q ≠ ⊥ := by
    intro hb
    apply hne
    have hm := congrArg (map f.range.subtype) hb
    simpa only [q,map_map,Subgroup.map_bot,MonoidHom.subtype_comp_rangeRestrict] using hm
  have hoff := Representation.NormalElementaryQuotient.maxElementary_isBestOffender
    W q hq hk Q B hWQ hB hne'
  have ho := (hoff.isOffender ρ).map_equivariant ρ
    (BinaryPermutation.coreRepresentation (Fin n)) f.range.subtype
    f.range.subtype_injective e he
  apply ChapterB.Offenders.core_offender_not_le_alternating hn ho
  have hm : (B.map q).map f.range.subtype = B.map f := by
    rw [map_map,MonoidHom.subtype_comp_rangeRestrict]
  rw [hm]
  exact (map_mono (le_sSup hB)).trans heven

/-- The actual odd actor fixes a normal A₅ block moved by the local Thompson subgroup. -/
theorem IsAlternatingBlock.normal_thompson_actor_centralizes
    (X Q Y : Subgroup A) [X.Normal] (hb : IsAlternatingBlock X 5)
    (hQ : IsPGroup 2 Q) (hWQ : (blockU X).map X.subtype ≤ Q)
    (P : Sylow 2 X) (hPQ : (P : Subgroup X).map X.subtype ≤ Q)
    (hmove : ⁅X, elementaryAbelianMaxJ Q⁆ = X)
    (hY : IsPPerfect 2 Y) (hYJ : Y ≤ normalizer (elementaryAbelianMaxJ Q : Set A)) :
    Y ≤ centralizer (X : Set A) := by
  classical
  obtain ⟨q,E,f,hf,hE,himage,_hker,hC⟩ := hb.five_normal_action X
  let W := (blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 (blockU X) := hb.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : blockU X ≃* W := (blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := j.symm.trans E
  have hF (g : A) (w : W) : (F (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (f g) (F w).toAdd := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (blockU X) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : A) * g⁻¹ = g * (((j.symm w : blockU X) : X) : A) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E (j.symm _)).toAdd = _
    rw [hh]
    exact hE g (j.symm w)
  let D := (elementaryAbelianMaxJ Q).map f
  have ho : ∃ t ∈ D, t^2=1 ∧ t ∉ alternatingGroup (Fin 5) := by
    by_contra hno
    have heven : D ≤ alternatingGroup (Fin 5) := by
      apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro B hB b hb
      by_contra hout
      let := hB.2.1
      have hp : b^2=1 := elemPow_eq_one_of_isElementaryAbelian b hb
      exact hno ⟨f b,mem_map_of_mem f ((le_sSup hB) hb),by rw [←map_pow,hp,map_one],hout⟩
    have hJker := thompson_le_kernel_of_even_thompson_action (Or.inl rfl) W Q hWQ f hC F hF heven
    have hbot : X.map f = ⊥ := by
      rw [←hmove,map_commutator,(Subgroup.map_eq_bot_iff _).mpr hJker,commutator_bot_right]
    exact ((alternatingGroup (Fin 5)).nontrivial_iff_ne_bot.mp inferInstance) (himage.symm.trans hbot)
  let a := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have ha : Function.Surjective a := q.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective ha
  have he : f.comp X.subtype = (alternatingGroup (Fin 5)).subtype.comp a := MonoidHom.ext hf
  have hR : (R : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype =
      ((P : Subgroup X).map X.subtype).map f := by
    rw [map_map,he,←map_map]
    rfl
  have hQN : Q ≤ normalizer (elementaryAbelianMaxJ Q : Set A) :=
    Q.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  have hn : (R : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype ≤
      normalizer (D : Set (Equiv.Perm (Fin 5))) := by
    rw [hR]
    exact (map_mono (hPQ.trans hQN)).trans (le_normalizer_map f)
  have hD : IsPGroup 2 D := (hQ.to_le (sSup_le fun _ hB => hB.1)).map f
  have hN := Chapter15.Section01.ConstrainedFiveAction.normalizer_isTwoGroup R D hD hn ho
  have hYN : Y.map f ≤ normalizer (D : Set (Equiv.Perm (Fin 5))) :=
    (map_mono hYJ).trans (le_normalizer_map f)
  have hyp : IsPPerfect 2 (Y.map f) := hY.of_surjective (f.subgroupMap Y) (f.subgroupMap_surjective Y)
  have hid := hyp.hom_eq_one_of_isPGroup (hN.to_le hYN) (MonoidHom.id (Y.map f))
  have hYker : Y ≤ f.ker := by
    intro y hy
    have hh := DFunLike.congr_fun hid (⟨f y,mem_map_of_mem f hy⟩ : Y.map f)
    exact congrArg Subtype.val hh
  rw [hC] at hYker
  exact hb.twoPerfect_centralizes_of_blockU_centralizes hY le_normalizer_of_normal hYker

/-- Restriction to N(L) preserves the actual Thompson subgroup; S itself
need not normalize the block. -/
theorem IsAlternatingBlock.thompson_actor_centralizes
    (L S Y : Subgroup A) (hb : IsAlternatingBlock L 5) (hS : IsPGroup 2 S)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    (hmove : ⁅L, elementaryAbelianMaxJ S⁆ = L)
    (hY : IsPPerfect 2 Y) (hYL : Y ≤ normalizer (L : Set A))
    (hYJ : Y ≤ normalizer (elementaryAbelianMaxJ S : Set A)) :
    Y ≤ centralizer (L : Set A) := by
  let N := normalizer (L : Set A)
  let X := L.subgroupOf N
  let Q := S.subgroupOf N
  let R := S ⊓ N
  have hJN : elementaryAbelianMaxJ S ≤ N :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  have hJR : elementaryAbelianMaxJ S ≤ R := le_inf (sSup_le fun _ hB => hB.1) hJN
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq R S inf_le_left
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S R hJR
  have horder := le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ R = elementaryAbelianMaxJ S :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hJmap : (elementaryAbelianMaxJ Q).map N.subtype = elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
      subgroupOf_map_subtype]
    exact hJeq
  have hJsub : elementaryAbelianMaxJ Q = (elementaryAbelianMaxJ S).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hJmap,map_subgroupOf_eq_of_le hJN]
  let : X.Normal := L.normal_in_normalizer
  let e : X ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let P' := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP' : (P' : Subgroup X).map X.subtype ≤ Q := by
    rintro z ⟨x,⟨l,hl,rfl⟩,rfl⟩
    exact hPS (mem_map_of_mem L.subtype hl)
  have hWQ : (blockU X).map X.subtype ≤ Q :=
    (map_mono (blockU_le_core.trans (pCore_isPGroup.le_sylow_of_normal P'))).trans hP'
  have hmove' : ⁅X, elementaryAbelianMaxJ Q⁆ = X := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer,hJmap,hmove]
  have hY' : IsPPerfect 2 (Y.subgroupOf N) := hY.of_surjective
    (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  have hYJ' : Y.subgroupOf N ≤ normalizer (elementaryAbelianMaxJ Q : Set N) := by
    rw [hJsub,←subgroupOf_normalizer_eq hJN]
    exact subgroupOf_mono N hYJ
  have hc := (hb.of_mulEquiv e.symm).normal_thompson_actor_centralizes X Q
    (Y.subgroupOf N) hS.comap_subtype hWQ P' hP' hmove' hY' hYJ'
  intro y hy l hl
  exact congrArg N.subtype (hc (show (⟨y,hYL hy⟩ : N) ∈ Y.subgroupOf N from hy)
    ⟨l,L.le_normalizer hl⟩ hl)
end CFSG.Quasithin.ChapterC
