module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.QuotientMarking
public import Theory.GroupTheory.ElementaryThompsonComponent
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Literal preliminary comparisons for 14.7.70

The span E = ⟨V₁^Y⟩ excludes Y from N_G(V), and hence from LT. This
normalizer is distinct from the book's M = N_G(L); the latter exclusion
still requires the earlier projection argument. B.2.3(3) identifies J(T)
with the Thompson subgroup of O₂(I) if it is contained there, proving that
the actual I would normalize J(T).

F.6.11 supplies compatible isomorphisms of the local plus and bang images,
including the original Sylow image. Once the plus quotient has been
recognized, the existing simultaneous marking theorem orients L₁T as the
point parabolic and YT as the line parabolic under a single isomorphism.

`SmallSubnormal` and `BangRecognition` are intermediate classification
outputs, not hypotheses of the source theorem. The B.5/14.3 witness and
F.6 alternative eliminations must still construct them. Final assembly
belongs to qt-14-07-rechoice-quotient-comparison and its Goldschmidt parent.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075; F.6.11, pp.306–307.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Subgroup Representation Chapter12.Section08 Stellmacher Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The source span already excludes the normalizer of V. This does not
identify that normalizer with the book's larger M = N_G(L). -/
theorem Y_not_le_normalizer_V (h : Geometry d c) :
    ¬ Y c ≤ normalizer (V : Set G) := by
  intro hY
  apply h.Zα_not_le
  exact (le_sup_right : c.Zα ≤ E c).trans
    (by change E c ≤ V; rw [h.span]; exact conjugateSpanBy_le (F.le_seed 1) hY)

/-- The original L and T both normalize the seed, so the same span
excludes Y from LT without any quotient identification. -/
theorem Y_not_le_LT (h : Geometry d c) :
    ¬ Y c ≤ L ⊔ (T : Subgroup G) := by
  intro hY
  apply Y_not_le_normalizer_V d c h
  apply hY.trans
  apply sup_le d.natural.chosen.normalizes
  simpa only [F.last] using F.invariant 3

omit [Finite G] in
private theorem normalizer_maxJ (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (elementaryAbelianMaxJ A : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change A.map (MulAut.conj g).toMonoidHom = A at hg
  change (elementaryAbelianMaxJ A).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, hg]

/-- B.2.3(3) on the original Sylow: if J(T) lay in the two-core of I,
then all of I would normalize the very same ambient J(T). -/
theorem I_normalizes_thompson_of_le_core
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2) :
    I c ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hQT : (I c).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := map_mono (pCore_isPGroup.le_sylow_of_normal (sylow c))
      (f := (I c).subtype)
    rw [sylow_coe, map_subgroupOf_eq_of_le (T_le_I c)] at hh
    exact hh
  have he := elementaryAbelianMaxJ_eq_of_intermediate
    (T : Subgroup G) ((I c).pCoreIn 2) hJ hQT
  rw [← he]
  exact ((I c).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (I c) (pCore 2 (I c)))).trans
      (normalizer_maxJ _)

/-- The small subnormal subgroup required by the comparison on printed
p.1075. Its carrier is a subgroup of the actual plus quotient. Producing
this witness from B.5.6 and 14.3.4 is a separate source obligation. -/
def SmallSubnormal : Prop :=
  ∃ K : Subgroup ((I c) ⧸ pCore 2 (I c)), K.IsSubnormal ∧
    (Nonempty (K ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (K ≃* Matrix.PSL3Two.SL) ∨
      Nonempty (K ≃* alternatingGroup (Fin 5)))

/-- The bang quotient is distinct from the plus quotient. -/
def bangMap : I c →* ((I c) ⧸ pPrimeCore 3 (I c)) :=
  QuotientGroup.mk' (pPrimeCore 3 (I c))

def bang (A : Subgroup G) : Subgroup ((I c) ⧸ pPrimeCore 3 (I c)) :=
  (A.subgroupOf (I c)).map (bangMap c)

/-- The two outputs of the nonsolvable comparison. The component is
inside the actual plus quotient, while the equivalence concerns the bang
quotient. Their comparison must still remove the prime-to-three kernel. -/
structure BangRecognition where
  equiv : ((I c) ⧸ pPrimeCore 3 (I c)) ≃* Matrix.PSL3Two.PSL
  component : Subgroup ((I c) ⧸ pCore 2 (I c))
  subnormal : component.IsSubnormal
  componentEquiv : component ≃* Matrix.PSL3Two.PSL

/-- Compatible local quotient transport from F.6.11, with the ambient I
and both of its quotient maps unchanged. -/
def localPlusBangEquiv (k : CoreFacts c) (A : Subgroup G) (hA : A ≤ group F L) :
    plus c A ≃* bang c A :=
  (RankTwoAmalgam.subgroupQuotientMapEquiv (plusMap c) (A.subgroupOf (I c))).symm.trans
    (k.triple.primeToThreeCoreLocalEquiv (A.subgroupOf (I c)) (fun _ hx => hA hx))

theorem localPlusBangEquiv_apply (k : CoreFacts c) (A : Subgroup G)
    (hA : A ≤ group F L) (a : A.subgroupOf (I c)) :
    localPlusBangEquiv c k A hA ((plusMap c).subgroupMap _ a) =
      (bangMap c).subgroupMap _ a := by
  let e := RankTwoAmalgam.subgroupQuotientMapEquiv (plusMap c) (A.subgroupOf (I c))
  have he : e.symm ((plusMap c).subgroupMap _ a) = QuotientGroup.mk' _ a :=
    e.symm_apply_eq.mpr (RankTwoAmalgam.subgroupQuotientMapEquiv_mk _ _ a).symm
  exact (congrArg (k.triple.primeToThreeCoreLocalEquiv (A.subgroupOf (I c))
    (fun _ hx => hA hx)) he).trans
      (k.triple.primeToThreeCoreLocalEquiv_mk (A.subgroupOf (I c))
        (fun _ hx => hA hx) a)

/-- In particular the two Sylow images have the same order, even before
any equality of the two cores has been proved. -/
theorem sylow_plus_card_eq_bang (k : CoreFacts c) :
    Nat.card (plus c (T : Subgroup G)) = Nat.card (bang c (T : Subgroup G)) :=
  Nat.card_congr (localPlusBangEquiv c k (T : Subgroup G) le_sup_right).toEquiv

/-- The final marking is obtained by applying the established simultaneous
marking theorem with the labels interchanged. Thus L₁T is the point vertex
and YT is the line vertex under one and the same isomorphism. -/
theorem parabolicMarking_of_plus_equiv (k : CoreFacts c)
    (e : ((I c) ⧸ pCore 2 (I c)) ≃* Matrix.PSL3Two.PSL) :
    Nonempty (ParabolicMarking c) := by
  obtain ⟨_, e, _, _, hr, hl⟩ :=
    Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.mark_goldschmidt_quotient
      (right c) (left c) k.triple.symm e
  exact ⟨⟨e, hl, hr⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
