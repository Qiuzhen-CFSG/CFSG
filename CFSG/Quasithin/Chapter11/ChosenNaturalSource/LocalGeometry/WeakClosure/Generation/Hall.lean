module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Cartan

/-!
# Faithfulness of the original Hall actor from odd-normalizer control

A nontrivial C_B(V) contains a characteristic elementary odd-prime subgroup.
The actual Hall Frattini factorization makes it permute with T. The proved
4.4.13 escape contradicts the specialized 4.4.3 containment. This proves
faithfulness for the entire Hall subgroup, including when B moves V.
Only the nonbinary 4.4.3 specialization remains an input.

Source: Aschbacher--Smith, first paragraph of the proof of 11.2.1, p.767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- A nontrivial kernel on the unchanged V yields the precise elementary
odd actor needed by both source normalizer theorems. -/
theorem hall_kernel_escape {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let C := (centralizer (V : Set G)).subgroupOf H
  have hne : d.witness.abelianGroup ⊓ C ≠ ⊥ := by
    intro he
    apply hk
    apply _root_.eq_bot_iff.mpr
    rintro x ⟨⟨a,ha,rfl⟩,hc⟩
    have ha1 : a = 1 := mem_bot.mp (he ▸ (show a ∈ d.witness.abelianGroup ⊓ C from ⟨ha,hc⟩))
    simp only [ha1, map_one, mem_bot]
  have hTC : (T.subtype hH.1.1.2 : Subgroup H) ≤ normalizer (C : Set H) :=
    (comap_mono (S.sylow_normalizes.trans (normalizer_le_normalizer_centralizer V))).trans
      (le_normalizer_comap H.subtype)
  obtain ⟨p,A,hp,ho,hA,hAe,hAC,_,hperm⟩ :=
    exists_elementary_odd_invariant_permuting d.witness.abelian d.witness.odd
      hne hTC d.frattini d.normalizes
  have hpermG : (A.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (A.map H.subtype : Set G) := by
    have hh := congrArg (Set.image H.subtype) hperm
    rw [Set.image_mul, Set.image_mul] at hh
    change (A.map H.subtype : Set G) *
        (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) =
      (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) * (A.map H.subtype : Set G) at hh
    simpa only [map_subgroupOf_eq_of_le hH.1.1.2, Sylow.coe_coe] using hh
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  refine ⟨p,A.map H.subtype,hp,ho,
    fun hz => hA ((map_eq_bot_iff_of_injective A H.subtype_injective).mp hz),
    IsElementaryAbelian.map H.subtype,?_,hpermG,
    elementary_hall_escape D S hH hlarge hP d hp A hAe (hAC.trans inf_le_left) hpermG⟩
  apply le_inf
  · exact map_le_iff_le_comap.mpr ((hAC.trans inf_le_left).trans (d.hall_le.trans hm.le))
  · exact map_le_iff_le_comap.mpr (hAC.trans inf_le_right)

/-- Faithfulness on V follows from escape and containment for the same
actual elementary kernel; it is not assumed as a Hall-witness field. -/
theorem hall_faithful
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ := by
  by_contra hk
  obtain ⟨p,A,hp,ho,hA,he,hAC,hperm,hescape⟩ :=
    hall_kernel_escape D S hH hlarge hP d hm hk
  exact hescape (hcontrol p hp ho A hA he hAC hperm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
