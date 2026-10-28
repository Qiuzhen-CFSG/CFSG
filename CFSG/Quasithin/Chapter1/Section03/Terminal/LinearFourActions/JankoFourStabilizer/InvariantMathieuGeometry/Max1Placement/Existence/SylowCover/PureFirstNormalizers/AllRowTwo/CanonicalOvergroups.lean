module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.CoreIntersection

/-!
# The canonical join of native sixteen overgroups

The family consists of actual pure first-class elementary sixteen subgroups
containing X and excluding every conjugate of the native row-seven pair.
Conjugation by N(X) permutes this family. Its join with X lies in the canonical
point-core intersection, hence is elementary of order at most 128. At maximal
TWO-local level its full normalizer equals N(X). The final theorem applies
this equality to arbitrary radicals with the literal restriction and two-core
maps retained.

This supplies the canonical-family part of the proposed continuation of
Kleidman--Wilson (1988), Section 2.1, pp.488--489. It does not assert that the
family has two members, that the join is mixed, or that its normalizer lies in
a named native local. In particular a later mixed reduction returning another
pure group is not a discharge of the original source placement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
open ElementaryNormalizerCover
attribute [local irreducible] modelGroup matrixA matrixB

/-- The actual native family; purity and exclusion concern every element and
all ambient conjugates, not a tag attached to a finite mask list. -/
@[expose] def sixteenOvergroups (X : Subgroup Model) : Set (Subgroup Model) :=
  {Y | X ≤ Y ∧ Nat.card Y = 16 ∧ IsElementaryAbelian 2 Y ∧
    (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
    ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map (MulAut.conj g).toMonoidHom ≤ Y}

/-- Adjoining the entire family is canonical even if individual sixteens
are permuted. Including X also covers the case of an empty family. -/
@[expose] def sixteenHull (X : Subgroup Model) : Subgroup Model :=
  X ⊔ sSup (sixteenOvergroups X)

theorem sixteenHull_le_commonCore (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X) : sixteenHull X ≤ commonCore X := by
  refine sup_le (le_commonCore X hpure hno) (sSup_le ?_)
  rintro Y ⟨hXY,_,hE,hp,hn⟩
  let := hE
  exact overgroup_le_commonCore X Y hXY hp hn

/-- This join is genuinely elementary in the ambient native model. -/
theorem sixteenHull_elementary (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X) : IsElementaryAbelian 2 (sixteenHull X) := by
  let := commonCore_elementary X hcard hpure
  exact IsElementaryAbelian.of_le (sixteenHull_le_commonCore X hpure hno)

/-- Conjugation by a whole-normalizer element preserves the literal family. -/
theorem sixteenOvergroups_map (X Y : Subgroup Model)
    (hY : Y ∈ sixteenOvergroups X) (g : Model)
    (hg : g ∈ normalizer (X : Set Model)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ sixteenOvergroups X := by
  obtain ⟨hXY,hcard,hE,hp,hn⟩ := hY
  let := hE
  refine ⟨?_,?_,IsElementaryAbelian.map _,?_,no_native_pair_map Y hn g⟩
  · rw [← mem_normalizer_iff_map_conj_eq.mp hg]
    exact map_mono hXY
  · rw [card_map_of_injective (MulAut.conj g).injective,hcard]
  · rintro y ⟨z,hz,rfl⟩ hy
    exact (hp z hz (fun he => hy (by simp [he]))).trans (isConj_iff.mpr ⟨g,rfl⟩)

/-- The entire normalizer preserves the join, without selecting one sixteen. -/
theorem normalizer_le_sixteenHull_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (sixteenHull X : Set Model) := by
  apply le_normalizer_iff.mpr
  intro g hg u hu
  have hmap : (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤ sixteenHull X := by
    apply map_le_iff_le_comap.mpr
    refine sup_le ?_ (sSup_le ?_)
    · apply map_le_iff_le_comap.mp
      rw [show X.map (MulAut.conj g).toMonoidHom = X from
        mem_normalizer_iff_map_conj_eq.mp hg]
      exact le_sup_left
    · intro Y hY
      exact map_le_iff_le_comap.mp
        (le_sup_of_le_right (le_sSup (sixteenOvergroups_map X Y hY g hg)))
  exact hmap (mem_map_of_mem _ hu)

/-- Under the original maximal TWO-local hypothesis, this actual elementary
join has exactly the original whole normalizer. This does not place that
normalizer in a named local. -/
theorem maximal_normalizer_eq_sixteenHull_normalizer
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    normalizer (X : Set Model) = normalizer (sixteenHull X : Set Model) := by
  let := sixteenHull_elementary X hcard hpure hno
  have hne : sixteenHull X ≠ ⊥ := by
    intro he
    have hb : X = ⊥ := le_bot_iff.mp (he ▸ (show X ≤ sixteenHull X from le_sup_left))
    simp [hb] at hcard
  exact hmax.eq_of_le ⟨sixteenHull X,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩
    (normalizer_le_sixteenHull_normalizer X)

/-- Literal radical restriction to the canonical join normalizer, retaining
both the ambient and relative full normalizers and the actual two-core maps. -/
theorem radical_restriction_sixteenHull
    (P X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hP : P.IsPRadical 2) (hcard : 4 < Nat.card X)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    let R := sixteenHull X
    let M := normalizer (R : Set Model)
    X ≤ R ∧ IsElementaryAbelian 2 R ∧ Nat.card R ≤ 128 ∧
      IsMaximalTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  let M := normalizer (sixteenHull X : Set Model)
  have he : normalizer (X : Set Model) = M :=
    maximal_normalizer_eq_sixteenHull_normalizer X hcard hpure hno hmax
  have hNM : normalizer (P : Set Model) ≤ M := hPX.trans he.le
  have hPM : P ≤ M := P.le_normalizer.trans hNM
  have hNN := hNM.trans M.le_normalizer
  have hc := hP.normalizer_core_subgroupOf M hPM hNN
  refine ⟨le_sup_left,sixteenHull_elementary X hcard hpure hno,
    (card_le_of_le (sixteenHull_le_commonCore X hpure hno)).trans
      (commonCore_card_le X hcard hpure),(show IsMaximalTwoLocal M from he ▸ hmax),hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hc,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
