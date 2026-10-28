module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12
public import Theory.Mathieu.M12.ExceptionalParabolics.AmalgamAutomorphisms.Bound
public import Theory.Mathieu.M12.ExceptionalParabolics.AmalgamAutomorphisms.OuterAction
public import Theory.GroupTheory.Amalgam.AutomorphismTransport

/-!
# The marked M₁₂ automorphism group in the Goldschmidt extension step

The actual outer overlap has order 128 and acts faithfully on the inner
M₁₂ amalgam. The compatible-automorphism upper bound therefore makes this
action bijective. Transport through the source's existing marked comparison
identifies the same action on its literal common Borel and parabolics.
In particular the Borel inside the actual abstract Aut(M₁₂) acts faithfully
and exhausts these compatible automorphisms, with its original action on
every endpoint element.

The embedded inner overlap has index two in the outer overlap, so an
intermediate subgroup is either that inner overlap or the entire outer
overlap. These are the two extension sizes in Goldschmidt, Automorphisms of
trivalent graphs, §3.8, supplying the model-side step for Aschbacher--Smith
F.1.12, cases (12)--(13), printed p.263. Classification and normal-base
reconstruction are separate source obligations.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt
open Theory.GroupTheory Sporadic.Mathieu
namespace MathieuExtensions


/-- Compatible automorphisms transport through an already marked amalgam isomorphism. -/
def amalgamAutEquiv {L B R L' B' R' : Type*}
    [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : RankTwoAmalgam.Iso α β) :
    RankTwoAmalgam.Iso α α ≃* RankTwoAmalgam.Iso β β :=
  RankTwoAmalgam.automorphismConjEquiv e

/-- The concrete order-128 outer overlap exhausts the inner compatible automorphisms. -/
theorem concrete_outer_action_bijective : Function.Bijective M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.outerOverlapAction := by
  apply M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.outerOverlapAction_injective.bijective_of_nat_card_le
  rw [M12ExceptionalExtension.SecondCoordinates.card_overlap
    M12ExceptionalExtension.innerModel]
  exact M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.card_amalgamAut_le

/-- The actual outer-overlap action preserves multiplication of compatible automorphisms. -/
def concreteOuterActionHom : M12ExceptionalExtension.overlap →*
    RankTwoAmalgam.Iso M12SmallPair.ExceptionalParabolics.amalgam
      M12SmallPair.ExceptionalParabolics.amalgam where
  toFun := M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.outerOverlapAction
  map_one' := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change M12ExceptionalExtension.automorphismEquiv 1 (x : M12) = (x : M12)
      rw [map_one]
      rfl
  map_mul' s t := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change M12ExceptionalExtension.automorphismEquiv (s.val * t.val) (x : M12) =
        M12ExceptionalExtension.automorphismEquiv s.val
          (M12ExceptionalExtension.automorphismEquiv t.val (x : M12))
      rw [map_mul]
      rfl

/-- The concrete outer overlap is the full group of compatible inner-amalgam automorphisms. -/
def concreteOuterActionEquiv : M12ExceptionalExtension.overlap ≃*
    RankTwoAmalgam.Iso M12SmallPair.ExceptionalParabolics.amalgam
      M12SmallPair.ExceptionalParabolics.amalgam :=
  MulEquiv.ofBijective concreteOuterActionHom concrete_outer_action_bijective

/-- The exact source-model amalgam has at most 128 compatible automorphisms. -/
theorem card_source_amalgamAut_le :
    Nat.card (RankTwoAmalgam.Iso MathieuTwelve.amalgam MathieuTwelve.amalgam) ≤ 128 := by
  rw [Nat.card_congr (amalgamAutEquiv MathieuTwelve.concreteIso).toEquiv]
  exact M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.card_amalgamAut_le

/-- The actual source Borel in Aut(M₁₂), identified with the literal outer overlap. -/
def outerBorelEquiv : AutMathieuTwelve.autB ≃* M12ExceptionalExtension.overlap :=
  AutMathieuTwelve.ambientIso.middle.symm.trans AutMathieuTwelve.concreteIso.middle

private theorem outerBorelEquiv_action (b : AutMathieuTwelve.autB) :
    M12ExceptionalExtension.automorphismEquiv (outerBorelEquiv b : M12ExceptionalExtension.Carrier) =
      (b : MulAut M12) := by
  exact congrArg (fun a : AutMathieuTwelve.autB => (a : MulAut M12))
    (AutMathieuTwelve.ambientIso.middle.apply_symm_apply b)

/-- The action on the literal inner source amalgam of its outer source Borel. -/
def outerBorelAction (b : AutMathieuTwelve.autB) :
    RankTwoAmalgam.Iso MathieuTwelve.amalgam MathieuTwelve.amalgam :=
  (amalgamAutEquiv MathieuTwelve.concreteIso).symm
    (M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.outerOverlapAction (outerBorelEquiv b))

theorem outerBorelAction_injective : Function.Injective outerBorelAction :=
  (amalgamAutEquiv MathieuTwelve.concreteIso).symm.injective.comp
    (M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.outerOverlapAction_injective.comp outerBorelEquiv.injective)

/-- Every compatible automorphism of the source M₁₂ amalgam is induced by this actual Borel. -/
theorem outerBorelAction_bijective : Function.Bijective outerBorelAction :=
  (amalgamAutEquiv MathieuTwelve.concreteIso).symm.bijective.comp
    (concrete_outer_action_bijective.comp outerBorelEquiv.bijective)

/-- The source action on the first endpoint is the original abstract automorphism. -/
theorem outerBorelAction_left_apply (b : AutMathieuTwelve.autB) (x : MathieuTwelve.P 0) :
    ((outerBorelAction b).left x : M12) = (b : MulAut M12) x := by
  change M12ExceptionalExtension.automorphismEquiv
    (outerBorelEquiv b : M12ExceptionalExtension.Carrier) x = _
  rw [outerBorelEquiv_action]

/-- The source common Borel retains its original action and inclusion marking. -/
theorem outerBorelAction_middle_apply (b : AutMathieuTwelve.autB) (x : MathieuTwelve.B) :
    ((outerBorelAction b).middle x : M12) = (b : MulAut M12) x := by
  change M12ExceptionalExtension.automorphismEquiv
    (outerBorelEquiv b : M12ExceptionalExtension.Carrier) x = _
  rw [outerBorelEquiv_action]

/-- The source action on the second endpoint is the same original abstract automorphism. -/
theorem outerBorelAction_right_apply (b : AutMathieuTwelve.autB) (x : MathieuTwelve.P 1) :
    ((outerBorelAction b).right x : M12) = (b : MulAut M12) x := by
  change M12ExceptionalExtension.automorphismEquiv
    (outerBorelEquiv b : M12ExceptionalExtension.Carrier) x = _
  rw [outerBorelEquiv_action]

/-- The source Borel acts by a homomorphism on the complete source inclusion amalgam. -/
def outerBorelActionHom : AutMathieuTwelve.autB →*
    RankTwoAmalgam.Iso MathieuTwelve.amalgam MathieuTwelve.amalgam :=
  (amalgamAutEquiv MathieuTwelve.concreteIso).symm.toMonoidHom.comp
    (concreteOuterActionHom.comp outerBorelEquiv.toMonoidHom)

/-- Full marked group identification for the source M₁₂ extension step. -/
def outerBorelActionEquiv : AutMathieuTwelve.autB ≃*
    RankTwoAmalgam.Iso MathieuTwelve.amalgam MathieuTwelve.amalgam :=
  MulEquiv.ofBijective outerBorelActionHom outerBorelAction_bijective

/-- The original Sylow subgroup has index two in the actual outer overlap. -/
theorem inner_overlap_index : M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range.index = 2 := by
  have hc : Nat.card M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range = 64 := by
    rw [MonoidHom.range_eq_map]
    rw [Subgroup.card_map_of_injective M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding_injective,
      Subgroup.card_top]
    exact M12SmallPair.card_sylowCandidate
  have h := M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range.card_mul_index
  rw [hc, M12ExceptionalExtension.SecondCoordinates.card_overlap
    M12ExceptionalExtension.innerModel] at h
  omega

/-- There are only two subgroups of the outer overlap containing the original inner overlap. -/
theorem intermediate_overlap_eq (H : Subgroup M12ExceptionalExtension.overlap)
    (h : M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range ≤ H) :
    H = M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range ∨ H = ⊤ := by
  have hd := Subgroup.index_dvd_of_le h
  rw [inner_overlap_index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact Or.inr (Subgroup.index_eq_one.mp he)
  · left
    apply (Subgroup.eq_of_le_of_card_ge h ?_).symm
    have hH := H.card_mul_index
    have hK := M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range.card_mul_index
    rw [he] at hH
    rw [inner_overlap_index] at hK
    omega

/-- The source inner Borel embeds in the actual Borel of Aut(M₁₂). -/
def sourceInnerBorelEmbedding : MathieuTwelve.B →* AutMathieuTwelve.autB :=
  outerBorelEquiv.symm.toMonoidHom.comp
    (M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.comp
      MathieuTwelve.concreteIso.middle.toMonoidHom)

theorem sourceInnerBorelEmbedding_injective : Function.Injective sourceInnerBorelEmbedding :=
  outerBorelEquiv.symm.injective.comp
    (M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding_injective.comp
      MathieuTwelve.concreteIso.middle.injective)

private theorem sourceInnerBorelEmbedding_outer (b : MathieuTwelve.B) :
    outerBorelEquiv (sourceInnerBorelEmbedding b) =
      M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding
        (MathieuTwelve.concreteIso.middle b) :=
  outerBorelEquiv.apply_symm_apply _

/-- The source embedding is the original inner conjugation homomorphism. -/
theorem sourceInnerBorelEmbedding_apply (b : MathieuTwelve.B) :
    (sourceInnerBorelEmbedding b : MulAut M12) = MulAut.conj (b : M12) := by
  have h := outerBorelEquiv_action (sourceInnerBorelEmbedding b)
  rw [sourceInnerBorelEmbedding_outer] at h
  change M12ExceptionalExtension.automorphismEquiv
    (M12ExceptionalExtension.innerModel.embedding (b : M12)) =
      (sourceInnerBorelEmbedding b : MulAut M12) at h
  exact h.symm.trans (M12ExceptionalExtension.automorphismEquiv_embedding b)

/-- The source inner action keeps the original first endpoint and conjugation convention. -/
theorem source_inner_action_left (b : MathieuTwelve.B) (x : MathieuTwelve.P 0) :
    ((outerBorelAction (sourceInnerBorelEmbedding b)).left x : M12) =
      (b : M12) * x * (b : M12)⁻¹ := by
  rw [outerBorelAction_left_apply, sourceInnerBorelEmbedding_apply]
  rfl

/-- The source inner action keeps the original common-Borel conjugation. -/
theorem source_inner_action_middle (b x : MathieuTwelve.B) :
    ((outerBorelAction (sourceInnerBorelEmbedding b)).middle x : M12) =
      (b : M12) * x * (b : M12)⁻¹ := by
  rw [outerBorelAction_middle_apply, sourceInnerBorelEmbedding_apply]
  rfl

/-- The source inner action keeps the original second endpoint and conjugation convention. -/
theorem source_inner_action_right (b : MathieuTwelve.B) (x : MathieuTwelve.P 1) :
    ((outerBorelAction (sourceInnerBorelEmbedding b)).right x : M12) =
      (b : M12) * x * (b : M12)⁻¹ := by
  rw [outerBorelAction_right_apply, sourceInnerBorelEmbedding_apply]
  rfl

private theorem sourceInnerBorelEmbedding_range_map :
    sourceInnerBorelEmbedding.range.map outerBorelEquiv.toMonoidHom =
      M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range := by
  ext x
  constructor
  · rintro ⟨b, ⟨s, rfl⟩, rfl⟩
    change outerBorelEquiv (sourceInnerBorelEmbedding s) ∈
      M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range
    rw [sourceInnerBorelEmbedding_outer]
    exact ⟨MathieuTwelve.concreteIso.middle s, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨sourceInnerBorelEmbedding (MathieuTwelve.concreteIso.middle.symm s),
      ⟨MathieuTwelve.concreteIso.middle.symm s, rfl⟩, ?_⟩
    change outerBorelEquiv
      (sourceInnerBorelEmbedding (MathieuTwelve.concreteIso.middle.symm s)) =
        M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding s
    rw [sourceInnerBorelEmbedding_outer, MathieuTwelve.concreteIso.middle.apply_symm_apply]

/-- The actual source inner Borel has index two in the source Borel of Aut(M₁₂). -/
theorem source_inner_borel_index : sourceInnerBorelEmbedding.range.index = 2 := by
  rw [← sourceInnerBorelEmbedding.range.index_map_equiv outerBorelEquiv]
  change (sourceInnerBorelEmbedding.range.map outerBorelEquiv.toMonoidHom).index = 2
  rw [sourceInnerBorelEmbedding_range_map]
  exact inner_overlap_index

/-- The source normal-extension image has exactly the inner or full-outer Borel alternative. -/
theorem source_intermediate_borel_eq (H : Subgroup AutMathieuTwelve.autB)
    (h : sourceInnerBorelEmbedding.range ≤ H) :
    H = sourceInnerBorelEmbedding.range ∨ H = ⊤ := by
  have hm : M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.innerOverlapEmbedding.range ≤
      H.map outerBorelEquiv.toMonoidHom := by
    rw [← sourceInnerBorelEmbedding_range_map]
    exact Subgroup.map_mono h
  rcases intermediate_overlap_eq (H.map outerBorelEquiv.toMonoidHom) hm with he | he
  · left
    apply Subgroup.map_injective (f := outerBorelEquiv.toMonoidHom) outerBorelEquiv.injective
    exact he.trans sourceInnerBorelEmbedding_range_map.symm
  · right
    apply Subgroup.map_injective (f := outerBorelEquiv.toMonoidHom) outerBorelEquiv.injective
    rw [Subgroup.map_top_of_surjective _ outerBorelEquiv.surjective]
    exact he

end MathieuExtensions
end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt
