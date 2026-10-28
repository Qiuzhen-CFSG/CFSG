module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original Chapter 12 applications of the linear-three completion inputs

The whole-reduced chosen module supplies the original rank-one input. Its
prepared linear comparison preserves m = n and n > 1. The completion in G
retains both full normalizers and their entire overlap, with ambient generation
and the source cube-in-middle witness explicit. Both orientations are allowed.

The common-normalizer action now extends to the native PSL₃ carrier, with
both endpoint equations, the whole-overlap equation and its full kernel.
The original source cubic witness also proves full ambient order and faithful
coset action. Normalization of the source S and ambient generation remain
explicit source premises. Conditional group recognition now gives the actual
PSL₃ isomorphism and IsPSL witness at the original exponent. Endpoint gluing,
production of the source premises and the terminal GlobalExit stay with the
ambient source owner.

Source: Aschbacher–Smith 5.3.2,7, pp.659–660 and F.4.49, pp.298–299,
applied to the original Chapter 12 pair on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original whole-reduced chosen module retains its original exponent,
both comparison orientations, the two full normalizers and their whole overlap.
The source owner must supply ambient generation and its cube-in-middle witness. -/
theorem rankOne_global_linear_completion_input
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (E : SourceExtension F) (e : Global.LinearCompletion.NormalizerComparison L (residual H) E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m = n ∧ 1 < m ∧
    let c := Global.LinearCompletion.normalizerCompletion L (residual H) E e hgen
    c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
    c.left.range ⊓ c.right.range = c.middle.range ∧
    ∃ u v : G, u ∈ c.left.range ∧ v ∈ c.right.range ∧
      u ∉ c.middle.range ∧ v ∉ c.middle.range ∧ u^2=1 ∧ v^2=1 ∧
      (u*v)^3 ∈ c.middle.range :=
  d.linear_full_normalizer_completion_input
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he E e hgen
    s t hs ht hsout htout hs2 ht2 hcube

/-- Apply the native cubic calculation to the literal common-normalizer
conjugation of the original Chapter 12 pair. Normalization of the source S
is the remaining local source premise; no ambient order bound is used. -/
theorem rankOne_global_linear_middle_cubic
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F) ⊕
      RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    (hS : normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (Global.sourceS L H : Set G)) :
    m = n ∧ 1 < m ∧
    match e with
    | .inl a => ∀ g : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G),
        let c := (modelCompletion F).pairCompletion ((modelCompletion F).comapIso
          (Global.LinearCompletion.transportedMiddleAction L (residual H) (Global.sourceS L H) hS a g))
        (c.left ⟨Matrix.PSL3.SmallCompletion.reflection F false,
            Matrix.PSL3.SmallCompletion.reflection_mem F false⟩ *
          c.right ⟨Matrix.PSL3.SmallCompletion.reflection F true,
            Matrix.PSL3.SmallCompletion.reflection_mem F true⟩)^3 = 1
    | .inr a => ∀ g : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G),
        let b := Global.LinearCompletion.transportedMiddleAction L (residual H)
          (Global.sourceS L H) hS a g
        ((b.left ⟨Matrix.PSL3.SmallCompletion.reflection F true,
            Matrix.PSL3.SmallCompletion.reflection_mem F true⟩).val *
          (b.right ⟨Matrix.PSL3.SmallCompletion.reflection F false,
            Matrix.PSL3.SmallCompletion.reflection_mem F false⟩).val)^3 = 1 := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse) := by
    cases e with
    | inl a => exact Or.inl ⟨a⟩
    | inr a => exact Or.inr ⟨a⟩
  have hmn := (d.linear_amalgam_blocks hi hH.1.1.2 hp F hm hF he).1
  have hm' : 1 < m := hmn.symm ▸ hn
  refine ⟨hmn,hm',?_⟩
  cases e with
  | inl a =>
    intro g
    exact Global.LinearCompletion.transportedMiddleAction_paired_cube
      L (residual H) (Global.sourceS L H) hS a hF hm' g
  | inr a =>
    intro g
    exact Global.LinearCompletion.transportedMiddleAction_reverse_cube
      L (residual H) (Global.sourceS L H) hS a hF hm' g

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The compatible original common-normalizer action extends to the concrete
native group, with both endpoint equations and the whole-overlap equation.
The original exponent and either source orientation are retained. -/
theorem rankOne_global_linear_middle_lift
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F) ⊕
      RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    (hS : normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (Global.sourceS L H : Set G)) :
    m = n ∧ 1 < m ∧
    match e with
    | .inl a => ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →* MulAut PSL(3,F),
        σ.ker = (Global.LinearCompletion.sourceMiddleAction L (residual H) (Global.sourceS L H) hS).ker ∧
        ∀ g, (∀ x, σ g (a.left x).val =
          (a.left ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).left x)).val) ∧
        (∀ b, σ g (a.middle b).val =
          (a.middle ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).middle b)).val) ∧
        (∀ y, σ g (a.right y).val =
          (a.right ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).right y)).val)
    | .inr a => ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →* MulAut PSL(3,F),
        σ.ker = (Global.LinearCompletion.sourceMiddleAction L (residual H) (Global.sourceS L H) hS).ker ∧
        ∀ g, (∀ x, σ g (a.left x).val =
          (a.left ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).left x)).val) ∧
        (∀ b, σ g (a.middle b).val =
          (a.middle ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).middle b)).val) ∧
        (∀ y, σ g (a.right y).val =
          (a.right ((Global.LinearCompletion.sourceMiddleAction L (residual H)
            (Global.sourceS L H) hS g).right y)).val) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse) := by
    cases e with
    | inl a => exact Or.inl ⟨a⟩
    | inr a => exact Or.inr ⟨a⟩
  have hmn := (d.linear_amalgam_blocks hi hH.1.1.2 hp F hm hF he).1
  have hm' : 1 < m := hmn.symm ▸ hn
  refine ⟨hmn,hm',?_⟩
  cases e with
  | inl a =>
    exact ⟨Global.LinearCompletion.nativeMiddleAction L (residual H) (Global.sourceS L H) hS a hF hm',
      Global.LinearCompletion.nativeMiddleAction_ker L (residual H) (Global.sourceS L H) hS a hF hm',
      Global.LinearCompletion.nativeMiddleAction_equations L (residual H) (Global.sourceS L H) hS a hF hm'⟩
  | inr a =>
    exact ⟨Global.LinearCompletion.nativeMiddleReverseAction L (residual H) (Global.sourceS L H) hS a hF hm',
      Global.LinearCompletion.nativeMiddleReverseAction_ker L (residual H) (Global.sourceS L H) hS a hF hm',
      Global.LinearCompletion.nativeMiddleReverseAction_equations L (residual H) (Global.sourceS L H) hS a hF hm'⟩

/-- The full ambient order follows from the literal source apartment relation. -/
theorem rankOne_global_linear_completion_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (E : SourceExtension F) (e : Global.LinearCompletion.NormalizerComparison L (residual H) E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m = n ∧ 1 < m ∧ Nat.card G = Nat.card E.carrier ∧
      Function.Injective (MulAction.toPermHom G (Completion.Vertex
        (Global.LinearCompletion.normalizerCompletion L (residual H) E e hgen))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hmn := (d.linear_amalgam_blocks hi hH.1.1.2 hp F hm hF he).1
  exact ⟨hmn,hmn.symm ▸ hn,
    Global.LinearCompletion.normalizerCompletion_card_eq L (residual H) E e hgen hF
      s t hs ht hsout htout hs2 ht2 hcube,
    Global.LinearCompletion.normalizerCompletion_action_injective L (residual H) E e hgen⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Chapter 12 row recognizes PSL₃ with m=n>1, both orientations,
and explicit source-proved generation of the original ambient group. -/
theorem rankOne_global_linear_completion_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (E : SourceExtension F) (e : Global.LinearCompletion.NormalizerComparison L (residual H) E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m=n ∧ 1<m ∧ ClassicalGroup.IsPSL G 3 (2^n) ∧ Nonempty (G ≃* PSL(3,F)) :=
  d.linear_full_normalizer_recognition
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he E e hgen
    s t hs ht hsout htout hs2 ht2 hcube
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
