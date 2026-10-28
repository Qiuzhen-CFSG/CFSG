module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Hall
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry
public import Theory.SpecificGroups.RankTwoCoreSolvableSylow
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Cartan placement before outside-component natural recognition

The paired overlap is solvable by its actual rank-one component model.
The SL3 and Sp4 solvable Sylow-overgroup theorems then put H intersect L
in the normalizer of the original T intersect L. Its odd subgroups extend
to source Cartans by Hall containment. The full torus quotient proves
that A intersect L is abelian, without a hypothesis on all of A.

This uses the original chosen-natural coordinates on L. It does not use
CommonCore.NaturalQuotientMarking, which is downstream of 11.3.5.
CartanPlane applies the result to the literal Hall prime torsion. The
model-indexed inner-Sylow theorem also supports FieldCoprime before the
model exponent is identified with the generation minimum.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Solvability of the overlap places its intersection with L in the
normalizer of the original inner Sylow. -/
theorem solvable_overlap_normalizes_inner_sylow
    (hTH : (T : Subgroup G) ≤ H)
    (hsolv : Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
    H ⊓ L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  let B := H.subgroupOf L
  let j : B →* (H ⊓ normalizer (L : Set G) : Subgroup G) :=
    { toFun x := ⟨x.val.val,x.property,L.le_normalizer x.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let := hsolv
  have hs : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := j) (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (H ⊓ normalizer (L : Set G) : Subgroup G) => (z : G)) he)
  have hPB : (P : Subgroup L) ≤ B := by
    rw [hP]
    exact comap_mono hTH
  have hn : B ≤ normalizer (P : Set L) := by
    rcases halt with ⟨F,_,_,hcard,⟨e⟩⟩ | ⟨F,_,_,hcard,⟨e⟩⟩
    · exact solvable_overgroup_normalizes_of_slThree_twoCore_quotient
        (by have := S.nonbinary; omega) hcard e P B hs hPB
    · exact solvable_overgroup_normalizes_of_spFour_twoCore_quotient
        (by have := S.nonbinary; omega) hcard e P B hs hPB
  have hm := (map_mono hn).trans ((P : Subgroup L).le_normalizer_map L.subtype)
  rw [hP,subgroupOf_map_subtype,subgroupOf_map_subtype] at hm
  simpa only [inf_comm] using hm

/-- Extend an odd subgroup of the original Sylow normalizer to a source
Cartan, retaining the literal subgroup and the full torus quotient. -/
theorem odd_subgroup_in_cartan (c : Coordinates D S.field)
    (A : Subgroup G) (ho : Odd (Nat.card A)) (hA : A ≤ cartanNormalizer T L) :
    ∃ X : Subgroup G, IsCartan T L X ∧ A ≤ X := by
  let N := cartanNormalizer T L
  have hquot : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := c.cartanNormalizerQuotientEquiv.toMonoidHom)
      c.cartanNormalizerQuotientEquiv.injective
  let : Group.IsNilpotent (pCore 2 N) := pCore_isPGroup.isNilpotent
  have hsolv : Group.IsSolvable N :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 N)).mpr ⟨inferInstance,hquot⟩
  obtain ⟨X,hAX,hXN,hX⟩ := OddHall.exists_hall_containing_odd N A hsolv hA ho
  exact ⟨X,⟨hXN,hX⟩,hAX⟩

/-- The paired rank-one overlap normalizes the original inner Sylow.
No natural marking of the outside residual is used. -/
theorem ComponentSeed.paired_linear_inner_sylow_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
    H ⊓ L ≤ cartanNormalizer T L := by
  rw [cartanNormalizer_eq_intersection_normalizer]
  exact le_inf inf_le_right (solvable_overlap_normalizes_inner_sylow h.outside.1.1.2
    (s.paired_linear_overlap_solvable_of_model h pr hc hs hn hf hm) halt)

/-- Specialization to the original generation minimum. -/
theorem ComponentSeed.paired_linear_inner_sylow (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
    H ⊓ L ≤ cartanNormalizer T L := by
  have hf : 0 < ChapterE.generationParameter H := by
    have := degree_le_parameter h pr hc hs
    have := S.nonbinary
    omega
  exact s.paired_linear_inner_sylow_of_model h pr hc hs hn hf hm halt

/-- The actual odd intersection embeds in a source Cartan, hence in the
full two-coordinate torus over the original field. -/
theorem ComponentSeed.paired_linear_odd_intersection_cartan (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (c : Coordinates D S.field) (A : Subgroup G) (hAH : A ≤ H) (ho : Odd (Nat.card A)) :
    ∃ X : Subgroup G, IsCartan T L X ∧ A ⊓ L ≤ X :=
  odd_subgroup_in_cartan c (A ⊓ L) (ho.of_dvd_nat (card_dvd_of_le inf_le_left))
    ((inf_le_inf_right L hAH).trans (s.paired_linear_inner_sylow h pr hc hs hn hm halt))

/-- Abelianness is proved on the odd intersection needed for the actual
prime torsion, without assuming that the whole Hall subgroup is abelian. -/
theorem ComponentSeed.paired_linear_odd_intersection_abelian (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (c : Coordinates D S.field) (A : Subgroup G) (hAH : A ≤ H) (ho : Odd (Nat.card A)) :
    IsMulCommutative (A ⊓ L : Subgroup G) := by
  obtain ⟨X,hX,hAX⟩ := s.paired_linear_odd_intersection_cartan h pr hc hs hn hm halt c A hAH ho
  let f := (c.cartanTorusEquiv hX).toMonoidHom.comp (inclusion hAX)
  have hf : Function.Injective f := (c.cartanTorusEquiv hX).injective.comp (inclusion_injective hAX)
  exact .of_comm fun a b => hf (by simp only [map_mul,mul_comm])

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
