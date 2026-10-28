module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceRadical
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionLinear
public import Theory.SpecificGroups.PSL3.RadicalPerfectNormalizer
/-!
# Completion of the binary linear source row

The source normalizer control makes the actual radical image radical in
its inner component. Projective radical-normalizer recognition then
identifies the two-core quotient of the actual secondary image with
SL₂ over the model field. The source degree is already two, so equality
with the order of SL₂(4) forces the model field to have four elements.
The full central quotient marking and the original outer torus clause
follow from the previously proved source center and prime-rank arguments.

The final disjunction retains the degree-five J₄ branch; excluding that
proper two-local remains necessary for the unconditional sieve.
Source: Aschbacher--Smith 4.3.14--16, printed pp.617--618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}
/-- Full normalizer control forces the model degree to equal two. -/
theorem SecondarySourceData.binary_linear_model_degree_two (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) : f=2 := by
  have hn2 := SecondarySourceData.binary_linear_source_degree_two s D h hn hg hf hm
  have hRI := SecondarySourceData.binary_linear_radical_le_inner s hg hf hm
  have hXI := SecondarySourceData.secondaryImage_le_componentImage s
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.normal
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let I := SecondarySourceData.componentImage s
  let X := SecondarySourceData.secondaryImage s
  let R := SecondarySourceData.radicalImage s
  let B := (X.subgroupOf I).map e.toMonoidHom
  let W := (R.subgroupOf I).map e.toMonoidHom
  let b := (subgroupOfEquivOfLe hXI).symm.trans
    ((X.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f:=b.toMonoidHom) b.surjective
  have hB : B ≠ ⊥ := by
    intro he
    have hc : Nat.card X = 1 := (Nat.card_congr b.toEquiv).trans (by change Nat.card B=1; rw [he]; simp)
    exact SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model
      (X.eq_bot_of_card_eq hc)
  have hW : W.IsPRadical 2 := by
    have hh := SecondarySourceData.inner_radical s D hRI
    refine ⟨fun he => hh.1 (((R.subgroupOf I).map_eq_bot_iff_of_injective e.injective).mp he),?_⟩
    change (normalizer (W : Set _)).pCoreIn 2 = W
    rw [show W = (R.subgroupOf I).map e.toMonoidHom from rfl,
      ←map_equiv_normalizer_eq,←map_pCoreIn_of_injective 2 _ _ e.injective]
    exact congrArg (map e.toMonoidHom) hh.2
  have hBW : B ≤ normalizer (W : Set _) := by
    rw [show W = (R.subgroupOf I).map e.toMonoidHom from rfl,←map_equiv_normalizer_eq]
    apply map_mono
    intro x hx y
    exact (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1 hx y.val
  have hWB : normalizer (W : Set _) ≤ normalizer (B : Set (PSL(3,F))) := by
    rw [show W = (R.subgroupOf I).map e.toMonoidHom from rfl,
      show B = (X.subgroupOf I).map e.toMonoidHom from rfl,
      ←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    apply map_mono
    rw [←subgroupOf_normalizer_eq hRI,←subgroupOf_normalizer_eq hXI]
    intro x hx
    exact (SecondarySourceData.localImageData s D).normalizer_control
      ⟨(show I ≤ SecondarySourceData.ambientImage s from le_sup_left.trans le_sup_left) x.property,hx⟩
  obtain ⟨a⟩ := Matrix.PSL3.LinearThree.RadicalNormalizer.projective_radical_perfect_normal_quotient
    W B hW hB hBW hWB (by omega) hF
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hcard : Nat.card (X ⧸ pCore 2 X) = 60 := by
    obtain ⟨K,_,_,hK,⟨k⟩⟩ := (SecondarySourceData.localImageData s D).secondary_model
    let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hK
    rw [Nat.card_congr (k.trans (Theory.PSL2.sl2QuotientEquiv K).symm).toEquiv,
      Atlas.card_sl_two,hK,hn2]
    norm_num
  have hc : 2^f*((2^f)^2-1)=60 := by
    rw [←hF,←Atlas.card_sl_two,←Nat.card_congr (bq.trans a).toEquiv]
    exact hcard
  by_contra he
  have hf3 : 3≤f := by omega
  have hpow : 8≤2^f := by
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hf3
  have hsq : 63 ≤ (2^f)^2-1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hpow 2) 1
  have hmul := Nat.mul_le_mul hpow hsq
  omega
/-- Full quotient recognition in the binary linear branch, including the source outer torus. -/
theorem SecondarySourceData.binary_linear_exceptional (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) :
    (n=2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      SecondarySourceData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ := by
  have hf2 := SecondarySourceData.binary_linear_model_degree_two s D h hn hg hf hm
  obtain ⟨hn2,_,hmodel⟩ := SecondarySourceData.binary_linear_degree_two_full_model s D h hn hg hf hm
  have hfour : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 := by
    simpa only [hf2,show (2:ℕ)^2=4 from rfl] using hmodel
  exact ⟨⟨hn2,hfour⟩,SecondarySourceData.exceptional_model_outer_torus s D h ⟨hn2,Or.inl hfour⟩⟩

/-- The complete linear inspection leaves only the exceptional full quotient
or the original degree-five J₄ branch. -/
theorem SecondarySourceData.exceptional_or_jankoFour (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s) :
    ((n=2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      SecondarySourceData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥) ∨
      (n=5 ∧ Nonempty (SecondarySourceData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondarySourceData.inspection_remaining_rows_after_g2 s hn hg D h with ⟨f,hf,hm⟩ | hh
  · exact Or.inl (SecondarySourceData.binary_linear_exceptional s D h hn hg hf hm)
  · exact Or.inr hh

/-- Away from degree five, the literal full-quotient exceptional conclusion is proved. -/
theorem SecondarySourceData.exceptional_of_degree_ne_five (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s) (hn5 : n≠5) :
    (n=2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      SecondarySourceData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ := by
  rcases SecondarySourceData.exceptional_or_jankoFour s D h hn hg with ⟨⟨hn2,hm⟩,ho⟩ | hh
  · exact ⟨⟨hn2,Or.inl hm⟩,ho⟩
  · exact (hn5 hh.1).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
