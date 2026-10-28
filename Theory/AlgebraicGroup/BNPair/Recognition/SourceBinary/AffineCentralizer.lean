module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryElementaryExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.OddCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.CentralizerSections
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Global Cartan fixed sections on the exceptional affine hexagon

On an affine nine-point endpoint the full odd Cartan centralizes the
root actor, hence every Weyl conjugate of that root. A nonbinary linear
opposite actor supplies a nonidentity Cartan element acting without fixed
points on its root. Normalization by N transports this statement to every
root of the opposite type.

On the hexagon the unique five-root coordinates therefore give an exact
two-root product for the Cartan centralizer in the canonical remainder.
It has order 64 and Frattini index at most 16. Coprime decomposition and
the actual exceptional index two identify its intersection with the true
panel kernel as a group of order 32. This smaller group is invariant under
the root actor without (2B). The source reflection acts nontrivially: the
index-two kernel meets an order-eight root nontrivially, and the reflection
moves that intersection into a disjoint root.

Source: Fong--Seitz I (2B), (5I), printed pp.9,31--34. This supplies the
literal centralizer section for the subsequent solvable-module argument;
it does not yet exclude the affine branch or select all seven rows.
BinaryAffineCentralizer transports the section to the original full
endpoint and applies it to the literal Chapter 12 pair.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The entire source Cartan fixes every root of the affine endpoint type. -/
theorem affine_cartan_centralizes_all_roots (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (w : Weyl Q) :
    rootAt Q split j w ≤ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) := by
  have hU : simpleRoot Q split j ≤ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) :=
    le_sup_left.trans (le_centralizer_iff.mp
      (torus_centralizes_rankOne_of_affine Q split j hs hp hg))
  let n := representative w
  have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hU
  change rootAt Q split j w ≤ rightConjugate
    (centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
  rwa [rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer _
    (torus_normalizes n))] at hh

/-- A nonbinary linear actor makes the full Cartan fixed-point-free on each of its roots. -/
theorem linear_cartan_all_roots_fixedFree
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (i : Fin 2) (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
  let A := (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)
    rw [rankOne_cartan_card Q split i hK μ s]
    omega)
  obtain ⟨t,ht⟩ := exists_ne (1 : A)
  have htne : (t : X ⧸ Q.D) ≠ 1 := fun he => ht (Subtype.ext he)
  have hf := rankOne_cartan_root_fixedFree Q split i hK μ s
    t.property.1 t.property.2 htne
  have hH : simpleRoot Q split i ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    exact hf.le ⟨hu.1,mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hu.2 _ t.property.1).symm⟩
  let n := representative w
  have hh := congrArg (fun C => rightConjugate C (n : X ⧸ Q.D)) hH
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer _ (torus_normalizes n))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  rwa [hb] at hh

/-- A degree-nine solvable panel has a non-elementary order-eight root. -/
theorem solvable_nine_root_frattini_bound (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j)) (hp : Nat.card (Panel Q j) = 9) :
    Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j)) ≤ 4 := by
  let A := simpleRoot Q split j
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  have hnon : frattini A ≠ ⊥ := fun hz =>
    simpleRoot_not_elementary_of_solvable_nine Q split j hs hp
      ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hz)
  have hPhi := (frattini A).one_lt_card_iff_ne_bot.mpr hnon
  have hc : Nat.card A = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card A at he
    omega
  have he := (frattini A).index_mul_card
  rw [hc] at he
  change (frattini A).index ≤ 4
  nlinarith

/-- The literal two-root centralizer product, its order and its Frattini bound. -/
theorem affine_hexagon_cartan_centralizer
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    let C := simpleRemainder Q split j ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))
    (C : Set (X ⧸ Q.D)) =
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) ∧
      Nat.card C = 64 ∧ Nat.card (C ⧸ frattini C) ≤ 16 := by
  let H := Q.tits.B ⊓ Q.tits.N
  let C := simpleRemainder Q split j ⊓ centralizer (H : Set (X ⧸ Q.D))
  have hfree := linear_cartan_all_roots_fixedFree Q split hF i hK μ s
  have hfix := affine_cartan_centralizes_all_roots Q split j hs hp hg
  have hprod := radical_centralizer_product Q split hm i j hij H le_rfl hfree hfix
  change (C : Set (X ⧸ Q.D)) = _ at hprod
  have hcard : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  let B := rootAt Q split j (Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let f : B × D → C := fun z => ⟨(z.1 : X ⧸ Q.D)*z.2, by
    rw [← SetLike.mem_coe,hprod]
    exact ⟨_,z.1.property,_,z.2.property,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b,d⟩ ⟨b',d'⟩ he
      have he' : (b : X ⧸ Q.D)*d = (b' : X ⧸ Q.D)*d' := congrArg Subtype.val he
      have hh : ((1 : simpleRoot Q split i),b,(1 : rootAt Q split i (Q.simple j*Q.simple i)),d,
          (1 : rootAt Q split i (Q.simple j))) = (1,b',1,d',1) := by
        apply (radicalCoordinates Q split hm i j hij).injective
        apply Subtype.ext
        simpa only [radicalCoordinates_apply,coe_one,one_mul,mul_one] using he'
      exact Prod.ext (congrArg (fun z => z.2.1) hh) (congrArg (fun z => z.2.2.2.1) hh)
    · intro x
      have hx := x.property
      rw [← SetLike.mem_coe,hprod] at hx
      obtain ⟨b,hb,d,hd,he⟩ := hx
      exact ⟨(⟨b,hb⟩,⟨d,hd⟩),Subtype.ext he⟩
  refine ⟨hprod,?_,?_⟩
  · change Nat.card C = 64
    rw [← Nat.card_congr (Equiv.ofBijective f hf),Nat.card_prod]
    change Nat.card (rootAt Q split j _) * Nat.card (rootAt Q split j _) = 64
    simp only [rootAt,card_rightConjugate,hcard]
  · have hb := centralizerSection_frattini_bound Q split hm i j hij H le_rfl hfree hfix
    exact hb.trans (by
      have hh := Nat.pow_le_pow_left (solvable_nine_root_frattini_bound Q split j hs hp) 2
      norm_num at hh ⊢
      exact hh)

/-- Coprime fixed points retain the precise index-two defect in the true panel kernel. -/
theorem affine_fixed_radical_index (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    let H := Q.tits.B ⊓ Q.tits.N
    (LocalCover.radical Q split j ⊓ centralizer (H : Set (X ⧸ Q.D))).relIndex
      (simpleRemainder Q split j ⊓ centralizer (H : Set (X ⧸ Q.D))) = 2 := by
  let H := Q.tits.B ⊓ Q.tits.N
  let R := simpleRemainder Q split j
  let V := LocalCover.radical Q split j
  let C := R ⊓ centralizer (H : Set (X ⧸ Q.D))
  have hVR : V ≤ R := unipotent_inf_kernel_le_remainder Q split j
  have htwo : IsPGroup 2 R := split.isTwo.to_le inf_le_left
  let := htwo.isNilpotent
  have hcop : Nat.Coprime (Nat.card H) (Nat.card R) := by
    obtain ⟨k,hk⟩ := htwo.exists_card_eq
    rw [hk]
    exact split.odd.symm.pow_right k
  have hcomm : ⁅R,H⁆ ≤ V :=
    (commutator_mono inf_le_left (torus_le_kernel_of_affine Q split j hs hp hg)).trans
      (LocalCover.unipotent_kernel_commutator Q split j)
  have hsup : V ⊔ C = R := by
    apply le_antisymm (sup_le hVR inf_le_left)
    nth_rw 1 [eq_commutator_sup_centralizer_of_solvable_coprime R H
      ((le_inf (inf_le_left.trans split.normalizes)
        (torus_normalizes_unipotentConjugate split (Q.simple j))).trans
          inf_normalizer_le_normalizer_inf) inferInstance hcop]
    exact sup_le_sup hcomm le_rfl
  have hn : R ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans
      (LocalCover.radical_parabolic_normalizes Q split j)
  let : (V.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hn
  have he := relIndex_sup_left (C.subgroupOf R) (V.subgroupOf R)
  rw [← subgroupOf_sup hVR (show C ≤ R from inf_le_left),hsup,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show C ≤ R from inf_le_left)] at he
  have hi : V.relIndex R = 2 := by
    rcases BinaryPanel.remainder_index_cases Q split j hp (Or.inr hg) with hr | hr
    · omega
    · exact hr.2.1
  have hiC : V.relIndex C = 2 := he ▸ hi
  have hVC : V ⊓ C = V ⊓ centralizer (H : Set (X ⧸ Q.D)) := by
    change V ⊓ (R ⊓ centralizer (H : Set (X ⧸ Q.D))) = _
    rw [← inf_assoc,inf_eq_left.mpr hVR]
  change (V ⊓ centralizer (H : Set (X ⧸ Q.D))).relIndex C = 2
  rw [←hVC,inf_relIndex_right]
  exact hiC

/-- The true kernel centralizer is an invariant section even on the defective branch. -/
@[expose] def affineFixedSection (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    RootSection Q split j where
  numerator := LocalCover.radical Q split j ⊓
    centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))
  le_radical := inf_le_left.trans (unipotent_inf_kernel_le_remainder Q split j)
  normalized :=
    (le_inf ((rankOne_le_parabolic Q split j).trans
        (LocalCover.radical_parabolic_normalizes Q split j))
      ((le_centralizer_iff.mp (torus_centralizes_rankOne_of_affine Q split j hs hp hg)).trans
        (centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))).le_normalizer)).trans
          inf_normalizer_le_normalizer_inf
  denominator := ⊥
  invariant _ := map_bot _

/-- The true kernel section has order 32, rather than the remainder centralizer order 64. -/
theorem affine_hexagon_fixed_section_card
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Nat.card (affineFixedSection Q split j hs hp hg).numerator = 32 := by
  have hc := (affine_hexagon_cartan_centralizer Q split hF hm i j hij hK μ s hs hp hg).2.1
  let C := simpleRemainder Q split j ⊓
    centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))
  let M := (affineFixedSection Q split j hs hp hg).numerator
  have hMC : M ≤ C := inf_le_inf_right _ (unipotent_inf_kernel_le_remainder Q split j)
  have he := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) M C bot_le hMC
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hi : M.relIndex C = 2 := affine_fixed_radical_index Q split j hs hp hg
  rw [hi,hc] at he
  change Nat.card M = 32
  omega

/-- Reflection movement detects the action on the true kernel section without (2B). -/
theorem affine_hexagon_fixed_section_action_ne_one
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    (affineFixedSection Q split j hs hp hg).action ≠ 1 := by
  let d := affineFixedSection Q split j hs hp hg
  let A := rootAt Q split j (Q.simple i)
  let V := LocalCover.radical Q split j
  have hAR : A ≤ simpleRemainder Q split j :=
    (show A ≤ middleRoots Q split i j from le_sup_left.trans le_sup_left).trans
      (middleRoots_le_remainder Q split hm i j hij)
  have hcard : Nat.card A = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    change Nat.card (rootAt Q split j _) = 8
    rw [rootAt,card_rightConjugate]
    omega
  have hi : V.relIndex (simpleRemainder Q split j) = 2 := by
    rcases BinaryPanel.remainder_index_cases Q split j hp (Or.inr hg) with hr | hr
    · omega
    · exact hr.2.1
  have hAV : A ⊓ V ≠ ⊥ := by
    intro hz
    have hi' := relIndex_le_of_le_right (H := V) hAR (by rw [hi]; decide)
    rw [←inf_relIndex_left A V,hz,relIndex_bot_left,hcard,hi] at hi'
    omega
  intro he
  apply hAV
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,ha.2,affine_cartan_centralizes_all_roots Q split j hs hp hg _ ha.1⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  have hx : d.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x))
      (show d.action r⁻¹ = 1 by rw [he]; rfl)
    rw [d.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hxa : (s.val : X ⧸ Q.D)⁻¹*a*s.val = a := by
    have hh := congrArg Subtype.val hx
    rw [d.numeratorAction_apply] at hh
    simpa only [r,x,coe_inv,inv_inv] using hh
  have hconj : a ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [← rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq, ← hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using (show a ∈ rootAt Q split j (Q.simple i) from ha.1)
  exact mem_bot.mpr (disjoint_def.mp
    (exchanged_roots_disjoint Q split hm j i hij.symm) ha.1 hconj)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
