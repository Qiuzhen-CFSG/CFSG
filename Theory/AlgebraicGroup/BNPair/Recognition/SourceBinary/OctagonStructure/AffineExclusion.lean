module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineFrattiniExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.FixedProducts

/-!
# Excluding the affine nine-point endpoint in a linear octagon

Opposite a nonbinary linear endpoint, the full Cartan fixes precisely the
three affine root coordinates in the octagon remainder, so its fixed group
has order 512. The true panel kernel has index two in that fixed group and
therefore order 256. Short-root separation makes its affine actor image
non-two, forcing a Frattini quotient of order at least 256. A crossed root
contains a nontrivial square in the fixed kernel, so its Frattini subgroup
is nontrivial, a contradiction.

Only reduced words of lengths at most five are used for the reflection
separation; all seven coordinates are used for the order calculation.
This removes the binary regularity exception before the regular-unitary
arguments of Fong--Seitz I (6F), printed pp.45--49. It does not itself
exclude a regular unitary endpoint. The original source and Chapter 12
applications are in BinaryAffineOctagonExclusion.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
open RootCoordinates UnitarySource HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
private theorem lengths (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple j*Q.simple i) = 2 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j) = 3 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 4 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 5 := by
  have h2 (b : Bool) := wordLength_alternatingWord Q b (n := 2) (by omega)
  have h3 (b : Bool) := wordLength_alternatingWord Q b (n := 3) (by omega)
  have h4 (b : Bool) := wordLength_alternatingWord Q b (n := 4) (by omega)
  have h5 (b : Bool) := wordLength_alternatingWord Q b (n := 5) (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using And.intro (h2 true) (And.intro (h3 true) (And.intro (h4 true) (h5 true)))
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using And.intro (h2 false) (And.intro (h3 false) (And.intro (h4 false) (h5 false)))
  · exact (hij rfl).elim

theorem cross_root_separation (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    let C := unipotentConjugate split (Q.simple j*Q.simple i)
    simpleRoot Q split j ≤ C ∧
      rootAt Q split j (Q.simple i*Q.simple j) ≤ C ∧
      Disjoint (rootAt Q split j (Q.simple i)) C := by
  have hl := lengths Q hm i j hij
  refine ⟨(simpleRoot_le_ascent_intersection Q split _ j (by rw [hl.1,hl.2.1])).trans inf_le_right,?_,?_⟩
  · apply rootAt_le_conjugate Q split
    simp only [mul_inv_rev,simple_inv,← mul_assoc]
    rw [hl.2.2.1,hl.2.2.2]
  · have hd := congrArg (fun A => rightConjugate A
        (representative (Q.simple i) : X ⧸ Q.D))
      (disjoint_iff.mp (simpleRoot_disjoint_simpleConjugate Q split j))
    rw [rightConjugate_inf,unipotentConjugate_right split _ _ _ (representative_spec _)] at hd
    apply disjoint_iff.mpr
    exact hd.trans (by
      ext x
      exact (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).map_eq_one_iff)

private theorem cross_root_le_remainder (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split j := by
  have hl := lengths Q hm j i hij.symm
  have hl' := lengths Q hm i j hij
  have h1 : Q.tits.wordLength (Q.simple i) = 1 := by
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,mul_one] using
        wordLength_alternatingWord Q false (n := 1) (by omega)
    · simpa only [alternatingWord,↓reduceIte,mul_one] using
        wordLength_alternatingWord Q true (n := 1) (by omega)
  apply rootAt_le_remainder Q split j j (Q.simple i)
  · rw [simple_inv,h1,hl.1]
  · rw [simple_inv,hl'.1,hl'.2.1]

/-- The reflection differs from every simple-root element on the actual fixed section. -/
theorem affine_fixed_reflection_ne_root (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j) :
    (affineFixedSection Q split j hs hp hg).numeratorAction ⟨s.val,s.mem_rankOne⟩ ≠
      (affineFixedSection Q split j hs hp hg).numeratorAction u := by
  let d := affineFixedSection Q split j hs hp hg
  let A := rootAt Q split j (Q.simple i)
  let V := LocalCover.radical Q split j
  have hAR : A ≤ simpleRemainder Q split j := cross_root_le_remainder Q split hm i j hij
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
  obtain ⟨a,ha,hane⟩ := (A ⊓ V).bot_or_exists_ne_one.resolve_left hAV
  let x : d.numerator := ⟨a,ha.2,affine_cartan_centralizes_all_roots Q split j hs hp hg _ ha.1⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : d.numeratorAction r⁻¹ = d.numeratorAction u⁻¹ := by
    rw [map_inv,map_inv,he]
  have hx := congrArg (fun f : MulAut d.numerator => (f x : X ⧸ Q.D)) hei
  rw [d.numeratorAction_apply,d.numeratorAction_apply] at hx
  simp only [coe_inv,inv_inv] at hx
  change (s.val : X ⧸ Q.D)⁻¹*a*s.val = (u : X ⧸ Q.D)⁻¹*a*u at hx
  have haD : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using (show a ∈ rootAt Q split j (Q.simple i) from ha.1)
  obtain ⟨hU,hD,hd⟩ := cross_root_separation Q split hm i j hij
  have haC := (unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem
    ((unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem (hU hu) (hx ▸ hD haD))
    ((unipotentConjugate split (Q.simple j*Q.simple i)).inv_mem (hU hu))
  have haC' : a ∈ unipotentConjugate split (Q.simple j*Q.simple i) := by
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using haC
  exact hane (disjoint_def.mp hd ha.1 haC')

theorem affine_fixed_action_not_two (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    ¬ IsPGroup 2 (affineFixedSection Q split j hs hp hg).numeratorAction.range := by
  let d := affineFixedSection Q split j hs hp hg
  let f := d.numeratorAction.rangeRestrict
  let R := rankOne Q split j
  let B := Q.tits.B.subgroupOf R
  let T := (Q.tits.B ⊓ Q.tits.N).subgroupOf R
  let A := (simpleRoot Q split j).subgroupOf R
  have hTK : T ≤ d.numeratorAction.ker := by
    intro t ht
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp x.property.2 _ ht)
  have hAB : A.map f = B.map f := by
    apply le_antisymm (map_mono (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)))
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨a,ha,t,ht,he⟩ := rootActor_borel_factorization Q split j r.property hr
    let a' : R := ⟨a,(show simpleRoot Q split j ≤ R from le_sup_left) ha⟩
    let t' : R := ⟨t,ht.1⟩
    have he' : r = a'*t' := Subtype.ext he
    refine ⟨a',ha,?_⟩
    rw [he',map_mul]
    have ht' : f t' = 1 := Subtype.ext (hTK ht.2)
    rw [ht',mul_one]
  intro htwo
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.numeratorAction.rangeRestrict_surjective
    rw [rankOne_borel_index Q split j,hp] at hh
    exact hh
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have htop : A.map f = ⊤ := hAB.trans (index_eq_one.mp hidx)
  have hr : f ⟨s.val,s.mem_rankOne⟩ ∈ A.map f := htop ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hr
  exact affine_fixed_reflection_ne_root Q split hm i j hij s hs hp hg u hu
    (congrArg Subtype.val he).symm

theorem affine_cross_root_square (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    ∃ x : (affineFixedSection Q split j hs hp hg).numerator,
      (x : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) ∧ x^2 ≠ 1 := by
  let A := rootAt Q split j (Q.simple i)
  let V := LocalCover.radical Q split j
  have hAR : A ≤ simpleRemainder Q split j := cross_root_le_remainder Q split hm i j hij
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
  have hi' := relIndex_le_of_le_right (H := V) hAR (by rw [hi]; decide)
  rw [←inf_relIndex_left A V,hi] at hi'
  have hc := ((A ⊓ V).subgroupOf A).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ V ≤ A from inf_le_left)).toEquiv] at hc
  change (A ⊓ V).relIndex A * Nat.card ↥(A ⊓ V) = Nat.card A at hc
  rw [hcard] at hc
  have hgt : 2 < Nat.card ↥(A ⊓ V) := by nlinarith
  obtain ⟨a,ha⟩ := affine_root_subgroup_square Q split j hs hp hg (Q.simple i)
    (A ⊓ V) inf_le_left hgt
  let x : (affineFixedSection Q split j hs hp hg).numerator :=
    ⟨a,a.property.2,affine_cartan_centralizes_all_roots Q split j hs hp hg _ a.property.1⟩
  refine ⟨x,a.property.1,?_⟩
  intro he
  exact ha (Subtype.ext (congrArg (fun z : (affineFixedSection Q split j hs hp hg).numerator => (z : X ⧸ Q.D)) he))


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
open Subgroup RootCoordinates UnitarySource HexagonStructure
open scoped Pointwise MatrixGroups
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The full Cartan fixes precisely three affine root coordinates in the octagon remainder. -/
theorem affine_octagon_cartan_fixed_card
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Nat.card (simpleRemainder Q split j ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = 512 := by
  have hfree := linear_cartan_all_roots_fixedFree Q split hF i hK μ s 1
  have hfix := affine_cartan_centralizes_all_roots Q split j hs hp hg 1
  rw [rootAt_one] at hfree hfix
  have hj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  have hc := octagon_radical_cartan_fixed_card Q split hm i j hij
  rw [hfree,inf_eq_left.mpr hfix,card_bot,hj] at hc
  norm_num at hc ⊢
  exact hc

/-- The actual Cartan-fixed panel kernel has order 256 opposite a nonbinary linear root. -/
theorem affine_octagon_fixed_section_card
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Nat.card (affineFixedSection Q split j hs hp hg).numerator = 256 := by
  have hc := affine_octagon_cartan_fixed_card Q split hF hm i j hij hK μ s hs hp hg
  let C := simpleRemainder Q split j ⊓
    centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))
  let M := (affineFixedSection Q split j hs hp hg).numerator
  have hMC : M ≤ C := inf_le_inf_right _ (unipotent_inf_kernel_le_remainder Q split j)
  have he := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) M C bot_le hMC
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hi : M.relIndex C = 2 := affine_fixed_radical_index Q split j hs hp hg
  rw [hi,hc] at he
  change Nat.card M = 256
  omega

/-- An affine nine-point endpoint cannot oppose a nonbinary linear endpoint in the actual octagon. -/
theorem no_affine_octagon_of_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  let d := affineFixedSection Q split j hs hp hg
  have hc : Nat.card d.numerator = 256 :=
    affine_octagon_fixed_section_card Q split hF hm i j hij hK μ s hs hp hg
  have hquot := affine_action_frattini_lower_bound Q split j hs hp hg d.isTwo d.numeratorAction
    (affine_fixed_panel_kernel Q split j hs hp hg)
    (affine_fixed_action_not_two Q split hm i j hij (actorReflection Q split j) hs hp hg)
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  obtain ⟨x,hx,hx2⟩ := affine_cross_root_square Q split hm i j hij hs hp hg
  have hPhi : frattini d.numerator ≠ ⊥ := by
    intro he
    apply hx2
    have hh := pth_power_mem_frattini_of_isPGroup (p := 2) x
    rwa [he,mem_bot] at hh
  have hPhiCard := (frattini d.numerator).one_lt_card_iff_ne_bot.mpr hPhi
  have he := (frattini d.numerator).card_mul_index
  rw [index_eq_card,hc] at he
  nlinarith

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
