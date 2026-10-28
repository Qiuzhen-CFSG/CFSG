module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineExclusion
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Two Frattini layers exclude small affine hexagons

A freely acting point stabilizer on the regular ternary plane has a unique
involution: each involution induces inversion. Thus every subgroup of an
affine root of order greater than two contains a nontrivial square. The
crossed root meets the actual panel two-kernel in such a subgroup, since
the remainder defect is exactly two. The square belongs to the Frattini
subgroup of the Cartan-fixed kernel M.

Root separation shows that the reflection acts differently from every
simple-root element on both M and its Frattini subgroup. The odd-index
Borel argument makes both action images non-two-groups. Each action factors
through the actual root-panel image of order 72; primitivity makes it
faithful. Frattini faithfulness and the regular ternary plane force binary
degree at least eight on both successive Frattini quotients. Consequently
|M| is at least 2^16. If the opposite root has order at most eight, the
five-root remainder has order at most 2^15, a contradiction.

All kernels, actions, roots and conjugations belong to the same marked
split quotient. No regularity at the affine endpoint or perfectness is
assumed. The original-source application in BinaryAffineHexagonExclusion
exhausts the remaining small catalogue entries using this contradiction.
Source: Fong--Seitz I (4D), (5E), (5I), pp.21--23,27,34. Other even Weyl
orders, source minimality and full marked recognition remain separate.
-/

public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
  [FaithfulSMul G Ω] [Finite Ω] [Group.IsSolvable G]

/-- A freely acting point stabilizer of a solvable nine-point group has a unique involution. -/
theorem stabilizer_involution_unique
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9) (o : Ω)
    (hfree : ∀ g : stabilizer G o, ∀ x : Ω, x ≠ o → (g : G) • x = x → g = 1)
    (a b : stabilizer G o) (ha : a ≠ 1) (hb : b ≠ 1)
    (ha2 : a^2 = 1) (hb2 : b^2 = 1) : a = b := by
  obtain ⟨N,hNn,hNe,hNc,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hNn
  let α := (MulAut.conjNormal : G →* MulAut N).comp (stabilizer G o).subtype
  have hf (g : stabilizer G o) (hg : g ≠ 1) : MonoidHom.FixedPointFree (α g) := by
    intro n hn
    by_contra hne
    have hx : (n : G) • o ≠ o := by
      intro hx
      exact hne ((hreg o o).unique hx (by simp))
    apply hg
    apply hfree g ((n : G) • o) hx
    have he : (g : G) * (n : G) = (n : G) * (g : G) :=
      mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hn)
    rw [←mul_smul,he,mul_smul,g.property]
  have hinv (g : stabilizer G o) (hg : g^2 = 1) : Function.Involutive (α g) := by
    intro n
    have he := congrArg α hg
    rw [map_pow,map_one,pow_two] at he
    exact congrArg (fun f : MulAut N => f n) he
  apply stabilizer_action_injective N o hreg
  apply MulEquiv.ext
  intro n
  rw [(hf a ha).coe_eq_inv_of_involutive (hinv a ha2),
    (hf b hb).coe_eq_inv_of_involutive (hinv b hb2)]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem affine_root_involution_unique (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (a b : simpleRoot Q split j) (ha : a ≠ 1) (hb : b ≠ 1)
    (ha2 : a^2 = 1) (hb2 : b^2 = 1) : a = b := by
  let f : simpleRoot Q split j →* stabilizer (rootPanelImage Q split j) (panelBase Q j) :=
    ((rootImageProjection Q split j).comp
      (inclusion (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left))).codRestrict _
        (fun r => panelRoot_fixes_base Q split j r)
  have hf : Function.Injective f := by
    intro r t he
    apply simpleRoot_panelAction_injective Q split j
    exact congrArg (fun x => x.val.val) he
  obtain ⟨hsol,hcard,hfree⟩ := affine_root_image_structure Q split j hs hp hg
  let := hsol
  apply hf
  apply BinaryPanel.stabilizer_involution_unique
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) hfree
  · exact fun he => ha (hf (he.trans f.map_one.symm))
  · exact fun he => hb (hf (he.trans f.map_one.symm))
  · rw [←map_pow,ha2,map_one]
  · rw [←map_pow,hb2,map_one]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Every subgroup of a conjugate affine root having order greater than two contains a nontrivial square. -/
theorem affine_root_subgroup_square (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (w : Weyl Q) (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ rootAt Q split j w)
    (hc : 2 < Nat.card A) : ∃ a : A, a^2 ≠ 1 := by
  classical
  by_contra! hn
  let n : X ⧸ Q.D := representative w
  let f : A →* simpleRoot Q split j :=
    ((MulAut.conj n).toMonoidHom.comp A.subtype).codRestrict _ (fun a => hA a.property)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact (MulAut.conj n).injective (congrArg Subtype.val he)
  have hu (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
    apply hf
    apply affine_root_involution_unique Q split j hs hp hg
    · exact fun he => ha (hf (he.trans f.map_one.symm))
    · exact fun he => hb (hf (he.trans f.map_one.symm))
    · rw [←map_pow,hn,map_one]
    · rw [←map_pow,hn,map_one]
  have hi : Function.Injective (fun a : A => decide (a = 1)) := by
    intro a b he
    by_cases ha : a = 1
    · have hb : b = 1 := by simpa [ha] using he.symm
      exact ha.trans hb.symm
    · have hb : b ≠ 1 := by simpa [ha] using he.symm
      exact hu a b ha hb
  have hcard := Nat.card_le_card_of_injective _ hi
  norm_num at hcard
  omega

/-- The crossed affine root meets the actual fixed kernel in an element with nontrivial square. -/
theorem affine_cross_root_square (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    ∃ x : (affineFixedSection Q split j hs hp hg).numerator,
      (x : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) ∧ x^2 ≠ 1 := by
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

/-- On any action killing the full Cartan, a two-group image would identify a reflection with a root element. -/
private theorem affine_action_not_two {A : Type*} [Group A] [Finite A]
    (j : Fin 2) (hp : Nat.card (Panel Q j) = 9)
    (s : RootReflection Q split j) (α : rankOne Q split j →* A)
    (ht : ∀ t : rankOne Q split j, (t : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N → α t = 1)
    (hne : ∀ u : rankOne Q split j, (u : X ⧸ Q.D) ∈ simpleRoot Q split j →
      α ⟨s.val,s.mem_rankOne⟩ ≠ α u) : ¬ IsPGroup 2 α.range := by
  let f := α.rangeRestrict
  let R := rankOne Q split j
  let B := Q.tits.B.subgroupOf R
  let A := (simpleRoot Q split j).subgroupOf R
  have hAB : A.map f = B.map f := by
    apply le_antisymm (map_mono (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)))
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨a,ha,t,ht',he⟩ := rootActor_borel_factorization Q split j r.property hr
    let a' : R := ⟨a,(show simpleRoot Q split j ≤ R from le_sup_left) ha⟩
    let t' : R := ⟨t,ht'.1⟩
    have he' : r = a'*t' := Subtype.ext he
    refine ⟨a',ha,?_⟩
    rw [he',map_mul,show f t' = 1 from Subtype.ext (ht t' ht'.2),mul_one]
  intro htwo
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd α.rangeRestrict_surjective
    rwa [rankOne_borel_index Q split j,hp] at hh
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have htop : A.map f = ⊤ := hAB.trans (index_eq_one.mp hidx)
  have hr : f ⟨s.val,s.mem_rankOne⟩ ∈ A.map f := htop ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hr
  exact hne u hu (congrArg Subtype.val he).symm

/-- A non-two affine action on a two-group forces a Frattini quotient of order at least 256. -/
theorem affine_action_frattini_lower_bound {A : Type*} [Group A] [Finite A]
    (j : Fin 2) (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (hA : IsPGroup 2 A) (α : rankOne Q split j →* MulAut A)
    (hk : (rankOneAction Q split j).ker ≤ α.ker) (hne : ¬ IsPGroup 2 α.range) :
    256 ≤ Nat.card (A ⧸ frattini A) := by
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hk' : f.ker ≤ α.ker := by
    change ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker ≤ _
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker,←rankOneAction_ker]
    exact hk
  let β : rootPanelImage Q split j →* MulAut A := f.liftOfSurjective hf ⟨α,hk'⟩
  have hb (r : rankOne Q split j) : β (f r) = α r :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hbrange : β.range = α.range := by
    have he : β.comp f = α := MonoidHom.ext hb
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
  obtain ⟨hsol,hcard,hfree⟩ := affine_root_image_structure Q split j hs hp hg
  let := hsol
  have hβ : Function.Injective β := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) β (hbrange ▸ hne)
  let γ := (quotientAut (frattini A)).comp β
  have hkγ : IsPGroup 2 γ.ker :=
    (isPGroup_quotientAut_frattini_kernel hA).comap_of_injective β hβ
  have hγ : Function.Injective γ := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) γ hkγ
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) := isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom γ
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hγ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive (A ⧸ frattini A)) => a (Additive.ofMul x)) he)
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (A ⧸ frattini A))
  simp only [Nat.card_zmod] at he
  rw [←he] at hh
  exact hh
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The reflection differs from every root element already on the Frattini subgroup of the true fixed kernel. -/
theorem affine_frattini_reflection_ne_root (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j) :
    let d := affineFixedSection Q split j hs hp hg
    let α := (MulAut.characteristic (frattini d.numerator)).comp d.numeratorAction
    α ⟨s.val,s.mem_rankOne⟩ ≠ α u := by
  let d := affineFixedSection Q split j hs hp hg
  let α := (MulAut.characteristic (frattini d.numerator)).comp d.numeratorAction
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  obtain ⟨x,hx,hx2⟩ := affine_cross_root_square Q split hm i j hij hs hp hg
  let y : frattini d.numerator := ⟨x^2,pth_power_mem_frattini_of_isPGroup (p := 2) x⟩
  let a : X ⧸ Q.D := (x : X ⧸ Q.D)^2
  have ha : a ∈ rootAt Q split j (Q.simple i) := (rootAt Q split j (Q.simple i)).pow_mem hx 2
  have hane : a ≠ 1 := fun he => hx2 (Subtype.ext he)
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  change α r ≠ α u
  intro he
  have hei : α r⁻¹ = α u⁻¹ := by rw [map_inv,map_inv,he]
  have hxy := congrArg (fun f : MulAut (frattini d.numerator) => ((f y : d.numerator) : X ⧸ Q.D)) hei
  change (d.numeratorAction r⁻¹ (x^2) : X ⧸ Q.D) = (d.numeratorAction u⁻¹ (x^2) : X ⧸ Q.D) at hxy
  rw [d.numeratorAction_apply,d.numeratorAction_apply] at hxy
  simp only [coe_inv,inv_inv,coe_pow] at hxy
  change (s.val : X ⧸ Q.D)⁻¹*a*s.val = (u : X ⧸ Q.D)⁻¹*a*u at hxy
  have haD : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  obtain ⟨hU,hD,hd⟩ := cross_root_separation Q split hm i j hij
  have haC := (unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem
    ((unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem (hU hu) (hxy ▸ hD haD))
    ((unipotentConjugate split (Q.simple j*Q.simple i)).inv_mem (hU hu))
  have haC' : a ∈ unipotentConjugate split (Q.simple j*Q.simple i) := by
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using haC
  exact hane (disjoint_def.mp hd ha haC')

/-- Both Frattini layers are faithful enough for the degree-eight bound; the true fixed kernel has order at least 2^16. -/
theorem affine_hexagon_fixed_section_large
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    65536 ≤ Nat.card (affineFixedSection Q split j hs hp hg).numerator := by
  let d := affineFixedSection Q split j hs hp hg
  let α := (MulAut.characteristic (frattini d.numerator)).comp d.numeratorAction
  have hk : (rankOneAction Q split j).ker ≤ α.ker := by
    intro r hr
    change (MulAut.characteristic (frattini d.numerator)) (d.numeratorAction r) = 1
    rw [show d.numeratorAction r = 1 from affine_fixed_panel_kernel Q split j hs hp hg hr,map_one]
  have ht (t : rankOne Q split j) (ht : (t : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N) : α t = 1 := by
    have he : d.numeratorAction t = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [d.numeratorAction_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp x.property.2 _ ht)
    change (MulAut.characteristic (frattini d.numerator)) (d.numeratorAction t) = 1
    rw [he,map_one]
  have hnon : ¬ IsPGroup 2 α.range := affine_action_not_two Q split j hp
    (actorReflection Q split j) α ht
    (affine_frattini_reflection_ne_root Q split hm i j hij (actorReflection Q split j) hs hp hg)
  have hphi := affine_action_frattini_lower_bound Q split j hs hp hg
    (d.isTwo.to_subgroup (frattini d.numerator)) α hk hnon
  have hquot := affine_action_frattini_lower_bound Q split j hs hp hg d.isTwo d.numeratorAction
    (affine_fixed_panel_kernel Q split j hs hp hg)
    (affine_fixed_action_not_two Q split hm i j hij (actorReflection Q split j) hs hp hg)
  have hle := Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective (frattini (frattini d.numerator)))
  have hc := (frattini d.numerator).card_mul_index
  rw [index_eq_card] at hc
  nlinarith

/-- The large fixed kernel excludes the affine hexagon whenever the opposite root has order at most eight. -/
theorem no_affine_hexagon_of_small_opposite
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) ≤ 8)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  have hj : Nat.card (simpleRoot Q split j) = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  have hU := unipotent_card_even Q split 3 hm
  have hprod : Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1) =
      Nat.card (simpleRoot Q split i) * 8 := by
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rw [hj]
    · rw [hj,Nat.mul_comm]
    · exact (hij rfl).elim
  rw [hprod] at hU
  have hbound : Nat.card split.U ≤ 262144 := by
    rw [hU]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right 8 hi) 3)
  have hrem := unipotent_card_simple Q split j
  rw [hj] at hrem
  have hM : (affineFixedSection Q split j hs hp hg).numerator ≤ simpleRemainder Q split j :=
    (affineFixedSection Q split j hs hp hg).le_radical
  have hcard := Nat.card_le_card_of_injective (inclusion hM) (inclusion_injective hM)
  have hlarge := affine_hexagon_fixed_section_large Q split hm i j hij hs hp hg
  omega
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
