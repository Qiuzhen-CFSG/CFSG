module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleSection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitarySeparation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootDerived
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearLayers

/-!
# The derived radical in the quadratic unitary octagon

The two linear end-root projections put the derived radical inside the
five middle roots. Their unique coordinates give the source order bound
2^(13b) when the linear degree is twice the unitary degree. The crossed
unitary root has a nontrivial derived subgroup in this same radical.
The unitary reflection moves it into a disjoint root, proving that the
actual rank-one actor moves the derived radical.

Its first Frattini quotient consequently has order at least 2^(6b).
For b >= 2 this follows from the special-unitary cover and the binary
degree theorem, retaining the scalar kernel. At b = 1 the existing
solvable special/projective section bounds replace perfectness. The
original-factor and Chapter 12 applications are in the matching CFSG
modules, with both orientations and full original amalgam markings.
The three cubic-fixed Frattini factors are root commutators, so the full
cubic radical centralizer already lies inside the derived radical.

Source: Fong--Seitz I (6F), printed p.47. These are the support and
initial-action inputs to the lower-central-series contradiction. The
projective-section bound 2^(8b), its persistence and the terminal
contradiction are not assumed or proved here.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual derived radical with its conjugation action and trivial denominator. -/
@[expose] def unitaryDerivedSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) : RootSection Q split j :=
  subgroupSection Q split j ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    (commutator_le_self _) ((rankOne_le_parabolic Q split j).trans
      (radical_commutator_normalized Q split j hKj))

/-- The source five-root bound has the exact exponent thirteen when the
linear field is the square of the unitary fixed field. -/
theorem unitary_derived_card_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hlin : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {b : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^(2*b))
    (hj : Nat.card (simpleRoot Q split j) = (2^b)^3) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ middleFive Q split j i ∧
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) ≤ 2^(13*b) := by
  have hle := radical_commutator_le_middleFive Q split hm j i hij.symm hKi hlin
  refine ⟨hle,(Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans_eq ?_⟩
  rw [middleFive_card Q split hm j i hij.symm,hi,hj,←pow_mul,←pow_mul,←pow_mul,←pow_add]
  congr 1
  omega

private theorem cross_root_moves_section (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (s : HexagonStructure.RootReflection Q split j)
    (d : RootSection Q split j) (hd : d.denominator = ⊥)
    (a : X ⧸ Q.D) (ha : a ∈ rootAt Q split j (Q.simple i))
    (hax : a ∈ d.numerator) (hne : a ≠ 1) : d.action ≠ 1 := by
  let x : d.numerator := ⟨a,hax⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : d.action r⁻¹ = 1 := by rw [he]; rfl
  have hx : d.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun z : MulAut d.Carrier => z (QuotientGroup.mk x)) hei
    rw [d.action_mk] at hh
    have hh' := QuotientGroup.eq_iff_div_mem.mp hh
    rw [hd,mem_bot] at hh'
    exact div_eq_one.mp hh'
  have hxa : (s.val : X ⧸ Q.D)⁻¹*a*s.val = a := by
    have hh := congrArg Subtype.val hx
    rw [d.numeratorAction_apply] at hh
    simpa only [r,x,coe_inv,inv_inv] using hh
  have hconj : a ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq,←hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  obtain ⟨_,hB,hdis⟩ := cross_root_separation Q split hm i j hij
  exact hne (disjoint_def.mp hdis ha (hB hconj))


/-- A nontrivial root commutator sits in the crossed unitary root and
in the derived radical; no perfectness assumption is needed. -/
theorem crossed_unitary_derived_witness (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    ∃ a : rootAt Q split j (Q.simple i), a ≠ 1 ∧
      (a : X ⧸ Q.D) ∈ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let A := rootAt Q split j (Q.simple i)
  have hAV : A ≤ simpleRemainder Q split j :=
    (show A ≤ middleFive Q split j i from
      le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))).trans
      (middleFive_le_remainder Q split hm j i hij.symm)
  have hn : ⁅A,A⁆ ≠ ⊥ := by
    intro he
    have hh : rightConjugate ⁅simpleRoot Q split j,simpleRoot Q split j⁆
        (representative (Q.simple i) : X ⧸ Q.D) = ⊥ := by
      simpa only [A,rootAt,rightConjugate,comap_equiv_eq_map_symm',map_commutator]
        using he
    apply hne
    rw [rightConjugate,comap_equiv_eq_map_symm'] at hh
    exact (map_eq_bot_iff_of_injective _
      (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).symm.injective).mp hh
  obtain ⟨a,hane⟩ := ne_bot_iff_exists_ne_one.mp hn
  exact ⟨⟨a,commutator_le_self _ a.property⟩,
    (fun he => hane (Subtype.ext (congrArg (fun x : rootAt Q split j (Q.simple i) => (x : X ⧸ Q.D)) he))),
    commutator_mono hAV hAV a.property⟩

/-- Nonabelianness of the crossed unitary root forces the reflection to
move the actual derived radical, including the smallest unitary field. -/
theorem unitary_derived_action_ne_one (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    (unitaryDerivedSection Q split j hKj).action ≠ 1 := by
  obtain ⟨a,ha,hax⟩ := crossed_unitary_derived_witness Q split hm i j hij hne
  exact cross_root_moves_section Q split hm i j hij (UnitarySource.actorReflection Q split j)
    (unitaryDerivedSection Q split j hKj) rfl a a.property hax
      (fun he => ha (Subtype.ext he))

/-- The movement is on the original ambient derived subgroup, not only
on a separately chosen representation. -/
theorem unitary_derived_not_centralized (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    ⁅rankOne Q split j,⁅simpleRemainder Q split j,simpleRemainder Q split j⁆⁆ ≠ ⊥ := by
  intro he
  have hcent := commutator_eq_bot_iff_le_centralizer.mp he
  apply unitary_derived_action_ne_one Q split hm i j hij hKj hne
  let d := unitaryDerivedSection Q split j hKj
  change d.action = 1
  ext r z
  induction z using QuotientGroup.induction_on with
  | H z =>
    change d.action r (QuotientGroup.mk z) = QuotientGroup.mk z
    rw [d.action_mk]
    congr 1
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    have hz := mem_centralizer_iff.mp (hcent r.property) z z.property
    rw [←hz,mul_inv_cancel_right]

/-- The actual unitary local marking supplies a nontrivial root commutator
for every positive degree, with arbitrary Hermitian Gram matrix. -/
theorem unitary_root_commutator_ne_bot
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥ := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  exact (QuadrangleStructure.simpleRoot_unitary_derived J₀ hb hcard hf rfl
    Q split j hKj (μj.trans ep)).2.2

/-- The derived radical has a nontrivial unitary action and its
Frattini quotient satisfies the genuine binary degree bound. -/
theorem unitary_derived_effective_and_card
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    (unitaryDerivedSection Q split j hKj).IsEffective ∧
      2^(6*b) ≤ Nat.card ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup (X ⧸ Q.D)) ⧸ frattini
          (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D))) := by
  let d := unitaryDerivedSection Q split j hKj
  have hmoving := unitary_derived_action_ne_one Q split hm i j hij hKj hne
  refine ⟨unitary_section_effective Q split j J hb hcard hconj σ hσ hKj μj d hmoving,?_⟩
  have hc := unitary_section_card_bound Q split j J hb hcard hconj σ hσ d hmoving
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(6*b) ≤ d.effectiveDenominator.index at hc
  rw [hd] at hc
  exact hc

/-- The first derived Frattini layer has at least six binary dimensions
per unitary field degree. The exceptional solvable actors are treated by
their actual special/projective models, rather than by perfectness. -/
theorem unitary_derived_frattini_card_ge
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    2^(6*b) ≤ Nat.card ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) ⧸ frattini
        (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D))) := by
  have hne := unitary_root_commutator_ne_bot Q split J hb hcard hconj j hKj μj
  by_cases hb1 : b=1
  · have hfull := hsmall hb1
    subst b
    norm_num only [mul_one,pow_one,Nat.reducePow] at hcard hconj hroot ⊢
    let d := unitaryDerivedSection Q split j hKj
    obtain ⟨a,ha,hax⟩ := crossed_unitary_derived_witness Q split hm i j hij hne
    have hc : 64 ≤ Nat.card d.EffectiveCarrier := by
      rcases hfull with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · have hf : Nat.card {x : F // J.conj x=x}=2 := by
          simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
            (by simpa using hcard) (by simpa using hconj)
        let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
        obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
          J 2 (by simpa using hcard) hf
        let es := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
        exact small_special_section_bound Q split j J₀ hcard hconj rfl hKj (ν.trans es)
          hroot hm i hij (UnitarySource.actorReflection Q split j) d rfl a ha hax
      · let := HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
        let : Group.IsSolvable (rankOne Q split j) :=
          Group.isSolvable_of_surjective (f:=ν.symm.toMonoidHom) ν.symm.surjective
        have hR : Nat.card (rankOne Q split j)=72 :=
          (Nat.card_congr ν.toEquiv).trans (HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
        exact (by decide : 64 ≤ 256).trans (nine_actor_section_bound Q split j hR hroot
          hm i hij (UnitarySource.actorReflection Q split j) d rfl a ha hax)
    have hd : d.effectiveDenominator = frattini d.numerator := by
      rw [d.effectiveDenominator_eq]
      exact sup_bot_eq _
    change 64 ≤ d.effectiveDenominator.index at hc
    rw [hd] at hc
    exact hc
  · exact (unitary_derived_effective_and_card Q split J (by omega) hcard hconj
      hm i j hij hKj μj σ hσ hne).2

/-- The root Frattini factors in the cubic fixed product are literally
ambient root commutators, including the quaternion root at degree one. -/
theorem unitary_rootFrattini_eq_commutator
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) :
    rootFrattiniAt Q split j w = ⁅rootAt Q split j w,rootAt Q split j w⁆ := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  have hs := (QuadrangleStructure.unitary_simpleRoot_special Q split J₀ hb hcard hf rfl
    j hKj (μj.trans ep)).1
  have he : frattini (rootAt Q split j w) = _root_.commutator (rootAt Q split j w) := by
    let f : rootAt Q split j w ≃* simpleRoot Q split j :=
      ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)
    apply Subgroup.map_injective (f:=f.toMonoidHom) f.injective
    rw [frattini_map_equiv,map_commutator_eq,MonoidHom.range_eq_top.mpr f.surjective]
    exact hs
  rw [rootFrattiniAt,he,map_subtype_commutator]

/-- Every cubic-fixed radical element already lies in the derived
radical. Thus the entire cubic fixed group survives in the derived
lower-central term, with the literal subgroup intersections retained. -/
theorem unitary_derived_threeCore_fixed (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hfree : ∀ w : Weyl Q, rootAt Q split i w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)
    (hderived : ∀ w : Weyl Q, rootFrattiniAt Q split j w =
      ⁅rootAt Q split j w,rootAt Q split j w⁆) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
        centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
      simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
  apply le_antisymm (inf_le_inf_right _ (commutator_le_self _))
  apply le_inf ?_ inf_le_right
  intro x hx
  have hp := unitary_cubic_radical_product Q split hm i j hij hfree hfix
  have hx' : x ∈ (↑(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) : Set (X ⧸ Q.D)) := hx
  rw [hp] at hx'
  obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hx'
  have inside (w : Weyl Q) (hw : rootAt Q split j w ≤ middleFive Q split j i) :
      rootFrattiniAt Q split j w ≤ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
    rw [hderived]
    have hv := hw.trans (middleFive_le_remainder Q split hm j i hij.symm)
    exact commutator_mono hv hv
  exact mul_mem (mul_mem
    (inside _ (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))) ha)
    (inside _ (le_sup_of_le_left (le_sup_of_le_left le_sup_right)) hb))
    (inside _ le_sup_right hc)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
