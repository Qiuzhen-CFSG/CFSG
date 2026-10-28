module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiParameters
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
public import Theory.Frattini.BinarySquares
/-!
# The actual derived radical in the regular Suzuki hexagon

Each Suzuki root has elementary abelianization. Its squares therefore lie
in its derived subgroup, and the literal five-root product makes the entire
radical abelianization elementary. Thus Φ(U_sj) = [U_sj,U_sj].

The five Cartan root quotients generate the radical Frattini quotient and
all have degree a. Its dimension is a subset sum of those five degrees,
while the faithful Suzuki action forces dimension at least 4a. Therefore
the quotient has degree 4a or 5a, and the actual derived radical has order
q⁶ or q⁵. This obtains the source order alternatives without yet asserting
the stronger exact product descriptions of the derived subgroup.

The existing Frattini RootSection is identified with that ambient derived
subgroup. Its nontrivial action and the small-degree theorem construct an
actual natural 4a-dimensional subquotient with its Suzuki intertwiner.
The location of this factor among the root products and the subsequent
triple-commutator contradiction are further source obligations.

Source: Fong--Seitz I (6C), printed p.41, using (4F) and the five-root
Cartan constituents. Positive native parameters are required throughout;
no original-factor perfectness is assumed by the applications.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem square_mem_commutator_of_suzukiRoot
    {A : Type*} [Group A] {m : ℕ} (hm : 0 < m)
    (ν : A ≃* SuzukiRootSubgroup m) (x : A) : x^2 ∈ _root_.commutator A := by
  have hmemb : (ν x)^2 ∈ _root_.commutator (SuzukiRootSubgroup m) := by
    rw [SchurCover.Family.root_commutator_eq_center m hm]
    exact suzukiRootSubgroup_square_mem_center m hm (ν x)
  have hmap : (_root_.commutator A).map ν.toMonoidHom =
      _root_.commutator (SuzukiRootSubgroup m) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr ν.surjective]
    rfl
  rw [←hmap,←map_pow] at hmemb
  exact (mem_map_iff_mem ν.injective).mp hmemb

/-- The five actual Suzuki roots generate a radical whose abelianization
has exponent two. Thus its Frattini subgroup is exactly its derived group. -/
theorem suzuki_radical_frattini_eq_commutator (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j) := by
  let V := simpleRemainder Q split j
  let π := QuotientGroup.mk' (_root_.commutator V)
  let : IsMulCommutative (V ⧸ _root_.commutator V) :=
    Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hroot (t : Fin 5)
      (x : rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)) :
      x^2 ∈ _root_.commutator (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)) := by
    let e := RootAction.conjugateEquiv
      (simpleRoot Q split (radicalRootKind i j t)) (representative (radicalRootWord Q i j t))
    by_cases ht : radicalRootKind i j t = i
    · have ν : simpleRoot Q split (radicalRootKind i j t) ≃* SuzukiRootSubgroup m :=
        (MulEquiv.subgroupCongr (congrArg (simpleRoot Q split) ht)).trans νi
      exact square_mem_commutator_of_suzukiRoot hm (e.trans ν) x
    · have he : radicalRootKind i j t = j := by omega
      have ν : simpleRoot Q split (radicalRootKind i j t) ≃* SuzukiRootSubgroup n :=
        (MulEquiv.subgroupCongr (congrArg (simpleRoot Q split) he)).trans νj
      exact square_mem_commutator_of_suzukiRoot hn (e.trans ν) x
  have hfactor (t : Fin 5)
      (x : rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)) :
      π (inclusion (radicalRoot_le Q split hhex i j hij t) x)^2 = 1 := by
    let f := inclusion (radicalRoot_le Q split hhex i j hij t)
    have hh : f (x^2) ∈ _root_.commutator V :=
      (show (_root_.commutator _).map f ≤ _root_.commutator V from by
        rw [map_commutator_eq]
        exact commutator_mono le_top le_top) (mem_map_of_mem f (hroot t x))
    rw [←map_pow,←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hh
  have hpow (v : V) : π v ^ 2 = 1 := by
    obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hhex i j hij).surjective v
    let a' : rootAt Q split i 1 := ⟨a,by rw [rootAt_one]; exact a.property⟩
    have h0 := hfactor 0 a'
    have h1 := hfactor 1 b
    have h2 := hfactor 2 c
    have h3 := hfactor 3 d
    have h4 := hfactor 4 e
    have hprod : inclusion (radicalRoot_le Q split hhex i j hij 0) a' *
        inclusion (radicalRoot_le Q split hhex i j hij 1) b *
        inclusion (radicalRoot_le Q split hhex i j hij 2) c *
        inclusion (radicalRoot_le Q split hhex i j hij 3) d *
        inclusion (radicalRoot_le Q split hhex i j hij 4) e = v := by
      apply Subtype.ext
      exact (radicalCoordinates_apply Q split hhex i j hij (a,b,c,d,e)).symm.trans
        (congrArg Subtype.val he)
    rw [←hprod]
    simp only [map_mul,mul_pow,h0,h1,h2,h3,h4,one_mul]
  have hV : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  let : Fact (IsPGroup 2 V) := ⟨hV⟩
  apply le_antisymm _ (commutator_le_frattini_of_isPGroup (p := 2))
  rw [hV.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp (show π (x^2) = 1 by rw [map_pow]; exact hpow x)

/-- The actual equal-parameter radical Frattini quotient has degree 4a or
5a. The five literal Cartan root maps give the divisibility by a; the
nontrivial rank-one action gives the lower bound. -/
theorem suzuki_radical_dimension_alternatives (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    let V := Additive (radicalSection Q split j hKj).EffectiveCarrier
    Module.finrank (ZMod 2) V = 4*(2*m+1) ∨ Module.finrank (ZMod 2) V = 5*(2*m+1) := by
  let V := Additive (radicalSection Q split j hKj).EffectiveCarrier
  let ρ := radicalHRepresentation Q split j hKj
  obtain ⟨s,hs⟩ := suzuki_radical_section_dimension Q split hhex i j hij hKi hKj hm hm
    μi μj νi νj (⊤ : Subrepresentation ρ) ⊥
  change Module.finrank (ZMod 2) ((⊤ : Submodule (ZMod 2) V) ⧸ ⊥) = _ at hs
  rw [Submodule.finrank_quotient,finrank_bot,Nat.sub_zero,finrank_top] at hs
  simp only [ite_self,Finset.sum_const,nsmul_eq_mul] at hs
  have hb := suzuki_suzuki_radical_finrank_bounds Q split hhex i j hij hKj hm hm μj νi νj
  change 4*(2*m+1) ≤ Module.finrank (ZMod 2) V ∧ _ at hb
  have hsc : s.card ≤ 5 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 5)
  have hsc4 : 4 ≤ s.card := by
    rw [hs] at hb
    nlinarith [hb.1]
  have hcases : s.card = 4 ∨ s.card = 5 := by omega
  rcases hcases with h | h
  · exact Or.inl (hs.trans (by simp only [h,Nat.cast_ofNat]))
  · exact Or.inr (hs.trans (by simp only [h,Nat.cast_ofNat]))

/-- The derived radical has exactly one of the two source orders q⁵,q⁶.
This concerns the actual ambient subgroup commutator. -/
theorem suzuki_derived_radical_card (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^(5*(2*m+1)) ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1)) := by
  let d := radicalSection Q split j hKj
  let V := simpleRemainder Q split j
  have hc : Nat.card V = 2^(10*(2*m+1)) := by
    rw [Nat.card_congr (radicalCoordinates Q split hhex i j hij).symm]
    simp only [Nat.card_prod,rootAt,card_rightConjugate,
      Nat.card_congr νi.toEquiv,Nat.card_congr νj.toEquiv,matrixRoot_card]
    simp only [←pow_add,←pow_mul]
    congr 1
    omega
  have he : Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) = Nat.card (frattini V) := by
    rw [←map_subtype_commutator,
      ←suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hm νi νj]
    exact Nat.card_congr ((frattini V).equivMapOfInjective V.subtype V.subtype_injective).symm.toEquiv
  have hcard : Nat.card (V ⧸ frattini V) =
      2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    rw [←suzuki_radical_effectiveDenominator Q split j hKj]
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  have hprod := (frattini V).index_mul_card
  change Nat.card (V ⧸ frattini V)*Nat.card (frattini V) = Nat.card V at hprod
  rw [hcard,hc] at hprod
  have hcalc (r s : ℕ) (hrs : r+s=10)
      (hd : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) = r*(2*m+1)) :
      Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) = 2^(s*(2*m+1)) := by
    rw [hd] at hprod
    rw [he]
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2))
    calc
      2^(r*(2*m+1))*Nat.card (frattini V) = 2^(10*(2*m+1)) := hprod
      _ = 2^(r*(2*m+1))*2^(s*(2*m+1)) := by
        rw [←pow_add,←Nat.add_mul,hrs]
  rcases suzuki_radical_dimension_alternatives Q split hhex i j hij hKi hKj hm μi μj νi νj with h | h
  · exact Or.inr (hcalc 4 6 rfl h)
  · exact Or.inl (hcalc 5 5 rfl h)

/-- The existing source Frattini section is literally the derived radical,
with its original ambient inclusion and conjugation action. -/
theorem suzuki_frattiniSection_numerator_eq_derived (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    (frattiniSection Q split j (radicalSection Q split j hKj)).numerator =
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  change (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype = _
  rw [suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hn νi νj,
    map_subtype_commutator]

/-- An actual invariant subquotient of the derived radical's Frattini
quotient is the natural 4a-dimensional Suzuki module. The quotient maps
and actor are those of the source RootSection. -/
theorem suzuki_derived_radical_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    let f := frattiniSection Q split j (radicalSection Q split j hKj)
    let ρ := f.effectiveRepresentation.comp μj.symm.toMonoidHom
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural m)) ∧
      Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*m+1) := by
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  let ρ := f.effectiveRepresentation.comp μj.symm.toMonoidHom
  have hmove := suzuki_frattini_radical_action_ne_one Q split j hhex i hij
    (UnitarySource.actorReflection Q split j) hKj νj
  have hf : Function.Injective ρ := (f.effectiveRepresentation_injective
    (suzuki_section_effectiveAction_injective Q split j hm μj f hmove)).comp μj.symm.injective
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hne : ρ ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := exists_ne (1 : SuzukiMatrixGroup m)
    exact hg (hf (by rw [he]; rfl))
  have hsz : Nat.card f.numerator ≤ 2^(6*(2*m+1)) := by
    rw [show f.numerator = ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ from
      suzuki_frattiniSection_numerator_eq_derived Q split hhex i j hij hKj hm hm νi νj]
    rcases suzuki_derived_radical_card Q split hhex i j hij hKi hKj hm μi μj νi νj with h | h
    · rw [h]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · exact h.le
  have hsz' : Nat.card f.EffectiveCarrier ≤ 2^(6*(2*m+1)) :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective f.effectiveDenominator)).trans hsz
  have hcard : Nat.card f.EffectiveCarrier =
      2^Module.finrank (ZMod 2) (Additive f.EffectiveCarrier) := by
    change Nat.card (Additive f.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive f.EffectiveCarrier)
  rw [hcard] at hsz'
  have hdim := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hsz'
  have hsmall : Module.finrank (ZMod 2) (Additive f.EffectiveCarrier) < 10*(2*m+1) := by omega
  obtain ⟨U,N,hi,⟨e⟩⟩ := Representation.SuzukiSmallDegree.exists_natural_section hm ρ hne hsmall
  exact ⟨U,N,hi,⟨e⟩,e.toLinearEquiv.finrank_eq.trans (Representation.SuzukiNatural.natural_finrank m)⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
