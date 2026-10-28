module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedRoots

/-!
# Derived-radical control for regular unitary hexagons

Hermitian trace surjectivity expresses every root square as a commutator.
Transport through the actual special or projective Sylow marking and the
five canonical root factors proves Φ(U_sj) = [U_sj,U_sj]. No scalar kernel
or original-factor perfectness assumption is introduced.

Write the opposite whole-root order as 2^a and the acting unitary parameter
as 2^n. The actual first Frattini layer gives |Φ(U_sj)| ≤ 2^(3a).
If a < 4n, the next two effective layers cannot both move: each would have
order at least 2^(6n). Thus R_j centralizes Φ²(U_sj). A square in any of
the four nonmiddle roots, transported by the literal source reflection,
then excludes that whole root from Φ(U_sj), and hence from U_sj'.

For a regular unitary pair of degrees m ≤ n this applies with a = 3m.
It gives 2^(6n) ≤ |U_sj'| ≤ 2^(9m), centralization of Φ(U_sj'), and the
four whole-root exclusions. The exact Cartan constituents, parameter
equality, lower-central-series contradiction, and complete (6D)/(6E)
assembly remain subsequent obligations. The statements below are local
steps on the source radicals, not an assertion of those exclusions.

Source: Fong--Seitz I (6D), printed pp.42--43, with (4D), (5D) and (3G).
The square calculation uses Huppert II.10.4 and II.10.12 in the established
Hermitian coordinates. The generic reflection and five-root maps are
reused from the preceding Suzuki development at their model-free types.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped commutatorElement IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

include hn hcard hconj in
/-- Two moving effective sections would exceed the order of this literal numerator. -/
theorem unitary_small_section_frattini_action_eq_one (j : Fin 2)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (hmove : d.action ≠ 1) (hsmall : Nat.card d.numerator < 2^(12*n)) :
    (frattiniSection Q split j d).action = 1 := by
  by_contra hn'
  let f := frattiniSection Q split j d
  have h1 := unitary_section_card_bound Q split j J hn hcard hconj σ hσ d hmove
  have h2 := unitary_section_card_bound Q split j J hn hcard hconj σ hσ f hn'
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq,hden,sup_bot_eq]
  change 2^(6*n) ≤ d.effectiveDenominator.index at h1
  rw [he] at h1
  have hc : Nat.card f.EffectiveCarrier ≤ Nat.card (frattini d.numerator) := by
    calc
      Nat.card f.EffectiveCarrier ≤ Nat.card f.numerator :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ = Nat.card (frattini d.numerator) :=
        Nat.card_congr ((frattini d.numerator).equivMapOfInjective
          d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  have hb : 2^(12*n) ≤ Nat.card d.numerator := by
    calc
      2^(12*n) = 2^(6*n)*2^(6*n) := by rw [←pow_add]; congr 1; omega
      _ ≤ (frattini d.numerator).index*Nat.card (frattini d.numerator) :=
        Nat.mul_le_mul h1 (h2.trans hc)
      _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card
  exact (not_lt_of_ge hb) hsmall

include hn hcard hconj in
/-- The first source layer and the exact five-root order bound the radical Frattini subgroup. -/
theorem unitary_radical_frattini_card_upper
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    Nat.card (frattini (simpleRemainder Q split j)) ≤ 2^(3*a) := by
  let V := simpleRemainder Q split j
  have hV : Nat.card V = 2^(3*a+6*n) := by
    rw [Nat.card_congr (radicalCoordinates Q split hm i j hij).symm]
    simp only [Nat.card_prod,rootAt,card_rightConjugate,hi,hj,←pow_mul,←pow_add]
    congr 1
    omega
  have hb := unitary_radical_first_layer_card_bound J hn hcard hconj Q split j σ hσ
    hm i hij (UnitarySource.actorReflection Q split j) hKj
  have hc := (frattini V).index_mul_card
  have he : 2^(6*n)*Nat.card (frattini V) ≤ 2^(6*n)*2^(3*a) := by
    calc
      _ ≤ (frattini V).index*Nat.card (frattini V) := Nat.mul_le_mul_right _ hb
      _ = Nat.card V := hc
      _ = 2^(6*n)*2^(3*a) := by rw [hV,←pow_add]; congr 1; omega
  exact Nat.le_of_mul_le_mul_left he (Nat.pow_pos (by decide : 0 < 2))

include hn hcard hconj in
/-- The actual rank-one action on the second Frattini subgroup is trivial in this parameter range. -/
theorem unitary_second_frattini_radical_action_eq_one
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) (han : a < 4*n)
    (hsquare : ∃ x : simpleRoot Q split j, x^2 ≠ 1) :
    (frattiniSection Q split j (frattiniSection Q split j
      (radicalSection Q split j hKj))).action = 1 := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  apply unitary_small_section_frattini_action_eq_one Q split J hn hcard hconj j σ hσ f rfl
    (root_square_frattini_action_ne_one Q split hm i j hij
      (UnitarySource.actorReflection Q split j) hKj hsquare)
  calc
    Nat.card f.numerator = Nat.card (frattini d.numerator) :=
      Nat.card_congr ((frattini d.numerator).equivMapOfInjective
        d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
    _ ≤ 2^(3*a) := unitary_radical_frattini_card_upper Q split J hn hcard hconj
      hm i j hij hKj σ hσ hi hj
    _ < 2^(12*n) := Nat.pow_lt_pow_right (by decide) (by omega)

include hn hcard hconj in
/-- None of the four nonmiddle roots can lie wholly in the radical Frattini subgroup. -/
theorem unitary_nonmiddle_root_not_le_frattini
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) (han : a < 4*n)
    (hsquare : ∀ k : Fin 2, ∃ x : simpleRoot Q split k, x^2 ≠ 1)
    (t : Fin 5) (ht : t ≠ 2) :
    ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  let A := rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)
  let e : A ≃* simpleRoot Q split (radicalRootKind i j t) :=
    RootAction.conjugateEquiv (simpleRoot Q split (radicalRootKind i j t))
      (representative (radicalRootWord Q i j t))
  obtain ⟨x,hx⟩ := hsquare (radicalRootKind i j t)
  have hx' : (e.symm x)^2 ≠ 1 := by
    intro he
    exact hx (by simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e he)
  intro hle
  exact reflection_moves_frattini_section Q split (UnitarySource.actorReflection Q split j) f A hle
    (radical_nonmiddle_root_disjoint Q split hm i j hij (UnitarySource.actorReflection Q split j) t ht)
    (e.symm x) hx'
    (unitary_second_frattini_radical_action_eq_one Q split J hn hcard hconj
      hm i j hij hKj σ hσ hi hj han (hsquare j))

include hn hcard hconj in
/-- In particular, none of those four whole roots lies in the actual derived radical. -/
theorem unitary_nonmiddle_root_not_le_derived
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) (han : a < 4*n)
    (hsquare : ∀ k : Fin 2, ∃ x : simpleRoot Q split k, x^2 ≠ 1)
    (t : Fin 5) (ht : t ≠ 2) :
    ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  intro hle
  apply unitary_nonmiddle_root_not_le_frattini Q split J hn hcard hconj
    hm i j hij hKj σ hσ hi hj han hsquare t ht
  apply hle.trans
  rw [←map_subtype_commutator]
  let : Fact (IsPGroup 2 (simpleRemainder Q split j)) := ⟨split.isTwo.to_le inf_le_left⟩
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

include hn hcard hconj in
/-- The preceding action statement as an ambient commutator identity, with both subgroup inclusions retained. -/
theorem unitary_second_frattini_radical_centralized
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) (han : a < 4*n)
    (hsquare : ∃ x : simpleRoot Q split j, x^2 ≠ 1) :
    let V := simpleRemainder Q split j
    ⁅rankOne Q split j,(frattini (frattini V)).map
      (V.subtype.comp (frattini V).subtype)⁆ = ⊥ := by
  let V := simpleRemainder Q split j
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  let g := frattiniSection Q split j f
  let e : frattini V ≃* f.numerator :=
    (frattini V).equivMapOfInjective V.subtype V.subtype_injective
  have he : g.numerator = (frattini (frattini V)).map
      (V.subtype.comp (frattini V).subtype) := by
    change (frattini f.numerator).map f.numerator.subtype = _
    rw [←frattini_map_equiv e,map_map]
    rfl
  have hact := unitary_second_frattini_radical_action_eq_one Q split J hn hcard hconj
    hm i j hij hKj σ hσ hi hj han hsquare
  change g.action = 1 at hact
  dsimp only
  rw [←he]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro r hr x hx
  have hfix := congrArg (fun a : MulAut g.Carrier => a (QuotientGroup.mk (⟨x,hx⟩ : g.numerator)))
    (show g.action ⟨r,hr⟩ = 1 by rw [hact]; rfl)
  rw [g.action_mk] at hfix
  have hh := congrArg Subtype.val (congrArg QuotientGroup.quotientBot hfix)
  change r*x*r⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem square_commutator_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hb : ∀ x : B, x^2 ∈ _root_.commutator B) (x : A) :
    x^2 ∈ _root_.commutator A := by
  have hh := hb (e x)
  have he : (_root_.commutator A).map e.toMonoidHom = _root_.commutator B := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  rw [←he,←map_pow] at hh
  exact (mem_map_iff_mem e.injective).mp hh

private theorem hermitian_square_mem_commutator [CharP F 2]
    {q : ℕ} (hc : Nat.card F = q^2)
    (hf : Nat.card {x : F // J.conj x=x} = q)
    (x : hermitianUnipotentCoord J) : x^2 ∈ _root_.commutator (hermitianUnipotentCoord J) := by
  let b := x.val.1 * J.conj x.val.1
  obtain ⟨c,hc'⟩ := huppert_II_10_4_trace_surjective J q hc hf b (by
    dsimp only [b]
    rw [map_mul,J.conj_involutive,mul_comm])
  obtain ⟨p,hp⟩ := HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hc hf (Multiplicative.ofAdd 1)
  obtain ⟨s,hs⟩ := HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hc hf (Multiplicative.ofAdd c)
  have hp' : p.val.1 = 1 := congrArg Multiplicative.toAdd hp
  have hs' : s.val.1 = c := congrArg Multiplicative.toAdd hs
  have he : ⁅p,s⁆ = x^2 := by
    rw [hermitianUnipotent_commutator]
    apply Subtype.ext
    rw [HermitianForm.EvenInner.square_coordinates]
    apply Prod.ext
    · rfl
    · change s.val.1 * J.conj p.val.1 - p.val.1 * J.conj s.val.1 = b
      rw [hp',hs',map_one,mul_one,one_mul,sub_eq_add_neg,CharTwo.neg_eq]
      exact hc'
  rw [←he]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

private instance projectiveFinite : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

include hn hcard hconj in
private theorem projective_sylow_square_profile
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card T = (2^n)^3 ∧ ∀ x : T, x^2 ∈ _root_.commutator T := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : T ≃* T' := (T : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  let c := b.trans (T'.equiv (HermitianForm.EvenTwoRank.rootSylow J' rfl (by omega) hcard hf))
  have hc : Nat.card T = (2^n)^3 := by
    rw [Nat.card_congr c.toEquiv]
    exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J' rfl _ hcard hf
  let e := b.trans (HermitianForm.SylowOmega.projectiveSylowEquivCoords J' hn hcard hf rfl T')
  exact ⟨hc,square_commutator_transport e (hermitian_square_mem_commutator J' hcard hf)⟩

private theorem root_square_profile_of_sylow (j : Fin 2)
    {M : Type*} [Group M] [Finite M] (μ : rankOne Q split j ≃* M)
    (T : Sylow 2 M) (hc : Nat.card (simpleRoot Q split j) = Nat.card T)
    (hs : ∀ x : T, x^2 ∈ _root_.commutator T) :
    ∀ x : simpleRoot Q split j, x^2 ∈ _root_.commutator (simpleRoot Q split j) := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  let eS : S ≃* S' := (S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  let eA : A ≃* simpleRoot Q split j := subgroupOfEquivOfLe
    (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)
  have hAS : Nat.card A = Nat.card S :=
    (Nat.card_congr eA.toEquiv).trans (hc.trans
      ((Nat.card_congr (S'.equiv T).symm.toEquiv).trans (Nat.card_congr eS.symm.toEquiv)))
  have he : A = (S : Subgroup (rankOne Q split j)) := eq_of_le_of_card_ge hS hAS.ge
  exact square_commutator_transport
    (eA.symm.trans ((MulEquiv.subgroupCongr he).trans (eS.trans (S'.equiv T)))) hs

include hn hcard hconj in
/-- Actual special and projective unitary root markings both put every root square in its derived subgroup. -/
theorem unitary_root_square_mem_commutator (j : Fin 2)
    (hmodel : Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (rankOne Q split j ≃* J.specialSubgroup))
    (hc : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    ∀ x : simpleRoot Q split j, x^2 ∈ _root_.commutator (simpleRoot Q split j) := by
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · let T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) := Classical.choice inferInstance
    obtain ⟨hT,hs⟩ := projective_sylow_square_profile J hn hcard hconj T
    exact root_square_profile_of_sylow Q split j μ T (hc.trans hT.symm) hs
  · let T : Sylow 2 J.specialSubgroup := Classical.choice inferInstance
    let e := HermitianForm.SylowOmega.specialSylowEquivProjective J T
    obtain ⟨hT,hs⟩ := projective_sylow_square_profile J hn hcard hconj
      (T.mapSurjective J.specialToProjective_surjective)
    exact root_square_profile_of_sylow Q split j μ T
      (hc.trans ((Nat.card_congr e.toEquiv).trans hT).symm)
      (square_commutator_transport e hs)

/-- The five-root product transports elementary root abelianizations to the literal radical abelianization. -/
theorem radical_frattini_eq_commutator_of_root_squares (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hsquare : ∀ k : Fin 2, ∀ x : simpleRoot Q split k,
      x^2 ∈ _root_.commutator (simpleRoot Q split k)) :
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
    exact square_commutator_transport e (hsquare _) x
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

include hn hcard hconj in
/-- Bounds, centralization and whole-root exclusions for the actual derived radical; its Frattini identification is proved internally. -/
theorem unitary_derived_radical_control
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = (2^n)^3) (han : a < 4*n)
    (hsquare : ∀ k : Fin 2, ∃ x : simpleRoot Q split k, x^2 ≠ 1)
    (hsq : ∀ k : Fin 2, ∀ x : simpleRoot Q split k,
      x^2 ∈ _root_.commutator (simpleRoot Q split k)) :
    let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    2^(6*n) ≤ Nat.card D ∧ Nat.card D ≤ 2^(3*a) ∧
      ⁅rankOne Q split j,(frattini D).map D.subtype⁆ = ⊥ ∧
      ∀ t : Fin 5, t ≠ 2 →
        ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤ D := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  let g := frattiniSection Q split j f
  have hPhi := radical_frattini_eq_commutator_of_root_squares Q split hm i j hij hsq
  have hD : f.numerator = D := by
    change (frattini V).map V.subtype = _
    rw [hPhi,map_subtype_commutator]
  have hcD : Nat.card D = Nat.card (frattini V) := by
    rw [←hD]
    exact Nat.card_congr ((frattini V).equivMapOfInjective V.subtype V.subtype_injective).symm.toEquiv
  have hlow := unitary_frattini_radical_card_bound J hn hcard hconj Q split j σ hσ
    hm i hij (UnitarySource.actorReflection Q split j) hKj (hsquare j)
  refine ⟨?_,?_,?_,?_⟩
  · rw [hcD]
    exact hlow.trans (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _))
  · rw [hcD]
    exact unitary_radical_frattini_card_upper Q split J hn hcard hconj hm i j hij hKj σ hσ hi hj
  · have hact := unitary_second_frattini_radical_action_eq_one Q split J hn hcard hconj
      hm i j hij hKj σ hσ hi hj han (hsquare j)
    change g.action = 1 at hact
    have he : g.numerator = (frattini D).map D.subtype := by
      change (frattini f.numerator).map f.numerator.subtype = _
      rw [hD]
    rw [←he]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro r hr x hx
    have hfix := congrArg (fun a : MulAut g.Carrier => a (QuotientGroup.mk (⟨x,hx⟩ : g.numerator)))
      (show g.action ⟨r,hr⟩ = 1 by rw [hact]; rfl)
    rw [g.action_mk] at hfix
    have hh := congrArg Subtype.val (congrArg QuotientGroup.quotientBot hfix)
    change r*x*r⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact unitary_nonmiddle_root_not_le_derived Q split J hn hcard hconj
      hm i j hij hKj σ hσ hi hj han hsquare

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
