module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PositiveRadicalBounds

/-!
# Cubic movement of the marked Suzuki root on actual radical sections

The order-four element u(1,0) has a nonzero third difference on the
natural Suzuki module: its four coordinates form a Jordan chain. A small
faithful positive-parameter module has a natural irreducible subquotient;
intertwining the difference operator through that subquotient preserves
its nonzero cube. This proves movement without identifying the whole
source section with a natural module.

The literal effective actions on V/Phi(V) and [V,V]/Phi([V,V]) meet the
size threshold by the existing two-layer estimates. Lifting a moved
vector gives an actual triple commutator outside the corresponding
Frattini subgroup. The same marked root u(1,0), quotient maps, and
independent-field size comparison are retained.

Source: Fong--Seitz I (1973), pp.52--53, the assertion
[V_2,U_2,U_2,U_2] ≠ 1 in the positive-parameter near-commutator argument.
The CFSG CubicMovement consumer supplies the natural panel markings
and (6.3); OriginalCubicMovement retains both original endpoints and Q.q.
This module does not assert the remaining perpendicular support or near
commutator equality. The binary branch has its separate completed proof.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Representation Representation.SuzukiNatural
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private theorem map_difference_pow {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (f : V →ₗ[ZMod 2] V) (g : W →ₗ[ZMod 2] W) (a : V →ₗ[ZMod 2] W)
    (ha : ∀ v, a (f v) = g (a v)) (k : ℕ) (v : V) :
    a (((f-1)^k) v) = ((g-1)^k) (a v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_apply,LinearMap.sub_apply,Module.End.one_apply,
      map_sub,ha,ih]

/-- The actual natural order-four root has a nonzero third difference, for all parameters. -/
theorem natural_four_difference_cube_ne_zero (m : ℕ) :
    (natural m (fourRoot m)-1)^3 ≠ 0 := by
  intro hz
  have he := congrArg (fun f : Module.End (ZMod 2) (W m) => f ![0,0,0,1] 0) hz
  have ha (v : W m) : natural m (fourRoot m) v =
      ![v 0+v 1+v 3,v 1+v 2+v 3,v 2+v 3,v 3] := by
    ext i
    fin_cases i <;> simp [natural_apply,fourRoot,SuzukiRootGL,SuzukiRootMatrix,
      Matrix.mulVec,dotProduct,Fin.sum_univ_four,add_assoc]
  have hd (v : W m) : (natural m (fourRoot m)-1) v = ![v 1+v 3,v 2+v 3,v 3,0] := by
    rw [LinearMap.sub_apply,Module.End.one_apply,ha]
    ext i
    fin_cases i <;> simp [add_assoc]
  simp only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,hd] at he
  change ((1: F m)+0)+0 = 0 at he
  exact one_ne_zero (by simpa only [add_zero] using he)

/-- A small faithful positive Suzuki module retains the natural cubic movement. -/
theorem small_suzuki_four_difference_cube_ne_zero {m : ℕ} (hm : 0 < m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (hf : Function.Injective ρ) (hsmall : Module.finrank (ZMod 2) V < 10*(2*m+1)) :
    (ρ (fourRoot m)-1)^3 ≠ 0 := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := SchurCover.isPerfect m hm
  let : Group.IsPerfect (⊤ : Subgroup (SuzukiMatrixGroup m)) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := SuzukiMatrixGroup m)).symm.toMonoidHom) (topEquiv (G := SuzukiMatrixGroup m)).symm.surjective
  have hn : ¬ (⊤ : Subgroup (SuzukiMatrixGroup m)) ≤ ρ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
    exact not_le_of_gt bot_lt_top
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) ⊤ hn
  let σ := N.quotientRepresentation
  have hs : Function.Injective σ := (MonoidHom.ker_eq_bot_iff _).mp
    ((inferInstance : σ.ker.Normal).eq_bot_or_eq_top.resolve_right (fun h => hN h.ge))
  have hdim := (Submodule.finrank_quotient_le N.toSubmodule).trans
    (Submodule.finrank_le U.toSubmodule)
  obtain ⟨e⟩ := SuzukiSmallDegree.natural_equiv_of_smallDegree (by omega) σ hs hi (hdim.trans_lt hsmall)
  intro hz
  have hU : (U.toRepresentation (fourRoot m)-1)^3 = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have he' := map_difference_pow (U.toRepresentation (fourRoot m)) (ρ (fourRoot m))
      U.toSubmodule.subtype (fun _ => rfl) 3 v
    simpa only [hz,LinearMap.zero_apply,Submodule.subtype_apply,ZeroMemClass.coe_zero] using he'
  let a := e.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
  have ha (v : U) : a (U.toRepresentation (fourRoot m) v) = natural m (fourRoot m) (a v) := by
    exact LinearMap.congr_fun (e.isIntertwining' (fourRoot m)) (N.toSubmodule.mkQ v)
  have has : Function.Surjective a := e.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective
  apply natural_four_difference_cube_ne_zero m
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := has w
  rw [←map_difference_pow _ _ a ha 3 v,hU,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]

open RootCoordinates HexagonStructure
open scoped commutatorElement
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include hB in
/-- Cubic movement in the actual effective section, under its proved size bound. -/
theorem positive_section_difference_cube_ne_zero (hm : 0 < m) (d : RootSection Q split i)
    (hd : d.denominator = ⊥) (hf : Function.Injective d.effectiveAction)
    (hsmall : Nat.card (d.numerator ⧸ frattini d.numerator) ≤ (2^(2*m+1))^6) :
    let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
    (d.effectiveRepresentation r - 1)^3 ≠ 0 := by
  dsimp only
  let e := suzukiActorEquiv Q split i m μ hB
  let ρ := d.effectiveRepresentation.comp e.symm.toMonoidHom
  have hfaith : Function.Injective ρ :=
    (d.effectiveRepresentation_injective hf).comp e.symm.injective
  have hdc : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq,hd,sup_bot_eq]
  have hsmall' : Nat.card d.EffectiveCarrier ≤ (2^(2*m+1))^6 := by
    change Nat.card (d.numerator ⧸ d.effectiveDenominator) ≤ _
    rwa [hdc]
  have hdim : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) ≤ 6*(2*m+1) := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
    rw [Nat.card_zmod] at hc
    change Nat.card d.EffectiveCarrier = _ at hc
    rw [hc,←pow_mul,Nat.mul_comm (2*m+1) 6] at hsmall'
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hsmall'
  have hh := small_suzuki_four_difference_cube_ne_zero hm ρ hfaith (by omega)
  let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
  have hr : e.symm (fourRoot m) = r := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (suzukiActorEquiv_fourRoot Q split i m μ hB).symm
  change (d.effectiveRepresentation (e.symm (fourRoot m))-1)^3 ≠ 0 at hh
  rwa [hr] at hh

/-- A nonzero cubic difference supplies a literal triple commutator outside the denominator. -/
theorem section_exists_cubic_commutator (d : RootSection Q split i) (r : rankOne Q split i)
    (hmove : (d.effectiveRepresentation r - 1)^3 ≠ 0) :
    ∃ v : d.numerator, ⁅(r : X ⧸ Q.D),⁅(r : X ⧸ Q.D),⁅(r : X ⧸ Q.D),(v : X ⧸ Q.D)⁆⁆⁆ ∉
      d.effectiveDenominator.map d.numerator.subtype := by
  let δ : d.numerator → d.numerator := fun v => d.numeratorAction r v / v
  have hδ (v : d.numerator) : (δ v : X ⧸ Q.D) = ⁅(r : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ := by
    change ((r : X ⧸ Q.D)*v*(r : X ⧸ Q.D)⁻¹)/(v : X ⧸ Q.D) = _
    rw [div_eq_mul_inv,commutatorElement_def]
  have hstep (v : d.numerator) :
      (d.effectiveRepresentation r - 1) (Additive.ofMul (QuotientGroup.mk v)) =
        Additive.ofMul (QuotientGroup.mk (δ v)) := rfl
  by_contra hn
  push Not at hn
  apply hmove
  apply LinearMap.ext
  intro w
  obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator w.toMul
  have hv' : Additive.ofMul (QuotientGroup.mk v) = w := congrArg Additive.ofMul hv
  rw [←hv']
  have hδmem : δ (δ (δ v)) ∈ d.effectiveDenominator := by
    have he := hn v
    rw [←hδ,←hδ,←hδ] at he
    obtain ⟨x,hx,hxe⟩ := he
    exact (Subtype.ext hxe : x = δ (δ (δ v))) ▸ hx
  have hz : QuotientGroup.mk (δ (δ (δ v))) = (1 : d.EffectiveCarrier) :=
    (QuotientGroup.eq_one_iff _).mpr hδmem
  simp only [pow_succ',pow_zero,Module.End.one_apply,Module.End.mul_apply,hstep,
    hz,LinearMap.zero_apply]
  rfl

include hB in
/-- The source radical has a triple commutator outside its actual Frattini subgroup. -/
theorem positive_radical_cubic_movement
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) (hmpos : 0 < m)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j) ≤ 2^(2*m+1)) :
    let u := (suzukiParameter Q split i m μ hB 1 0 : X ⧸ Q.D)
    ∃ v : simpleRemainder Q split i, ⁅u,⁅u,⁅u,(v : X ⧸ Q.D)⁆⁆⁆ ∉
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  dsimp only
  let d := radicalSection Q split i hV
  have hh := section_exists_cubic_commutator Q split i d
    (inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0))
    (positive_section_difference_cube_ne_zero Q split i m μ hB hmpos d rfl
      (radical_effectiveAction_injective Q split i hV hc)
      (radical_two_layers_card_le Q split i hV m μ hB hc hm j hij hcomm hsize).1)
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  rwa [hd] at hh

include hB in
/-- The same marked root has cubic movement on the actual derived radical section. -/
theorem positive_derived_cubic_movement
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) (hmpos : 0 < m)
    (hsize : Nat.card (simpleRoot Q split j) ≤ 2^(2*m+1)) :
    let D : Subgroup (X ⧸ Q.D) := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
    let u := (suzukiParameter Q split i m μ hB 1 0 : X ⧸ Q.D)
    ∃ v : D, ⁅u,⁅u,⁅u,(v : X ⧸ Q.D)⁆⁆⁆ ∉ (frattini D).map D.subtype := by
  dsimp only
  let V := simpleRemainder Q split i
  let d := derivedRadicalSection Q split i hV
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hDc : Nat.card d.numerator = Nat.card (commutator V) := by
    change Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) = _
    rw [←map_subtype_commutator,card_map_of_injective V.subtype_injective]
  have hsmall : Nat.card (d.numerator ⧸ frattini d.numerator) ≤ (2^(2*m+1))^6 := by
    calc
      _ ≤ Nat.card d.numerator := Nat.card_le_card_of_surjective
        (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      _ = Nat.card (commutator V) := hDc
      _ ≤ Nat.card (frattini V) := card_le_of_le (commutator_le_frattini_of_isPGroup (p := 2))
      _ ≤ (2^(2*m+1))^2*Nat.card (simpleRoot Q split j)^4 :=
        suzuki_radical_frattini_card_le Q split i j m μ hB hV hc hm hij
      _ ≤ (2^(2*m+1))^2*(2^(2*m+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 4)
      _ = _ := by ring
  have hh := section_exists_cubic_commutator Q split i d
    (inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0))
    (positive_section_difference_cube_ne_zero Q split i m μ hB hmpos d rfl
      (derivedRadical_effectiveAction_injective Q split i hV m μ hB hm hmpos) hsmall)
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  rwa [hd] at hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
