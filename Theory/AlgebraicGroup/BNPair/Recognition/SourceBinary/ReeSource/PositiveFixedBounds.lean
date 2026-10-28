module
public import Theory.Representation.Suzuki.SmallDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryFixedBounds
public import Theory.Representation.FrattiniAction

/-!
# Positive Suzuki fixed indices on small source sections

A faithful binary representation of positive-parameter Sz(q), of dimension
below 10 log₂(q), has a nontrivial irreducible section. Perfectness retains
nontriviality and simplicity gives faithfulness on that section. The proved
small-degree recognition identifies it with the natural module. Direct matrix
calculation gives fixed codimensions 3 log₂(q) and 2 log₂(q) for u(1,0) and
its square; invariant subquotients cannot increase these codimensions.

The final theorem applies both bounds to the literal effective Frattini
quotient of a source RootSection and the original marked root generator.
PositiveRadicalBounds discharges the size bound on the actual two layers.
The binary parameter has its separate BinaryFixedBounds argument.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the effective
module estimates preceding (6.1). This replaces the Hall--Higman step by the
existing Suzuki small-degree theorem; it does not assume a source natural
module or synchronized fields.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Representation Representation.BinaryOffender Representation.SuzukiNatural
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

def fourRoot (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m 1 0, subset_closure (Or.inl ⟨1,0,rfl⟩)⟩

private theorem fourRoot_action (m : ℕ) (v : W m) :
    natural m (fourRoot m) v = ![v 0+v 1+v 3,v 1+v 2+v 3,v 2+v 3,v 3] := by
  ext i
  fin_cases i <;> simp [natural_apply,fourRoot,SuzukiRootGL,SuzukiRootMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four,add_assoc]

private theorem fourRoot_fixed (m : ℕ) (v : W m) :
    natural m (fourRoot m) v = v ↔ v 1=0 ∧ v 2=0 ∧ v 3=0 := by
  rw [fourRoot_action]
  constructor
  · intro h
    have h3 : v 3=0 := by simpa using congrFun h 2
    have h2 : v 2=0 := by simpa [h3] using congrFun h 1
    have h1 : v 1=0 := by simpa [h3] using congrFun h 0
    exact ⟨h1,h2,h3⟩
  · rintro ⟨h1,h2,h3⟩
    ext i
    fin_cases i <;> simp [h1,h2,h3]

private theorem fourRoot_square_fixed (m : ℕ) (v : W m) :
    natural m (fourRoot m ^ 2) v = v ↔ v 2=0 ∧ v 3=0 := by
  rw [map_pow,pow_two,Module.End.mul_apply,fourRoot_action,fourRoot_action]
  constructor
  · intro h
    have h3 : v 3=0 := by simpa [CharTwo.add_self_eq_zero,add_assoc] using congrFun h 1
    have h2 : v 2=0 := by
      have hh : v 1+(v 1+v 2)=0 := by simpa [h3,add_assoc] using congrFun h 0
      simpa only [←add_assoc,CharTwo.add_self_eq_zero,zero_add] using hh
    exact ⟨h2,h3⟩
  · rintro ⟨h2,h3⟩
    ext i
    fin_cases i <;> simp [h2,h3,CharTwo.add_self_eq_zero,add_assoc]

private def fourFixedEquiv (m : ℕ) :
    fixedSpace (natural m) (zpowers (fourRoot m)) ≃ₗ[ZMod 2] F m where
  toFun v := v.val 0
  invFun a := ⟨![a,0,0,0],(mem_fixedSpace_zpowers_iff _ _ _).mpr
    ((fourRoot_fixed _ _).mpr (by simp))⟩
  left_inv v := by
    have hv := (fourRoot_fixed _ _).mp ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def squareFixedEquiv (m : ℕ) :
    fixedSpace (natural m) (zpowers (fourRoot m ^ 2)) ≃ₗ[ZMod 2] (Fin 2 → F m) where
  toFun v := ![v.val 0,v.val 1]
  invFun a := ⟨![a 0,a 1,0,0],(mem_fixedSpace_zpowers_iff _ _ _).mpr
    ((fourRoot_square_fixed _ _).mpr (by simp))⟩
  left_inv v := by
    have hv := (fourRoot_square_fixed _ _).mp ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [hv.1,hv.2]
  right_inv a := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

theorem natural_four_fixedCodim (m : ℕ) :
    fixedCodim (natural m) (zpowers (fourRoot m)) = 3*(2*m+1) ∧
    fixedCodim (natural m) (zpowers (fourRoot m ^ 2)) = 2*(2*m+1) := by
  have h1 := fixedCodim_add_finrank (natural m) (zpowers (fourRoot m))
  have h2 := fixedCodim_add_finrank (natural m) (zpowers (fourRoot m^2))
  rw [(fourFixedEquiv m).finrank_eq,natural_finrank] at h1
  rw [(squareFixedEquiv m).finrank_eq,Module.finrank_pi_fintype,natural_finrank] at h2
  simp only [F,GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h1 h2
  omega

/-- A small faithful section contains a natural constituent, so its fixed codimensions
are at least those of the literal natural root element and its square. -/
theorem small_suzuki_four_fixedCodim {m : ℕ} (hm : 0 < m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (hf : Function.Injective ρ) (hsmall : Module.finrank (ZMod 2) V < 10*(2*m+1)) :
    3*(2*m+1) ≤ fixedCodim ρ (zpowers (fourRoot m)) ∧
    2*(2*m+1) ≤ fixedCodim ρ (zpowers (fourRoot m^2)) := by
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
  have hb (A : Subgroup (SuzukiMatrixGroup m)) : fixedCodim (natural m) A ≤ fixedCodim ρ A := by
    have he := fixedCodim_map_equivariant σ (natural m) (MonoidHom.id _) e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A
    simp only [Subgroup.map_id] at he
    have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    have hu := fixedCodim_subrepresentation_le ρ U A
    change fixedCodim N.quotientRepresentation A = _ at he
    omega
  have hh := natural_four_fixedCodim m
  exact ⟨hh.1 ▸ hb _,hh.2 ▸ hb _⟩


private theorem automorphism_fixed_index {H V : Type*} [Group H] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (f : H →* MulAut V) (r : H) :
    (f r).fixedSubgroup.index = 2^fixedCodim (FrattiniAction.ofAutomorphismHom f) (zpowers r) := by
  let ρ := FrattiniAction.ofAutomorphismHom f
  let e : fixedSpace ρ (zpowers r) ≃ (f r).fixedSubgroup := {
    toFun v := ⟨v.val.toMul,(MulAut.mem_fixedSubgroup _ _).mpr
      (Additive.ofMul.injective ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property))⟩
    invFun v := ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff _ _ _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hd := fixedCodim_add_finrank ρ (zpowers r)
  have hc := (f r).fixedSubgroup.index_mul_card
  rw [←Nat.card_congr e] at hc
  have hV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (zpowers r))
  rw [Nat.card_zmod] at hV hF
  change Nat.card V = _ at hV
  rw [hV,hF,←hd,pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hc

/-- Fixed indices on every small faithful elementary source section. -/
theorem small_suzuki_four_fixed_indices {m : ℕ} (hm : 0 < m)
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (f : SuzukiMatrixGroup m →* MulAut V) (hf : Function.Injective f)
    (hsmall : Nat.card V ≤ (2^(2*m+1))^6) :
    (2^(2*m+1))^3 ≤ (f (fourRoot m)).fixedSubgroup.index ∧
    (2^(2*m+1))^2 ≤ (f (fourRoot m^2)).fixedSubgroup.index := by
  let ρ := FrattiniAction.ofAutomorphismHom f
  have hfaith : Function.Injective ρ := by
    intro g h he
    apply hf
    ext v
    exact Additive.ofMul.injective (DFunLike.congr_fun he (Additive.ofMul v))
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 6*(2*m+1) := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hc
    change Nat.card V = _ at hc
    rw [hc,←pow_mul,Nat.mul_comm (2*m+1) 6] at hsmall
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hsmall
  obtain ⟨h1,h2⟩ := small_suzuki_four_fixedCodim hm ρ hfaith (by omega)
  rw [automorphism_fixed_index,automorphism_fixed_index]
  constructor
  · simpa only [pow_mul,Nat.mul_comm 3 (2*m+1)] using
      Nat.pow_le_pow_right (by decide : 0 < 2) h1
  · simpa only [pow_mul,Nat.mul_comm 2 (2*m+1)] using
      Nat.pow_le_pow_right (by decide : 0 < 2) h2

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The chosen matrix is the literal marked source root generator. -/
theorem suzukiActorEquiv_fourRoot :
    suzukiActorEquiv Q split i m μ hB
      (inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)) = fourRoot m := by
  rw [suzukiActorEquiv_simpleRoot,suzukiParameter,MulEquiv.apply_symm_apply]
  rfl

include hB in
/-- The two fixed-index bounds on the actual source Frattini quotient. -/
theorem positive_section_fixed_indices (hm : 0 < m) (d : RootSection Q split i)
    (hd : d.denominator = ⊥) (hf : Function.Injective d.effectiveAction)
    (hsmall : Nat.card (d.numerator ⧸ frattini d.numerator) ≤ (2^(2*m+1))^6) :
    let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
    (2^(2*m+1))^3 ≤ (quotientAut (frattini d.numerator) (d.numeratorAction r)).fixedSubgroup.index ∧
    (2^(2*m+1))^2 ≤ (quotientAut (frattini d.numerator) (d.numeratorAction (r^2))).fixedSubgroup.index := by
  dsimp only
  let e := suzukiActorEquiv Q split i m μ hB
  let f := d.effectiveAction.comp e.symm.toMonoidHom
  let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
  have hdc : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq,hd,sup_bot_eq]
  have hsmall' : Nat.card d.EffectiveCarrier ≤ (2^(2*m+1))^6 := by
    change Nat.card (d.numerator ⧸ d.effectiveDenominator) ≤ _
    rwa [hdc]
  obtain ⟨h1,h2⟩ := small_suzuki_four_fixed_indices hm f (hf.comp e.symm.injective) hsmall'
  have hr : e r = fourRoot m := suzukiActorEquiv_fourRoot Q split i m μ hB
  rw [section_frattini_fixed_index Q split i d hd r,
    section_frattini_fixed_index Q split i d hd (r^2)]
  rw [←hr] at h1 h2
  constructor
  · simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using h1
  · simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,←map_pow,e.symm_apply_apply] using h2

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
