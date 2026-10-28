module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PrimeFixedIndex

/-!
# The exact derived product in the source Suzuki radical

The perpendicular root E meets Φ(V) in Ω₁(E), so its image in V/Φ(V)
has order q and is fixed by the whole Suzuki actor. A primitive prime
in that faithful action forces fixed index at least q⁴, including q=2.
Thus |V/Φ(V)| ≥ q⁵ and |Φ(V)| ≤ q⁵. The five already constructed
commuting root factors have that order and lie in Φ(V)=[V,V], proving
the exact (6H)(f) product and the vanishing of the second Frattini layer.

OriginalDerivedProduct retains the original two-core and literal Q.q;
Section10DerivedProduct discharges the product and square clauses of
(10.3) at every actual N-conjugate. Natural panel markings and odd linear
degree remain the earlier inputs. The center clauses and final marked
recognition remain separate source obligations.
Source: Fong--Seitz I (1973), (6H)(f), printed p.55; II (1974), (10.3), p.221.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include μ hB in
private theorem perpendicular_card :
    Nat.card (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) = (2^(2*m+1))^2 := by
  change Nat.card (rightConjugate (simpleRoot Q split 1)
    (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = _
  rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1)
    (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
    Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]

include μ hB in
private theorem perpendicular_omega_card :
    Nat.card (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) =
      2^(2*m+1) := by
  let f := (MulAut.conj (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map f.toMonoidHom =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective f.toMonoidHom f.injective,
    card_map_of_injective f.injective]
  exact suzukiOmega_card Q split 1 m μ hB

include ν hC μ hB hn in
/-- The perpendicular root supplies q fixed points on the faithful radical
Frattini quotient, forcing its order to be at least q⁵. -/
theorem source_radical_frattini_quotient_card_ge_five
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (2^(2*m+1))^5 ≤ Nat.card
      (simpleRemainder Q split 1 ⧸ frattini (simpleRemainder Q split 1)) := by
  let V := simpleRemainder Q split 1
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let d := radicalSection Q split 1 hV
  have hd : d.effectiveDenominator = frattini V := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  let : (d.effectiveDenominator : Subgroup V).Normal := d.effectiveDenominator_normal
  have hEV : E ≤ V := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
  let π : E →* d.EffectiveCarrier := (QuotientGroup.mk' d.effectiveDenominator).comp (inclusion hEV)
  have hker : π.ker = (omegaOneAmbient E).subgroupOf E := by
    ext x
    have hmem : π x = 1 ↔ inclusion hEV x ∈ frattini V := by
      change QuotientGroup.mk (inclusion hEV x) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff,hd]
    rw [MonoidHom.mem_ker,hmem]
    change inclusion hEV x ∈ frattini V ↔ (x : X ⧸ Q.D) ∈ omegaOneAmbient E
    have hI := source_derived_inf_perpendicular_eq_omega Q split n hn m ν T hC μ hB hm hcore hc
    rw [source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc] at hI
    constructor
    · intro hx
      exact hI.le ⟨⟨inclusion hEV x,hx,rfl⟩,x.property⟩
    · intro hx
      obtain ⟨y,hy,he⟩ := (hI.ge hx).1
      have he' : y = inclusion hEV x := Subtype.ext he
      exact he' ▸ hy
  have hkcard : Nat.card π.ker = 2^(2*m+1) := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe (omegaOneAmbient_le E)).toEquiv]
    exact perpendicular_omega_card Q split m μ hB
  have hπcard : Nat.card π.range = 2^(2*m+1) := by
    have h := π.ker.card_mul_index
    rw [index_ker,hkcard,perpendicular_card Q split m μ hB] at h
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(2*m+1))
    simpa only [pow_two] using h
  let e := suzukiActorEquiv Q split 1 m μ hB
  let f : SuzukiMatrixGroup m →* MulAut d.EffectiveCarrier := d.effectiveAction.comp e.symm.toMonoidHom
  have hf : Function.Injective f :=
    (radical_effectiveAction_injective Q split 1 hV hc).comp e.symm.injective
  obtain ⟨g,hg⟩ := suzuki_exists_large_fixed_index (d.isTwo.to_quotient d.effectiveDenominator) m f hf
  have hfixed : π.range ≤ (f g).fixedSubgroup := by
    rintro z ⟨x,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change d.effectiveAction (e.symm g) (QuotientGroup.mk (inclusion hEV x)) =
      QuotientGroup.mk (inclusion hEV x)
    rw [d.effectiveAction_mk]
    congr 1
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    have hx := (source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).ge x.property
    have hcomm := mem_centralizer_iff.mp hx.2 (e.symm g : X ⧸ Q.D) (e.symm g).property
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D)⁻¹ = x
    rw [hcomm,mul_inv_cancel_right]
  have hfixedcard : 2^(2*m+1) ≤ Nat.card (f g).fixedSubgroup := by
    rw [←hπcard]
    exact Nat.card_le_card_of_injective (inclusion hfixed) (inclusion_injective _)
  have hbound : (2^(2*m+1))^5 ≤ Nat.card d.EffectiveCarrier := by
    calc
      _ = (2^(2*m+1))^4 * 2^(2*m+1) := by ring
      _ ≤ (f g).fixedSubgroup.index * Nat.card (f g).fixedSubgroup := Nat.mul_le_mul hg hfixedcard
      _ = _ := (f g).fixedSubgroup.index_mul_card
  change _ ≤ Nat.card (V ⧸ d.effectiveDenominator) at hbound
  rwa [hd] at hbound

include ν hC μ hB hn in
/-- The exact five-factor derived subgroup in (6H)(f), including Sz(2). -/
theorem source_radical_derived_eq_five
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ = fiveDerivedSubgroup Q split := by
  apply Eq.symm
  apply eq_of_le_of_card_ge (source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc)
  rw [source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc,
    source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc,
    card_map_of_injective (simpleRemainder Q split 1).subtype_injective]
  let V := simpleRemainder Q split 1
  let q := 2^(2*m+1)
  have hsize : Nat.card V = q^10 := by
    rw [suzuki_octagon_radical_card Q split 1 0 m μ hB hm (by decide),
      ←rootAt_one Q split 0,linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB
        (UnitarySource.actorReflection Q split) hcore]
    dsimp only [q]
    ring
  have hquot := source_radical_frattini_quotient_card_ge_five Q split n hn m ν T hC μ hB hm hcore hc
  have hmul := (frattini V).card_mul_index
  change Nat.card (frattini V) * Nat.card (V ⧸ frattini V) = Nat.card V at hmul
  have hb : Nat.card (frattini V)*q^5 ≤ q^5*q^5 := by
    calc
      _ ≤ Nat.card (frattini V)*Nat.card (V ⧸ frattini V) := Nat.mul_le_mul_left _ hquot
      _ = Nat.card V := hmul
      _ = _ := hsize.trans (by ring)
  exact Nat.le_of_mul_le_mul_right hb (by dsimp [q]; positivity)

include ν hC μ hB hn in
/-- The actual derived radical is elementary abelian of order q⁵. -/
theorem source_radical_derived_data
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    IsElementaryAbelian 2 (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ :
        Subgroup (X ⧸ Q.D)) ∧
      Nat.card (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ :
        Subgroup (X ⧸ Q.D)) = (2^(2*m+1))^5 := by
  rw [source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm hcore hc]
  exact ⟨(source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1,
    source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc⟩

include ν hC μ hB hn in
/-- The second Frattini layer vanishes, as required in (10.3). -/
theorem source_radical_second_frattini_eq_bot
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    frattini ((frattini (simpleRemainder Q split 1)).map
      (simpleRemainder Q split 1).subtype) = ⊥ := by
  rw [←source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc]
  let : IsElementaryAbelian 2 (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ :
      Subgroup (X ⧸ Q.D)) := (source_radical_derived_data Q split n hn m ν T hC μ hB hm hcore hc).1
  let : Fact (IsPGroup 2 (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ :
      Subgroup (X ⧸ Q.D))) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
