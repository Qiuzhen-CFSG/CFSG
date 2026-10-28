module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Assembly
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import Theory.GroupAction.SubgroupConjugation

/-!
# Earlier-source inputs to the odd centralizer assembly

The original Choices give exactly a SingerChoice. The proved J.2.3
statements supply its fixed four-group, internal Sylow product and
Suzuki moving factor. To match the recognition API, the cyclic
involution action first puts every involution in V. The literal
order-seven Singer group is then transitive on these involutions;
a nontrivial stabilizer would be the whole prime-order group and
contradict C_V(B₇)=1. This proves regularity and faithfulness.

The final application discharges all J.2.3 inputs of J.2.9. Only the
specified J.2.7(7),(8),(10) embedding, fusion and Sylow-centralizer
witnesses remain. No SQTK or model-recognition premise is introduced.

Source: Aschbacher–Smith, J.2.3 and J.2.9, printed pp.433–434,438
(PDF pp.444–445,449).
-/

@[expose] public section
open Subgroup BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Reuse exactly the original Singer subgroup and cubic normalizing action. -/
def toSingerChoice : SpecialCore.SingerChoice d.toTypeRuSetup c.sylowThree :=
  ⟨c.B7, c.B7_le, c.B7_card, c.B_normalizes⟩

/-- The source cubic subgroup has order three by J.2.1 and the local quotient. -/
theorem B_card_source : Nat.card c.B = 3 :=
  SpecialCore.cubicSubgroup_card d.toTypeRuSetup c.sylowThree d.card_Z
    (d.center_eq.le.trans inf_le_left)

/-- The literal seven-subgroup is transitive on the nonidentity elements of V. -/
theorem B7_transitive_source : c.B7TransitiveOnV := by
  intro v hv hv1 w hw hw1
  exact c.toSingerChoice.transitive_V d.toTypeRuSetup c.sylowThree v w hv hw hv1 hw1

/-- J.2.3 supplies the full faithful, regular Suzuki two-group action used by recognition. -/
theorem S1_suzuki_source : IsSuzukiTwoGroup c.S1 := by
  have h5 := (c.toSingerChoice.source_conclusions d c.sylowThree).five c.s c.s_mem c.s_ne_one
  change IsPGroup 2 c.S1 ∧ ¬ IsMulCommutative c.S1 ∧
    _root_.commutator c.S1 = center c.S1 ∧
    ∃ A : Subgroup (MulAut c.S1), IsCyclic A ∧
      ∀ x y : c.S1, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y at h5
  obtain ⟨h2, hnab, hderived, A, hA, htransA⟩ := h5
  have hVL := c.V_le_S1 hnab c.B7_transitive_source
  have hD := c.S1_derived_eq_V hnab c.B7_transitive_source
  have hvpow (v : G) (hv : v ∈ d.V) : v ^ 2 = 1 :=
    congrArg Subtype.val (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨v, hv⟩)
  have hV (x : c.S1) (hx : IsInvolution x) : (x : G) ∈ d.V := by
    have hne : _root_.commutator c.S1 ≠ ⊥ :=
      fun he => hnab ((commutator_eq_bot_iff c.S1).mp he)
    obtain ⟨⟨v, hv⟩, hv1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hvV : (v : G) ∈ d.V := hD ▸ mem_map_of_mem c.S1.subtype hv
    have hv2 : IsInvolution v := ⟨fun he => hv1 (Subtype.ext he), Subtype.ext (hvpow v hvV)⟩
    have order_two {x : c.S1} (hx : IsInvolution x) : orderOf x = 2 :=
      orderOf_eq_prime hx.2 hx.1
    obtain ⟨a, ha, he⟩ := htransA v x (order_two hv2) (order_two hx)
    have hm : a v ∈ _root_.commutator c.S1 :=
      (characteristic_iff_map_le.mp (_root_.instCharacteristicCommutator c.S1) a) (mem_map_of_mem a.toMonoidHom hv)
    rw [he] at hm
    exact hD ▸ mem_map_of_mem c.S1.subtype hm
  let : Nontrivial d.V := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.ru1.card_V]; decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : d.V)
  obtain ⟨w, hw, hwv⟩ := ENat.exists_ne_ne_of_three_le (α := d.V)
    (by simp only [ENat.card_eq_coe_natCard, d.ru1.card_V]; decide) 1 v
  let v' : c.S1 := ⟨v, hVL v.property⟩
  let w' : c.S1 := ⟨w, hVL w.property⟩
  have hv' : IsInvolution v' :=
    ⟨fun he => hv (Subtype.ext (congrArg (fun x : c.S1 => (x : G)) he)), Subtype.ext (hvpow v v.property)⟩
  have hw' : IsInvolution w' :=
    ⟨fun he => hw (Subtype.ext (congrArg (fun x : c.S1 => (x : G)) he)), Subtype.ext (hvpow w w.property)⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic c.B7 := isCyclic_of_prime_card c.B7_card
  let : MulDistribMulAction c.B7 c.S1 :=
    conjMulDistribMulActionOfLeNormalizer c.B7 c.S1 (normalizer_commutator_ge_right c.Ts c.B7)
  have hfree (x : c.S1) (hx : IsInvolution x) (a : c.B7) (ha : a • x = x) : a = 1 := by
    by_contra ha1
    have hall : (⊤ : Subgroup c.B7) ≤ MulAction.stabilizer c.B7 x := by
      rw [← zpowers_eq_top_of_prime_card c.B7_card ha1]
      exact zpowers_le.mpr ha
    have hxE : (x : G) ∈ c.S0 := by
      refine ⟨(c.S1_le_Ts x.property).1, ?_⟩
      intro b hb
      have he := congrArg Subtype.val (hall (show (⟨b, hb⟩ : c.B7) ∈ ⊤ from trivial))
      change b * (x : G) * b⁻¹ = (x : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have he := disjoint_def.mp (c.toSingerChoice.fixedCore_disjoint_V d.toTypeRuSetup c.sylowThree)
      hxE (hV x hx)
    exact hx.1 (Subtype.ext he)
  have hfaith : FaithfulSMul c.B7 c.S1 := by
    rw [faithfulSMul_iff]
    intro a ha
    exact hfree v' hv' a (ha v')
  have hreg : ActionRegularOn c.B7 c.S1 (involutions c.S1) := by
    constructor
    · intro x hx a
      let f : MulAut c.S1 := MulDistribMulAction.toMulAut c.B7 c.S1 a
      exact ⟨fun he => hx.1 (f.injective (he.trans f.map_one.symm)),
        by change (f x) ^ 2 = 1; rw [← map_pow, hx.2, map_one]⟩
    · intro x hx y hy
      obtain ⟨b, hb, he⟩ := c.B7_transitive_source x (hV x hx)
        (fun he => hx.1 (Subtype.ext he)) y (hV y hy) (fun he => hy.1 (Subtype.ext he))
      let b' : c.B7 := ⟨b, hb⟩
      have hb' : y = b' • x := Subtype.ext he.symm
      refine ⟨b', hb', ?_⟩
      intro a ha
      have heq : (b'⁻¹ * a) • x = x := by rw [mul_smul, ← ha, hb', inv_smul_smul]
      exact (inv_mul_eq_one.mp (hfree x hx _ heq)).symm
  refine ⟨?_, hnab, ⟨v', w', hv', hw', ?_⟩, c.B7, inferInstance, inferInstance,
    inferInstance, hfaith, hreg⟩
  · obtain ⟨n, hn⟩ := h2.exists_card_eq
    exact ⟨n, (Nat.card_congr (topEquiv (G := c.S1)).toEquiv).trans hn⟩
  · intro he
    exact hwv (Subtype.ext (congrArg (fun x : c.S1 => (x : G)) he.symm))

/-- The source fixed subgroup is elementary abelian. -/
theorem S0_elementary_source : IsElementaryAbelian 2 c.S0 := by
  let e : c.S0 ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    c.toSingerChoice.fixedCoreEquivFour d.toTypeRuSetup c.sylowThree
  refine {
    toIsMulCommutative := c.toSingerChoice.fixedCore_commutative d.toTypeRuSetup c.sylowThree
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply e.injective
  rw [map_pow, map_one, pow_two]
  change (e x).toAdd + (e x).toAdd = 0
  exact CharTwo.add_self_eq_zero _

/-- The source fixed subgroup has order four. -/
theorem S0_card_source : Nat.card c.S0 = 4 :=
  c.toSingerChoice.fixedCore_card d.toTypeRuSetup c.sylowThree

/-- The full centralizer in L is the literal Singer supplement of the two-centralizer. -/
theorem local_centralizer_source : d.L ⊓ c.Gs = c.Ts ⊔ c.B7 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := c.toSingerChoice.fullCentralizer_factor
      d.toTypeRuSetup c.sylowThree c.s c.s_mem c.s_ne_one x hx
    exact (c.Ts ⊔ c.B7).mul_mem (mem_sup_left ha) (mem_sup_right hb)
  · exact sup_le (inf_le_inf d.ru1.steinberg.section_le le_rfl)
      (le_inf c.B7_le c.B7_le_Gs)

/-- J.2.9 after supplying the precise fusion and Sylow data from J.2.7(7),(8),(10). -/
theorem suzuki_recognition_of_J27
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = t)
    {t : G} (hst : IsConj c.s t)
    (f : Multiplicative (ZMod 2) × BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 →*
      centralizer ({t} : Set G)) (hf : Function.Injective f)
    (hzfusion : ∀ u : Multiplicative (ZMod 2) × BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
      u.1 = 1 → orderOf u = 2 → IsConj c.z (f u : G)) :
    Nonempty c.SuzukiSourceConclusion := by
  let := c.S0_elementary_source
  have h3 := (c.toSingerChoice.source_conclusions d c.sylowThree).three c.s c.s_mem c.s_ne_one
  obtain ⟨a, ha⟩ := h3.2.1
  change c.S0 × c.S1 ≃* c.Ts at a
  have hTs : c.Ts ≤ c.Gs := inf_le_right
  let e0 : P ≃* c.Ts := (MulEquiv.subgroupCongr hP).trans (subgroupOfEquivOfLe hTs)
  let e : P ≃* c.S0 × c.S1 := e0.trans a.symm
  have he (x : P) : ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G) := by
    have hh := ha (a.symm (e0 x)).1 (a.symm (e0 x)).2
    change (a (a.symm (e0 x)) : G) = _ at hh
    rw [a.apply_symm_apply] at hh
    exact hh
  have hz1 : c.z ≠ 1 := by
    intro hz
    have hh := c.z_generator
    rw [hz, zpowers_one_eq_bot] at hh
    have hcard := d.card_Z
    simp [hh] at hcard
  exact c.source_suzuki_recognition P hP e he c.S0_card_source h3.2.2.2.1
    c.B_card_source c.S1_suzuki_source c.B7_transitive_source c.local_centralizer_source
    c.H_eq_centralizer_z.symm hHs (d.center_eq.le c.z_mem_Z).1 hz1 hsfusion hst f hf hzfusion

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
