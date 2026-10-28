module

public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Exchange
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Mathlib.GroupTheory.IndexNormal

/-!
# The opposite five-subgroups generate the source SL₂(5)

The original edge E=B₅ C_P(u) has order25 and is self-centralizing.
It has index five in each of the two actual extraspecial cores, so both
opposite fixed fives normalize it. Their join K centralizes zu, whereas
zu inverts E. Thus the conjugation kernel K∩C_G(E) is trivial.

Coordinates on the same E give a faithful GL₂(5) representation. The
opposite factors are distinct and have order five, so the general
five-generator theorem identifies the literal K with SL₂(5). The
coordinate-action equation and the original ambient subgroups remain
available alongside that equivalence. The final existence export uses
only the original source inputs.

Source: Aschbacher–Smith, discussion preceding J.4.8 and J.4.9(1),
printed pp.442–443, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Centralizers Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)

abbrev edge (u : G) : Subgroup G := B5Image B5 ⊔ fixedFive B5 u
abbrev oppositePair (u : G) : Subgroup G := fixedFive B5 (c.z*u) ⊔ nextFive c B5 u

omit [Finite G] in
private theorem normalizes_twentyfive {E P : Subgroup G}
    (hEP : E≤P) (hE : Nat.card E=25) (hP : Nat.card P=125) :
    P≤normalizer (E : Set G) := by
  have hc : Nat.card (E.subgroupOf P)=25 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv,hE]
  have hi : (E.subgroupOf P).index=5 := by
    have h := (E.subgroupOf P).index_mul_card
    rw [hc,hP] at h
    omega
  have hn : (E.subgroupOf P).Normal := normal_of_index_eq_minFac_card (by
    rw [hi,hP]; norm_num)
  exact (normal_subgroupOf_iff_le_normalizer hEP).mp hn

theorem opposite_pair_normalizes_edge (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    oppositePair c B5 u≤normalizer (edge B5 u : Set G) := by
  have hE := base_fixed_card c B5 u hu huz hi
  have hP := SourceCompletion.five_oddPart_card c B5
  have hn1 := normalizes_twentyfive
    (show edge B5 u≤fiveOddPart B5 from
      sup_le (B5Image_le_fiveOddPart d.card_Z B5) inf_le_left) hE hP
  have hs := next_five_structure c B5 u hu huz hi
  have hA : fixedFive B5 u≤coreAt (fixedFive B5 u) := by
    calc
      fixedFive B5 u = (center (coreAt (fixedFive B5 u))).map
        (coreAt (fixedFive B5 u)).subtype := hs.2.2.1.symm
      _ ≤ coreAt (fixedFive B5 u) := map_subtype_le _
  have hB : B5Image B5≤coreAt (fixedFive B5 u) :=
    le_sup_left.trans hs.2.2.2.1.le
  have hn2 := normalizes_twentyfive (sup_le hB hA) hE hs.2.1
  exact sup_le (inf_le_left.trans hn1) (inf_le_left.trans hn2)

theorem product_inverts_edge (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    ∀ x∈edge B5 u,(c.z*u)*x*(c.z*u)⁻¹=x⁻¹ := by
  have hnorm : fixedFive B5 u≤normalizer (B5Image B5 : Set G) :=
    (le_centralizer_iff.mp (central_edge B5 u)).trans (Subgroup.centralizer_le_normalizer _)
  intro x hx
  have hx' : x∈(B5Image B5 : Set G)*(fixedFive B5 u : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hx'
  have hta := inverts_product c B5 u hi a ha
  have htb : (c.z*u)*b*(c.z*u)⁻¹=b⁻¹ := by
    calc
      _ = c.z*(u*b*u⁻¹)*c.z⁻¹ := by group
      _ = c.z*b*c.z⁻¹ := by
        rw [← mem_centralizer_singleton_iff.mp hb.2,mul_inv_cancel_right]
      _ = b⁻¹ := base_inverts_fixed c B5 u hu huz hi b hb
  calc
    _ = ((c.z*u)*a*(c.z*u)⁻¹)*((c.z*u)*b*(c.z*u)⁻¹) := by group
    _ = a⁻¹*b⁻¹ := by rw [hta,htb]
    _ = (a*b)⁻¹ := by
      rw [mul_inv_rev]
      exact (show Commute a b from (central_edge B5 u ha b hb).symm).inv_inv.eq

/-- The literal conjugation representation of the opposite pair on the same edge. -/
def oppositeAction (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    oppositePair c B5 u →* MulAut (edge B5 u) :=
  (edge B5 u).normalizerMonoidHom.comp
    (inclusion (opposite_pair_normalizes_edge c B5 u hu huz hi))

theorem oppositeAction_injective (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    Function.Injective (oppositeAction c B5 u hu huz hi) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hCE : (x:G)∈centralizer (edge B5 u : Set G) := by
    intro a ha
    have he := congrArg (fun f:MulAut (edge B5 u) => (f ⟨a,ha⟩:G)) hx
    change (x:G)*a*(x:G)⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxE : (x:G)∈edge B5 u := by
    change (x:G)∈B5Image B5 ⊔ fixedFive B5 u
    rw [← centralizer_base_fixed c B5 u hu huz hi]
    exact hCE
  have hKc : oppositePair c B5 u≤centralizer ({c.z*u}:Set G) :=
    sup_le inf_le_right inf_le_right
  have hcomm := mem_centralizer_singleton_iff.mp (hKc x.property)
  have he := product_inverts_edge c B5 u hu huz hi x hxE
  have hx2 : (x:G)^2=1 := by
    have he' : (x:G)=(x:G)⁻¹ := by
      simpa only [← hcomm,mul_inv_cancel_right] using he
    calc
      (x:G)^2 = (x:G)*(x:G) := pow_two _
      _ = (x:G)⁻¹*(x:G) := congrArg (· * (x:G)) he'
      _ = 1 := inv_mul_cancel _
  have hx25 : (x:G)^25=1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hxE⟩:edge B5 u))
    rw [base_fixed_card c B5 u hu huz hi] at hh
    exact congrArg Subtype.val hh
  apply Subtype.ext
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
    (show orderOf (x:G)∣1 from Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2)
      (orderOf_dvd_of_pow_eq_one hx25)))

/-- Coordinates of the same source edge give a faithful binary-free prime-plane
representation; the evaluation equation retains original conjugation. -/
theorem opposite_pair_linear_action (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    ∃ (b : edge B5 u ≃* Multiplicative (Fin 2 → ZMod 5))
      (ρ : oppositePair c B5 u →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)),
      Function.Injective ρ ∧ ∀ k v,
        Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.planeAction 5 (ρ k) (b v)=
          b (oppositeAction c B5 u hu huz hi k v) := by
  let : IsElementaryAbelian 5 (edge B5 u) := base_fixed_elementary c B5 u hu huz hi
  obtain ⟨b,e,he⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
    (p:=5) (V:=edge B5 u) (base_fixed_card c B5 u hu huz hi)
  exact ⟨b,e.toMonoidHom.comp (oppositeAction c B5 u hu huz hi),
    e.injective.comp (oppositeAction_injective c B5 u hu huz hi),fun k v => he _ _⟩

/-- The opposite source fives generate the actual SL₂(5), using their
faithful action on the original self-centralizing order-twenty-five edge. -/
theorem opposite_pair_equiv_SL2 (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    Nonempty (oppositePair c B5 u ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  let K := oppositePair c B5 u
  let X := fixedFive B5 (c.z*u)
  let Y := nextFive c B5 u
  have hX : X≤K := le_sup_left
  have hY : Y≤K := le_sup_right
  have hcX : Nat.card (X.subgroupOf K)=5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
    exact (source_three_fives c B5 u hu huz hi).2.1
  have hcY : Nat.card (Y.subgroupOf K)=5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv]
    exact (next_five_structure c B5 u hu huz hi).1
  have hne : X.subgroupOf K≠Y.subgroupOf K := by
    intro he
    have he' : X=Y := by
      have h := congrArg (Subgroup.map K.subtype) he
      rwa [map_subgroupOf_eq_of_le hX,map_subgroupOf_eq_of_le hY] at h
    apply (next_five_structure c B5 u hu huz hi).2.2.2.2.2
    change B5Image B5≤centralizer (Y : Set G)
    rw [← he']
    exact central_edge B5 (c.z*u)
  have hgen : X.subgroupOf K ⊔ Y.subgroupOf K=⊤ := by
    apply Subgroup.map_injective (f:=K.subtype) K.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hX,map_subgroupOf_eq_of_le hY,
      ← MonoidHom.range_eq_map,K.range_subtype]
  obtain ⟨b,ρ,hρ,_⟩ := opposite_pair_linear_action c B5 u hu huz hi
  exact Matrix.GeneralLinearGroup.equiv_sl2_of_five_generators
    (X.subgroupOf K) (Y.subgroupOf K) hcX hcY hne hgen ρ hρ

/-- Original-source existence of the opposite SL₂(5) row. -/
theorem exists_source_opposite_pair :
    ∃ u:G, u∈d.toTypeRuSetup.H ∧ IsConj u c.z ∧
      (∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) ∧ (fourFives c B5 u).card=4 ∧
      Nonempty (oppositePair c B5 u ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨r⟩ := c.fiveInverterData_source B5
  exact ⟨r.i,r.mem_H,r.z_class,r.inverts,
    four_fives_card c B5 r.i r.mem_H r.z_class r.inverts,
    opposite_pair_equiv_SL2 c B5 r.i r.mem_H r.z_class r.inverts⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
