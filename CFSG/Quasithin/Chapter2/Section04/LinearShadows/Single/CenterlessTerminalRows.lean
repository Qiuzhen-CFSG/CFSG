module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldCentralizerSupplement
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterCommutatorCardSource
/-!
# Original centerless terminal fixed-group rows

The field involution has a Sylow centralizer with the actual outside supplement.
The full-center fusion obstruction therefore applies without any independent
Sylow, orbit, TI or fixed-cardinality premise. The second theorem records the
exact orders of the field-fixed Thompson group and its fixed center for the
remaining unitary-type row on printed p.539.

Source: Aschbacher–Smith, 2.4.12, 2.4.23 and the end of the single-block
argument, printed pp.532 and 537–539.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_field_not_conj_to_full_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (i : G) (hiZ : distinguishedZ d ≤ centralizer ({i}:Set G)) : ¬IsConj i (s:G) := by
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  have hSylow := source_centerless_field_centralizer_sylow d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  obtain ⟨_,x,hx,hxS⟩ := source_field_centralizer_supplement d hG T hST hsingle hL hM hTM hu c s hs hs2 hsR
  exact source_field_involution_not_conj_to_full_center d hG T hST hsingle hL hM hTM hu c hZ
    s hs hs2 hsR hclosed hSylow x hx.1 hxS hx.2 i hiZ

theorem source_centerless_field_fixed_orders
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R:Set G)
    ∃ m : ℕ, 0<m ∧ n=2*m ∧ Nat.card (Z⊓centralizer ({(s:G)}:Set G) : Subgroup G)=2^m ∧
      Nat.card (R⊓centralizer ({(s:G)}:Set G) : Subgroup G)=2^(3*m) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R:Set G)
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hspow : (s:G)^2=1 := by simpa only [hsord] using pow_orderOf_eq_one (s:G)
  have hsnon : (s:G)∉centralizer (Z:Set G) := by
    intro hh
    have hSC : S⊓centralizer (Z:Set G)=R := by
      simpa only [distinguishedZ_of_centerless d hZ] using
        source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu
    exact hsR (hSC.le ⟨hs.1,hh⟩)
  obtain ⟨m,hm,hn,hJ⟩ := source_centerless_center_involution_fixed_card d hG T hST hsingle hL
    hM hTM hu c hZ s s.property hspow hsnon
  refine ⟨m,hm,hn,hJ,?_⟩
  have hc := source_field_thompson_centralizer_card_square d hG T hST hsingle hL hM hTM hu c s hs hsord
  change Nat.card (R⊓centralizer ({(s:G)}:Set G) : Subgroup G)^2=Nat.card R at hc
  have hRcard : Nat.card R=Nat.card Z^3 := source_centerless_sylow_card d hG T hST hsingle hL hM hTM hu hZ
  have hZcard : Nat.card Z=2^n := by
    simpa only [distinguishedZ_of_centerless d hZ] using
      (source_distinguished_elementary d hG T hST hsingle hL hM hTM hu).2.1
  rw [hRcard,hZcard,hn,←pow_mul] at hc
  apply (Nat.pow_left_inj (by decide : 2≠0)).mp
  rw [hc,←pow_mul]
  congr 1
  omega
end CFSG.Quasithin.Chapter2.LinearShadows.Single
