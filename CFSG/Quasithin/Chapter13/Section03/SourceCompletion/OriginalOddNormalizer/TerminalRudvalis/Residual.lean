module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisFusion
public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFour
public import Theory.GroupTheory.SylowKernelCore

/-!
# The actual terminal fixed residual in Rudvalis

The original factorization L = R O₂(L), for R = C_L(A)∞, realizes the
natural module's transitivity inside R itself. The compatible original
quotient map shows that O₂(R) centralizes this module. Under any faithful
embedding of this same R in Rudvalis, the native order and two-rank bounds
then identify O₂(R) with the whole original V, of order 64, and give
|R| = 64 · 6048. Every nonidentity module element is in the central
involution class, with its actual ambient point centralizer.

No failure of residual uniqueness is assumed. The terminal component
application, including its literal embedding and original flag, is in
TerminalRudvalis.Marking.
Source: Aschbacher--Smith 4.4.5 and the inspection in 4.4.3 case (c),
printed pp.620 and 622--623, using the native calculation of 4.2.13.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem original_core_centralizes (s : Context T L V) :
    L.pCoreIn 2 ≤ centralizer (V : Set G) := by
  apply le_trans _ s.chosen.core_centralizes
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
    ((pCoreIn_le 2 L).trans le_sup_left)
    ((sup_le L.le_normalizer s.chosen.sylow_normalizes_component).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))

/-- The fixed residual itself fuses all nonidentity elements of the original V. -/
theorem unitary_original_terminal_residual_fusion (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    ∀ x ∈ V, ∀ y ∈ V, x ≠ 1 → y ≠ 1 →
      ∃ r ∈ oddActorResidual L A, r*x*r⁻¹ = y := by
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hcover := (chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV).1
  have hQV := original_core_centralizes s
  intro x hx y hy hx1 hy1
  obtain ⟨l,hl,he⟩ := unitary_original_nonzero_fusion s hx hy hx1 hy1
  obtain ⟨r,hr,q,hq,rfl⟩ := hcover ▸ (show l ∈ (L : Set G) from hl)
  refine ⟨r,hr,?_⟩
  have hc : q*x*q⁻¹ = x := by
    rw [←hQV hq x hx,mul_inv_cancel_right]
  have hh : (r*q)*x*(r*q)⁻¹ = r*x*r⁻¹ := by
    calc
      _ = r*(q*x*q⁻¹)*r⁻¹ := by group
      _ = _ := by rw [hc]
  exact hh.symm.trans he

/-- Restricting the original quotient map puts O₂(R) in O₂(L), so it centralizes V. -/
theorem unitary_original_terminal_residual_core_centralizes (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    (oddActorResidual L A).pCoreIn 2 ≤ centralizer (V : Set G) := by
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  obtain ⟨a,ha⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hcomm hodd hAV
  apply le_trans _ (original_core_centralizes s)
  rintro x ⟨r,hr,rfl⟩
  refine ⟨⟨r.val,((oddActorResidual_le L A).trans inf_le_left) r.property⟩,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 L)
    ⟨r.val,((oddActorResidual_le L A).trans inf_le_left) r.property⟩ = 1
  have hz : QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr hr
  rw [←ha r,hz,map_one]

/-- The literal fixed residual, embedded in Rudvalis, has the original module
as its two-core. Its quotient and involution markings use the same injection. -/
theorem unitary_original_terminal_rudvalis_residual (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (i : oddActorResidual L A →* Rudvalis.Model) (hi : Function.Injective i) :
    let R := oddActorResidual L A
    let E := (V.subgroupOf R).map i
    R.pCoreIn 2 = V ∧ Nat.card R = 64 * 6048 ∧
    IsElementaryAbelian 2 E ∧ Nat.card E = 64 ∧
    i.range.pCoreIn 2 = E ∧ Nat.card i.range = 64 * 6048 ∧
    ∀ z : E, z ≠ 1 →
      IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) ∧
      Nat.card (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)) = 245760 := by
  let R := oddActorResidual L A
  let V0 := V.subgroupOf R
  let E := V0.map i
  let B := i.range
  let d : R ≃* B := MonoidHom.ofInjective hi
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  obtain ⟨_,_,hVP,_⟩ := chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV
  have hVR : V ≤ R := hVP.trans (pCoreIn_le 2 R)
  let : IsElementaryAbelian 2 V0 := IsElementaryAbelian.subgroupOf hVR
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map i
  let : V0.Normal := normal_subgroupOf_of_le_normalizer
    (((oddActorResidual_le L A).trans inf_le_left).trans s.chosen.normalizes)
  have hBE : B ≤ normalizer (E : Set Rudvalis.Model) := by
    have hh := V0.le_normalizer_map i
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map] at hh
  have hEB : E ≤ B := map_le_range i V0
  have hV : Nat.card V = 64 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod,s.coordinates.finrank_eq,Atlas.G2.Natural.finrank_space] at hh
    exact hh
  have hE : Nat.card E = 64 := by
    rw [card_map_of_injective hi,Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv,hV]
  obtain ⟨a,_⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hcomm hodd hAV
  let aB : B ⧸ pCore 2 B ≃* Atlas.G2.Natural.BinaryNormalizer.Derived :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans (a.trans s.quotient)
  have hp : (pCore 2 R).map i = B.pCoreIn 2 := by
    rw [pCoreIn,←pCore_map_iso 2 d,map_map]
    rfl
  have hcore : B.pCoreIn 2 ≤ centralizer (E : Set Rudvalis.Model) := by
    rw [←hp]
    rintro _ ⟨r,hr,rfl⟩ _ ⟨v,hv,rfl⟩
    have hh := unitary_original_terminal_residual_core_centralizes s A hAN hcomm hodd hAV
      (mem_map_of_mem R.subtype hr) v hv
    have hh' : v*r = r*v := Subtype.ext hh
    simpa only [map_mul] using congrArg i hh'
  have ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hx1 hy1
    have hxG : (x : G) ≠ 1 := fun h => hx1 ((congrArg i (Subtype.ext h)).trans (map_one i))
    have hyG : (y : G) ≠ 1 := fun h => hy1 ((congrArg i (Subtype.ext h)).trans (map_one i))
    obtain ⟨r,hr,he⟩ := unitary_original_terminal_residual_fusion s A hAN hcomm hodd hAV
      x hx y hy hxG hyG
    let r0 : R := ⟨r,hr⟩
    refine ⟨i r0,⟨r0,rfl⟩,?_⟩
    have hh : r0*x*r0⁻¹ = y := Subtype.ext he
    simpa only [map_mul,map_inv] using congrArg i hh
  obtain ⟨hPE,hB⟩ := Rudvalis.transitive_sixtyFour_twoCore B E hEB hBE hE aB hcore ht
  have hPV : pCore 2 R = V0 := map_injective hi (hp.trans hPE)
  have hRV : R.pCoreIn 2 = V := by
    change (pCore 2 R).map R.subtype = V
    rw [hPV,map_subgroupOf_eq_of_le hVR]
  refine ⟨hRV,(Nat.card_congr d.toEquiv).trans hB,inferInstance,hE,hPE,hB,?_⟩
  intro z hz
  have hd : 6048 ∣ Nat.card B := by rw [hB]; exact dvd_mul_left _ _
  obtain ⟨hclass,hcard,_⟩ := Rudvalis.transitive_sixtyFour_involution_class B E hBE hE hd ht z hz
  exact ⟨hclass,hcard⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
