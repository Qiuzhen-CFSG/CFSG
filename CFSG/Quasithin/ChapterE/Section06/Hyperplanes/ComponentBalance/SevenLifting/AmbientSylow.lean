module
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Sylow promotion in a component product

Let Q = C_T(V) in the original E.6 setup. If a subgroup J centralizes a
nonidentity subspace A of V, Q normalizes J, and |V ∩ J| ≤ 4, then m > 2
makes Q a Sylow two-subgroup of JQ. For a two-overgroup P inside M ∩ JQ,
the TI condition makes P normalize V. Its displacement lies in V ∩ J;
a nontrivial two-action would contain an involution moving at most two
dimensions, contrary to m > 2. The original uniqueness condition controls
N_G(Q), and the normalizer condition completes Sylow promotion.

This uses no Γ assertion about A. It supplies the ambient Sylow step in
the Held repair of E.6.18, printed p.252 of Aschbacher–Smith.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {V M A J : Subgroup G}

private theorem two_subgroup_centralizes_of_small_commutator
    [IsElementaryAbelian 2 V] (hm : 2 < localM V)
    (P : Subgroup G) (hp : IsPGroup 2 P)
    (hPN : P ≤ normalizer (V : Set G)) (hc : Nat.card (⁅V,P⁆ : Subgroup G) ≤ 4) :
    P ≤ centralizer (V : Set G) := by
  apply (inducedAutomizer_eq_bot_iff hPN).mp
  let I := inducedAutomizer V P
  have hI : IsPGroup 2 I := hp.comap_subtype.map _
  by_contra hn
  obtain ⟨a, ha, hane⟩ := I.bot_or_exists_ne_one.resolve_left hn
  have hne : (⟨a, ha⟩ : I) ≠ 1 := fun h => hane (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
    ((hI.dvd_orderOf hne).trans (orderOf_dvd_natCard (x := (⟨a, ha⟩ : I))))
  have ht' : orderOf (t : Automizer V) = 2 := (Subgroup.orderOf_coe t).trans ht
  let d := automizerRepresentation V (t : Automizer V) - LinearMap.id
  have hd : ∀ w : LinearMap.range d, ((w : Additive V).toMul : G) ∈ ⁅V,P⁆ := by
    intro w
    obtain ⟨g, hgP, hgt⟩ := t.property
    obtain ⟨v, hv⟩ := w.property
    have he : (w : Additive V) = automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict g) v - v := by
      rw [hgt]
      exact hv.symm
    rw [he]
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    change (g : G) * (v.toMul : G) * (g : G)⁻¹ * (v.toMul : G)⁻¹ ∈ ⁅V,P⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hgP v.toMul.property
  let f : LinearMap.range d → ↥(⁅V,P⁆ : Subgroup G) := fun w => ⟨((w : Additive V).toMul : G), hd w⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hh : ((x : Additive V).toMul : G) = ((y : Additive V).toMul : G) :=
      congrArg (fun z : ↥(⁅V,P⁆ : Subgroup G) => (z : G)) hxy
    have hv : (x : Additive V).toMul = (y : Additive V).toMul := Subtype.ext hh
    exact Subtype.ext (congrArg Additive.ofMul hv)
  have hcard : Nat.card (LinearMap.range d) ≤ 4 :=
    (Nat.card_le_card_of_injective f hf).trans hc
  have hr : Module.finrank (ZMod 2) (LinearMap.range d) ≤ 2 := by
    classical
    let : Fintype (LinearMap.range d) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)] at hcard
    simp only [ZMod.card] at hcard
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ Module.finrank (ZMod 2) (LinearMap.range d) by omega)
    omega
  have hlow := moduleM_le_involution (automizerRepresentation V) ht'
  rw [fixedCodim_zpowers_eq_displacement_rank] at hlow
  exact (not_le_of_gt hm) (hlow.trans hr)

/-- A component product with small intersection with V has the original Q
as a Sylow subgroup. The intersection A need only be nonidentity. -/
theorem HypothesisE61.sylow_component_product_of_small_intersection
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V)
    (hAV : A ≤ V) (hA : A ≠ ⊥)
    (hJA : J ≤ centralizer (A : Set G))
    (hQJ : sylowCentralizer (T : Subgroup G) V ≤ normalizer (J : Set G))
    (hcard : Nat.card (V ⊓ J : Subgroup G) ≤ 4) :
    ∃ S : Sylow 2 ↥(J ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G),
      (S : Subgroup ↥(J ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G)).map
        (J ⊔ sylowCentralizer (T : Subgroup G) V).subtype =
          sylowCentralizer (T : Subgroup G) V := by
  let Q := sylowCentralizer (T : Subgroup G) V
  let B := J ⊔ Q
  have hBN : B ≤ normalizer (J : Set G) := sup_le J.le_normalizer hQJ
  have hBA : B ≤ centralizer (A : Set G) :=
    sup_le hJA (inf_le_right.trans (Subgroup.centralizer_le hAV))
  have hBVJ : ⁅B,V⁆ ≤ J := by
    have hpre : B ≤ commutatorPreimage B V J := sup_le
      (le_commutatorPreimage le_sup_left
        (le_normalizer_iff_commutator_le_left.mp (h.le_sylowCentralizer.trans hQJ)))
      (le_commutatorPreimage le_sup_right (by
        rw [commutator_eq_bot_iff_le_centralizer.mpr (show Q ≤ centralizer (V : Set G) from inf_le_right)]
        exact bot_le))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le B V J hBN)
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hQpB : IsPGroup 2 (Q.subgroupOf B) := hQp.comap_subtype
  obtain ⟨S,hS⟩ := hQpB.exists_le_sylow
  refine ⟨S, ?_⟩
  apply prime_overgroup_eq_of_normalizer_control (p := 2) Q B M
    h.normalizer_sylowCentralizer_le
  · intro P hp hQP hPB hPM
    have hPN : P ≤ normalizer (V : Set G) :=
      (le_inf hPM (hPB.trans hBA)).trans (h.localCentralizer_le_normalizer hA hAV)
    have hcomm : ⁅V,P⁆ ≤ V ⊓ J := le_inf
      (le_normalizer_iff_commutator_le_left.mp hPN)
      (by rw [commutator_comm]; exact (commutator_mono hPB le_rfl).trans hBVJ)
    exact h.sylowCentralizer_maximal hp hQP
      (two_subgroup_centralizes_of_small_commutator hm P hp hPN
        ((card_le_of_le hcomm).trans hcard))
  · exact S.isPGroup'.map _
  · rw [← map_subgroupOf_eq_of_le (show Q ≤ B from le_sup_right)]
    exact map_mono hS
  · exact map_subtype_le _

end CFSG.Quasithin.ChapterE.Section06
