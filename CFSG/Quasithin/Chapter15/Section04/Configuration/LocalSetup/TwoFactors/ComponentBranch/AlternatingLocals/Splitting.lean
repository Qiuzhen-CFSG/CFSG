module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Lifting
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# Splitting the two original local groups

The elementary fixed plane E_i has order four and lies in C_{T_I}(Y_i).
Once C_{T_I}(L) has order two, the proved centralizer index makes these
two subgroups equal. The S₆ centralizer calculation then shows that E_i
commutes with, and is disjoint from, the actual S₄ subgroup G_i ∩ L.
Their images generate the quotient and E_i contains its kernel, so their
join is G_i. Multiplication provides the asserted E₄ × S₄ isomorphism.

The centralizer order is an explicit input discharged by the parent's
index-two invariance theorem. Compatible quotient coordinates remain an
upstream obligation. Source: Aschbacher–Smith 15.4.18, printed p.1163.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
variable {I : Type*} [Group I] [Finite I] {L : Subgroup I} (d : QuotientCoordinates L)
include d

/-- Once the component centralizer has order two, the actual source fixed
plane supplies the elementary direct factor. Its complement is the even S₄
subgroup, and multiplication constructs the splitting. -/
theorem local_equiv_e4_s4 (T : Sylow 2 I) (Y E : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3)
    (hC : Nat.card ((T : Subgroup I) ⊓ centralizer (L : Set I) : Subgroup I) = 2)
    [IsElementaryAbelian 2 E] (hET : E ≤ (T : Subgroup I))
    (hEY : E ≤ centralizer (Y : Set I)) (hE : Nat.card E = 4) :
    Nonempty (↥(Y ⊔ (T : Subgroup I)) ≃*
      (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4))) := by
  let H := Y ⊔ (T : Subgroup I)
  let A := (T : Subgroup I) ⊓ centralizer (Y : Set I)
  let B := H ⊓ L
  let q := d.quotientMap
  have hYL := d.factor_le_component Y hY
  have hEA : E ≤ A := le_inf hET hEY
  have hBA : (T : Subgroup I) ⊓ centralizer (L : Set I) ≤ A :=
    inf_le_inf_left _ (centralizer_le hYL)
  have hAcard : Nat.card A = 4 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup I)
      ((T : Subgroup I) ⊓ centralizer (L : Set I)) A bot_le hBA
    rw [relIndex_bot_left, relIndex_bot_left, hC,
      d.factor_centralizer_index T Y hY hn hi] at hc
    omega
  have hEAeq : E = A := eq_of_le_of_card_ge hEA (by rw [hE, hAcard])
  have hEmap : E.map q = centralizer (Y.map q : Set S6) := by
    rw [hEAeq]
    exact d.map_sylow_factor_centralizer T Y hY hn hi
  obtain ⟨_, _, hcentral, hdisjoint, _, hproduct⟩ :=
    d.parabolic_image_structure T Y hY hn hi
  have hkH : q.ker ≤ H := (d.kernel_le_sylow T).trans le_sup_right
  have hkE : q.ker ≤ E := by
    rw [hEAeq, ← d.sylow_component_centralizer T]
    exact hBA
  have hdis : Disjoint E B := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hxc : q x ∈ centralizer (Y.map q : Set S6) :=
      hEmap ▸ mem_map_of_mem q hx.1
    have hxa : q x ∈ A6 := d.component_image ▸ mem_map_of_mem q hx.2.2
    have hq : q x = 1 := mem_bot.mp (disjoint_iff_inf_le.mp hdisjoint ⟨hxc, hxa⟩)
    apply mem_bot.mpr
    apply congrArg Subtype.val (d.component_faithful
      (a₁ := ⟨x, hx.2.2⟩) (a₂ := 1) _)
    change q x = q 1
    simpa only [map_one] using hq
  have hcomm : E ≤ centralizer (B : Set I) := by
    rw [← d.centralizer_lift B inf_le_right]
    intro x hx z hz
    obtain ⟨b, hb, rfl⟩ := hz
    have hxc : q x ∈ centralizer (Y.map q : Set S6) :=
      hEmap ▸ mem_map_of_mem q hx
    exact hcentral hxc (q b) (mem_map_of_mem q hb.1)
  have hgen : E ⊔ B = H := by
    apply map_injective_of_ker_le q (hkE.trans le_sup_left) hkH
    rw [Subgroup.map_sup, hEmap, d.map_inf_component H hkH]
    exact hproduct
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour E := ⟨hE, IsElementaryAbelian.exponent_eq_prime⟩
  obtain ⟨eE⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := E) (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  obtain ⟨eB⟩ := d.even_local_equiv T Y hY hn hi
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting E B hdis hcomm
  exact ⟨(MulEquiv.subgroupCongr hgen.symm).trans
    (e.symm.trans (MulEquiv.prodCongr eE eB))⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
