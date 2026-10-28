module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import Theory.ElementaryAbelian.Quotient

/-!
# The transvection action in 13.8.9

Work inside the actual vertex stabilizer J=Gγ; all normality is relative
to J. Normal generation first proves [F,Vγ] is noncentral modulo Uγ.
The equality of commutator images modulo V₁ then bounds this commutator
by Uγ V₁. An order-two image argument proves V₁≤Vγ and identifies the
full displacement in the literal quotient Vγ/Uγ with V₁Uγ/Uγ. Finally
each actor is recognized as a linear transvection on that same carrier.

The source inputs are the generation hypothesis in 13.8.9, the transported
normal-generation and noncentrality conclusions of 13.8.4(5), and the lifted
commutator comparison in 13.8.9(2). The critical-pair construction and its
transport to J remain the responsibility of the geometry assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.949–950, Lemma 13.8.9.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {J : Type*} [Group J] [Finite J]

/-- The noncentral line is contained in the module, not merely its overgroup. -/
theorem line_le_of_noncentral_commutator (F V U Z : Subgroup J)
    [V.Normal] [U.Normal] (hUV : U ≤ V) (hZ : Nat.card Z = 2)
    (hbound : ⁅F, V⁆ ≤ U ⊔ Z) (hnoncentral : ¬ ⁅F, V⁆ ≤ U) :
    Z ≤ V ∧ ¬ Z ≤ U ∧ U ⊔ ⁅F, V⁆ = U ⊔ Z := by
  let q := QuotientGroup.mk' U
  have hC : (⁅F, V⁆.map q) ≠ ⊥ := by
    intro hh
    exact hnoncentral (by simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh)
  have hCZ : ⁅F, V⁆.map q ≤ Z.map q := by
    have hh := map_mono (f := q) hbound
    simpa only [Subgroup.map_sup, (Subgroup.map_eq_bot_iff U (f := q)).mpr (by simp [q]), bot_sup_eq] using hh
  have hdiv : Nat.card (⁅F, V⁆.map q) ∣ 2 := by
    rw [← hZ]
    exact (card_dvd_of_le hCZ).trans (Z.card_map_dvd q)
  have hccard : Nat.card (⁅F, V⁆.map q) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left (fun h => hC (card_eq_one.mp h))
  have heq : ⁅F, V⁆.map q = Z.map q := eq_of_le_of_card_ge hCZ (by
    rw [hccard]
    exact Nat.le_of_dvd (by omega : 0 < 2) (hZ ▸ Z.card_map_dvd q))
  have hs : U ⊔ ⁅F, V⁆ = U ⊔ Z := by
    have hh := congrArg (fun K => K.comap q) heq
    simpa only [comap_map_eq, QuotientGroup.ker_mk', q, sup_comm] using hh
  refine ⟨?_, ?_, hs⟩
  · exact (le_sup_right.trans hs.symm.le).trans (sup_le hUV (commutator_le_right _ _))
  · intro hZU
    exact hnoncentral (hbound.trans (sup_le le_rfl hZU))

/-- The complete center and transvection inference in 13.8.9, inside J=Gγ. -/
theorem transvections_on_generated_section
    (F E W V U Z : Subgroup J) [U.Normal] [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hV : V = normalClosure (W : Set J))
    (hgen : normalClosure (F : Set J) ⊔ E = ⊤)
    (hEW : ⁅E, W⁆ ≤ U) (hnoncentral : ¬ ⁅(⊤ : Subgroup J), V⁆ ≤ U)
    (hZ : Nat.card Z = 2) (hcomparison : ⁅F, V⁆ ≤ ⁅F, U⁆ ⊔ Z) :
    let _ : V.Normal := hV ▸ normalClosure_normal
    ∃ action : F →* MulAut (V ⧸ U.subgroupOf V),
      (∀ f : F, ∀ v : V,
        action f (QuotientGroup.mk' (U.subgroupOf V) v) =
          QuotientGroup.mk' (U.subgroupOf V)
            ⟨(f : J) * (v : J) * (f : J)⁻¹,
              (inferInstance : V.Normal).conj_mem v v.property f⟩) ∧
      ¬ Z ≤ U ∧ Z ≤ V ∧
      commutatorAction action.range (V ⧸ U.subgroupOf V) =
        (Z.subgroupOf V).map (QuotientGroup.mk' (U.subgroupOf V)) ∧
      Nat.card (commutatorAction action.range (V ⧸ U.subgroupOf V)) = 2 ∧
      ∀ f : F, binaryLinear (action f) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (V ⧸ U.subgroupOf V)) := by
  let _ : V.Normal := hV ▸ normalClosure_normal
  dsimp only
  have hFV := commutator_not_le_of_noncentral_generated_quotient
    F E W V U hV hgen hEW hnoncentral
  have hbound : ⁅F, V⁆ ≤ U ⊔ Z :=
    hcomparison.trans (sup_le_sup_right (commutator_le_right F U) Z)
  obtain ⟨hZV, hZU, hs⟩ := line_le_of_noncentral_commutator F V U Z hUV hZ hbound hFV
  have hFN : F ≤ normalizer (V : Set J) := le_normalizer_of_normal
  obtain ⟨action, hact⟩ := exists_quotient_conjugation_action F V U hFN
    le_normalizer_of_normal inferInstance
  let q := QuotientGroup.mk' (U.subgroupOf V)
  have himage : commutatorAction action.range (V ⧸ U.subgroupOf V) =
      (⁅F, V⁆.subgroupOf V).map q := by
    have hh := quotient_conjugation_commutatorAction_eq_image
      F V U F hFN le_rfl inferInstance action hact
    have hactors : (F.subgroupOf F).map action = action.range := by
      rw [subgroupOf_self, ← MonoidHom.range_eq_map]
    have hh' := (congrArg (fun A : Subgroup (MulAut (V ⧸ U.subgroupOf V)) =>
      commutatorAction A (V ⧸ U.subgroupOf V)) hactors).symm.trans hh
    simpa only [commutator_comm] using hh'
  have heq : (⁅F, V⁆.subgroupOf V).map q = (Z.subgroupOf V).map q := by
    have hh := congrArg (fun A : Subgroup J => (A.subgroupOf V).map q) hs
    rw [subgroupOf_sup hUV (commutator_le_right F V),
      subgroupOf_sup hUV hZV, Subgroup.map_sup, Subgroup.map_sup] at hh
    simpa only [(Subgroup.map_eq_bot_iff (U.subgroupOf V) (f := q)).mpr (by simp [q]),
      bot_sup_eq] using hh
  have hc : Nat.card ((Z.subgroupOf V).map q) = 2 := by
    have hdiv : Nat.card ((Z.subgroupOf V).map q) ∣ 2 := by
      have hh := (Z.subgroupOf V).card_map_dvd q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZ] at hh
    refine ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left ?_
    intro hone
    have hh := (Subgroup.map_eq_bot_iff _).mp (card_eq_one.mp hone)
    apply hZU
    intro z hz
    have hzker := hh (show (⟨z, hZV hz⟩ : V) ∈ Z.subgroupOf V from hz)
    simpa only [q, QuotientGroup.ker_mk', mem_subgroupOf] using hzker
  refine ⟨action, hact, hZU, hZV, himage.trans heq, ?_, ?_⟩
  · rwa [himage, heq]
  · intro f
    exact transvections_of_displacement_card_two action.range
      (by rwa [himage, heq]) (action f) ⟨f, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
