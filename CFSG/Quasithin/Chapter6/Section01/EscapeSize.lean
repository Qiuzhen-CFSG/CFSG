module

public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Basic
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Geometry
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural
public import Theory.GroupTheory.IrreducibleSectionCentralizer


/-!
# Coset transitivity and the terminal size bound for the escaping branch

The actual constructions are in `EscapeSize.Basic`. The fixed-centralizer
argument reduces `|F| ≤ 4` to irreducibility of the actual section `R/E`
under `L₀`. Combining this with `E = V_L F` proves the relative-index bound;
the natural-module order and the two index-four identities then give the
order bound for the genuine quotient `U/Z_S`.

`lemma_6_1_26_of_geometric_identities` assembles the geometric and natural-module
proofs: it derives the supplement, splitting and both irreducibility assertions,
proves preservation and transitivity on the nontrivial layer cosets, and proves
`C_F(u) = 1` and `|E:V_L| ≤ 4`. The case `E = V_L` is treated explicitly.
`quotient_bound_of_geometric_identities` then proves `|U| ≤ 1024` and the actual
quotient bound `|U/Z_S| ≤ 256`, including relative normality.

The earlier geometric identities of 6.1.20–21, the natural models at `n = 2`
from 6.1.25, and `C_T(L) = 1` remain explicit source inputs. The parent §6.1
assembly owns their discharge from Hypothesis 6.1.1 and Theorem 6.1.27.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 6.1.26
and the final paragraph of Theorem 6.1.27, printed pp.678–679.
-/

public section

namespace CFSG.Quasithin.Chapter6.Source.Escape
open Subgroup
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G]

/-- Once the action of `L₀` on `R/E` is known to be irreducible, the
continuation on p.679 gives `|F| ≤ 4`. Choose `u ∈ C_U(V_L) − E` using
its index four; the general fixed-centralizer lemma gives `C_F(u)=1`,
and commutation with `u` embeds `F` into `Z_S`. No nontriviality of `E/V_L`
is assumed, so the equality case is included. -/
theorem F_card_le_four_of_irreducible [Finite G] {T L V : Subgroup G} {g l : G}
    (hER : E T L V l ≤ R T L V l)
    (hET : E T L V l ≤ T)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hDR : L0 L V g l ≤ normalizer (R T L V l : Set G))
    (hL : L ≤ L0 L V g l ⊔ R T L V l)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hIrr : ∀ A : Subgroup G, E T L V l ≤ A → A ≤ R T L V l →
      L0 L V g l ≤ normalizer (A : Set G) → A = E T L V l ∨ A = R T L V l)
    (hCR : U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l)
    (hCE : (E T L V l).relIndex (U T L V ⊓ centralizer (layer L V : Set G)) = 4)
    (hcomm : ⁅U T L V, U T L V⁆ ≤ ZS T L V)
    (hZ : Nat.card (ZS T L V) = 4) : Nat.card (F T L V g l) ≤ 4 := by
  have hn : ¬ U T L V ⊓ centralizer (layer L V : Set G) ≤ E T L V l := by
    intro h
    have hi := relIndex_eq_one.mpr h
    rw [hCE] at hi
    contradiction
  obtain ⟨u, hu, huE⟩ := SetLike.not_le_iff_exists.mp hn
  have hfix : F T L V g l ⊓ centralizer ({u} : Set G) = ⊥ :=
    fixed_centralizer_eq_bot_of_irreducible_section hER hET hEE hDR hL hCT hIrr
      (hCR hu) huE
  calc
    Nat.card (F T L V g l) ≤ Nat.card (ZS T L V) :=
      card_le_of_injective_commutator hfix fun f hf =>
        hcomm (commutator_mem_commutator (show f ∈ U T L V from hf.1.1) hu.1)
    _ = 4 := hZ

/-- The actual relative index follows from the geometric splitting.
Normality is only needed inside `E` and follows from its commutativity. -/
theorem layer_relIndex_E_le_card_F_of_split [Finite G] {T L V : Subgroup G} {g l : G}
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hsplit : E T L V l = layer L V ⊔ F T L V g l) :
    (layer L V).relIndex (E T L V l) ≤ Nat.card (F T L V g l) := by
  have hVE : layer L V ≤ E T L V l := hsplit ▸ le_sup_left
  have hN : F T L V g l ≤ normalizer (layer L V : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro f hf
    exact mem_centralizer_iff.mpr fun v hv => mem_centralizer_iff.mp (hEE hf.1) v (hVE hv)
  rw [hsplit]
  let B := layer L V
  let C := F T L V g l
  let : (B.subgroupOf (B ⊔ C)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hN)
  have hi := relIndex_sup_left (C.subgroupOf (B ⊔ C)) (B.subgroupOf (B ⊔ C))
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_right] at hi
  change B.relIndex (B ⊔ C) ≤ Nat.card C
  rw [hi]
  exact Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card B C)

/-- The three successive indices in the last paragraph of 6.1.27 give
`|U| ≤ 4^5`. The layer order is derived from its natural-module model. -/
theorem U_card_le_of_layer_index {T L V : Subgroup G} {l : G}
    (hVE : layer L V ≤ E T L V l)
    (hEC : E T L V l ≤ U T L V ⊓ centralizer (layer L V : Set G))
    (hV : IsNaturalModule L (layer L V) 2)
    (hEV : (layer L V).relIndex (E T L V l) ≤ 4)
    (hCE : (E T L V l).relIndex (U T L V ⊓ centralizer (layer L V : Set G)) = 4)
    (hUC : (U T L V ⊓ centralizer (layer L V : Set G)).relIndex (U T L V) = 4) :
    Nat.card (U T L V) ≤ 1024 := by
  have hv : Nat.card (layer L V) = 16 := by simpa using hV.card
  have h₁ := relIndex_mul_relIndex (⊥ : Subgroup G) (layer L V) (E T L V l) bot_le hVE
  have h₂ := relIndex_mul_relIndex (⊥ : Subgroup G) (E T L V l)
    (U T L V ⊓ centralizer (layer L V : Set G)) bot_le hEC
  have h₃ := relIndex_mul_relIndex (⊥ : Subgroup G)
    (U T L V ⊓ centralizer (layer L V : Set G)) (U T L V) bot_le inf_le_left
  simp only [relIndex_bot_left, hv, hCE, hUC] at h₁ h₂ h₃
  omega

/-- Divide by the order-four subgroup inside `U`, with the actual
quotient group and its normality instance. -/
theorem quotient_card_le_of_U_card {T L V : Subgroup G}
    (hZ : Nat.card (ZS T L V) = 4)
    (hU : Nat.card (U T L V) ≤ 1024)
    [((ZS T L V).subgroupOf (U T L V)).Normal] :
    Nat.card ((U T L V) ⧸ (ZS T L V).subgroupOf (U T L V)) ≤ 256 := by
  have hc := ((ZS T L V).subgroupOf (U T L V)).card_mul_index
  have hsub : Nat.card ((ZS T L V).subgroupOf (U T L V)) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (ZS_le_U T L V)).toEquiv).trans hZ
  rw [hsub, index_eq_card] at hc
  omega

/-- Intermediate size calculation from splitting and section irreducibility.
The assembly below derives these premises from the geometric identities and
the equivariant natural model. This helper alone is not source Lemma 6.1.26. -/
theorem quotient_bound_of_split_and_irreducible [Finite G] {T L V : Subgroup G} {g l : G}
    (hER : E T L V l ≤ R T L V l)
    (hET : E T L V l ≤ T)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hDR : L0 L V g l ≤ normalizer (R T L V l : Set G))
    (hL : L ≤ L0 L V g l ⊔ R T L V l)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hIrr : ∀ A : Subgroup G, E T L V l ≤ A → A ≤ R T L V l →
      L0 L V g l ≤ normalizer (A : Set G) → A = E T L V l ∨ A = R T L V l)
    (hsplit : E T L V l = layer L V ⊔ F T L V g l)
    (hCR : U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l)
    (hV : IsNaturalModule L (layer L V) 2)
    (hCE : (E T L V l).relIndex (U T L V ⊓ centralizer (layer L V : Set G)) = 4)
    (hUC : (U T L V ⊓ centralizer (layer L V : Set G)).relIndex (U T L V) = 4)
    (hcomm : ⁅U T L V, U T L V⁆ ≤ ZS T L V)
    (hZ : Nat.card (ZS T L V) = 4) :
    ((ZS T L V).subgroupOf (U T L V)).Normal ∧
      Nat.card ((U T L V) ⧸ (ZS T L V).subgroupOf (U T L V)) ≤ 256 := by
  have hVE : layer L V ≤ E T L V l := hsplit ▸ le_sup_left
  have hEC : E T L V l ≤ U T L V ⊓ centralizer (layer L V : Set G) := by
    refine le_inf inf_le_left ?_
    intro e he
    exact mem_centralizer_iff.mpr fun v hv => mem_centralizer_iff.mp (hEE he) v (hVE hv)
  have hVZ : layer L V ≤ centralizer (ZS T L V : Set G) := by
    intro v hv
    exact mem_centralizer_iff.mpr fun z hz =>
      mem_centralizer_iff.mp (hEE (hVE hv)) z (hVE hz.1)
  have hn := ZS_normal_in_U hVZ
  let := hn
  refine ⟨hn, quotient_card_le_of_U_card hZ ?_⟩
  apply U_card_le_of_layer_index hVE hEC hV _ hCE hUC
  exact (layer_relIndex_E_le_card_F_of_split hEE hsplit).trans
    (F_card_le_four_of_irreducible hER hET hEE hDR hL hCT hIrr hCR hCE hcomm hZ)

/-- The central-quotient assertion of 6.1.21(3) supplies the action of
`L₀` on the actual layer, not merely an abstract invariant-subgroup test. -/
theorem L0_normalizes_layer_of_central_quotient {T L V : Subgroup G} {g l : G}
    (hg : g ∈ I T L V) (hVE : layer L V ≤ E T L V l)
    (hcentral : ⁅L1 T L V l, E T L V l⁆ ≤ layer L V) :
    L0 L V g l ≤ normalizer (layer L V : Set G) :=
  (L0_le_L1 hg).trans (le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hVE).trans hcentral))

section GeometricAssembly
variable [Finite G] {T L V : Subgroup G} {g l : G}
variable
    (hg : g ∈ I T L V) (hl : l ∈ L)
    (hV : IsNaturalModule L (layer L V) 2)
    (hL1 : L1 T L V l = L ⊔ U T L V)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hUT : U T L V ≤ T)
    (hR : R T L V l = (U T L V ⊓ centralizer (layer L V : Set G)) ⊔
      ((U T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G)))
    (hprod : U T L V = (layer L V ⊔
      (layer L V).map (MulAut.conj g⁻¹).toMonoidHom) ⊔
      (U T L V ⊓ centralizer ((layer L V ⊔
        (layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)))
    (hcentral : ⁅L1 T L V l, E T L V l⁆ ≤ layer L V)
    (hZ : Nat.card (ZS T L V) = 4)
    (hindex : (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
      (U T L V) = 4)
    (hfixB : ZS T L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixA : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hmodel : IsNaturalSectionFour (L1 T L V l) (R T L V l) (E T L V l))
    (hCE : (E T L V l).relIndex (U T L V ⊓ centralizer (layer L V : Set G)) = 4)
    (hcomm : ⁅U T L V, U T L V⁆ ≤ ZS T L V)

include hg hl hV hL1 hEE hUT hR hprod hcentral hZ hindex hfixB hfixA hCT hmodel hCE hcomm

/-- Lemma 6.1.26, conditional only on the earlier geometric identities and
the genuine equivariant natural modules. The conclusions retain the actual
product `E = V_L F`, preservation and transitivity on every nontrivial coset,
the continuation `C_F(u) = 1` for `u ∈ R − E`, and the index bound.

Both irreducibility assertions and the supplement are proved internally.
The equality case `E = V_L` has index one, so the bound also holds without
the source's existential premise. The owner of Theorem 6.1.27 must supply
the displayed inputs from 6.1.20–21 and 6.1.25; this is a conditional branch,
not a theorem from Hypothesis 6.1.1 alone. -/
theorem lemma_6_1_26_of_geometric_identities :
    (E T L V l : Set G) = (layer L V : Set G) * (F T L V g l : Set G) ∧
    (∀ e ∈ E T L V l, ∀ r ∈ R T L V l, ∀ v ∈ layer L V,
      ∃ w ∈ layer L V, r⁻¹ * (e * v) * r = e * w) ∧
    (∀ e ∈ E T L V l, e ∉ layer L V → ∀ v ∈ layer L V,
      ∃ r ∈ R T L V l, e * v = r⁻¹ * e * r) ∧
    (∀ u ∈ R T L V l, u ∉ E T L V l →
      F T L V g l ⊓ centralizer ({u} : Set G) = ⊥) ∧
    Nat.card (F T L V g l) ≤ 4 ∧
    (layer L V).relIndex (E T L V l) ≤ 4 := by
  have hn : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hV
    exact hm.normalizes
  obtain ⟨hVE, hER, hET, _, hCR, hRW⟩ := core_bridges hn hl hEE hUT hR
  obtain ⟨hsupp, hL, hDR⟩ :=
    supplement_of_geometric_identities hg hl hV hL1 hEE hR hprod
  have hD := L0_normalizes_layer_of_central_quotient hg hVE hcentral
  have hWIrr := (layer_irreducible_of_natural hV hL hRW hD).2
  have hRIrr := section_irreducible_of_natural hmodel hsupp
  have hsplit := split_of_geometric_ranks hg hl hV hEE hZ hindex hfixB hfixA
  obtain ⟨hpres, horbit⟩ := cosets_of_geometric_identities hg hl hV hL1 hEE hUT hR
    hprod hcentral hZ hindex hfixB hfixA hCT hWIrr
  have hF := F_card_le_four_of_irreducible hER hET hEE hDR hL hCT hRIrr hCR hCE hcomm hZ
  refine ⟨set_product_of_split hEE hsplit, hpres, horbit, ?_, hF, ?_⟩
  · intro u hu huE
    exact fixed_centralizer_eq_bot_of_irreducible_section hER hET hEE hDR hL hCT hRIrr
      hu huE
  · by_cases heq : E T L V l = layer L V
    · rw [heq, relIndex_self]
      decide
    · exact (layer_relIndex_E_le_card_F_of_split hEE hsplit).trans hF

/-- The terminal estimate from the same geometric and natural-module inputs.
The order of `V_L` is derived from its model; the three actual relative
indices give `|U| ≤ 1024`, and division by the central order-four `Z_S`
gives `|U/Z_S| ≤ 256`. Relative normality is proved as part of the result.
No splitting, transitivity, irreducibility, or size conclusion is assumed. -/
theorem quotient_bound_of_geometric_identities
    (hUC : (U T L V ⊓ centralizer (layer L V : Set G)).relIndex (U T L V) = 4) :
    Nat.card (U T L V) ≤ 1024 ∧
    ((ZS T L V).subgroupOf (U T L V)).Normal ∧
    Nat.card ((U T L V) ⧸ (ZS T L V).subgroupOf (U T L V)) ≤ 256 := by
  have hEV := (lemma_6_1_26_of_geometric_identities hg hl hV hL1 hEE hUT hR hprod
    hcentral hZ hindex hfixB hfixA hCT hmodel hCE hcomm).2.2.2.2.2
  have hnL : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hV
    exact hm.normalizes
  obtain ⟨hVE, _, _, hEC, _, _⟩ := core_bridges hnL hl hEE hUT hR
  have hU := U_card_le_of_layer_index hVE hEC hV hEV hCE hUC
  have hVZ : layer L V ≤ centralizer (ZS T L V : Set G) :=
    (hVE.trans hEE).trans (centralizer_le (inf_le_left.trans hVE))
  have hn := ZS_normal_in_U hVZ
  let := hn
  exact ⟨hU, hn, quotient_card_le_of_U_card hZ hU⟩

end GeometricAssembly
end CFSG.Quasithin.Chapter6.Source.Escape
