module

public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Basic
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The central line in the original Chapter 6 configuration

The nonzero elementary layer is normalized by T. The fixed-point theorem for
finite two-groups therefore makes Z_S = C_[V,L](T ∩ L) nontrivial, before any
natural-module classification. Its two defining subgroups are T-invariant,
so its normalizer contains T. Even characteristic then proves the literal
source 6.1.9(3), F*(N_G(Z_S)) = O₂(N_G(Z_S)). Characteristic-two inheritance
gives the corresponding identity for I = C_G(Z_S).

The actual conjugate-generated U from the escape branch centralizes Z_S,
which supplies relative normality for its quotient U/Z_S. This discharges
the centrality premise of `Escape.ZS_normal_in_U` from Hypothesis 6.1.1.
The natural-module reduction, C_T(L) = 1, and the two global weak-closure
branches of 6.1.27 remain separate source obligations.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript,
6.1.9(3), printed p.669, and the constructions on pp.672--679.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
  (h : Hypothesis611 K T L M V n)
include h

theorem sylow_normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G) :=
  h.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)

theorem sylow_normalizes_layer : (T : Subgroup G) ≤ normalizer (layer L V : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅V, L⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅V, L⁆
  rw [map_commutator]
  have hV : V.map (MulAut.conj t).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp ((le_sup_right.trans (reduced_normalizes h.V_mem)) ht)
  have hL : L.map (MulAut.conj t).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (h.sylow_normalizes_L ht)
  rw [hV, hL]

theorem layer_elementary : IsElementaryAbelian 2 (layer L V) := by
  let := h.V_mem.2.1
  exact IsElementaryAbelian.of_injective (inclusion h.layer_le_V)
    (inclusion_injective h.layer_le_V)

theorem ZS_elementary : IsElementaryAbelian 2 (ZS (T : Subgroup G) L V) := by
  let := h.layer_elementary
  exact IsElementaryAbelian.of_injective (inclusion (H := ZS (T : Subgroup G) L V)
    (K := layer L V) inf_le_left) (inclusion_injective inf_le_left)

theorem ZS_ne_bot : ZS (T : Subgroup G) L V ≠ ⊥ := by
  exact inf_centralizer_ne_bot_of_pGroups ((T : Subgroup G) ⊓ L) (layer L V)
    (T.isPGroup'.to_le inf_le_left) (T.isPGroup'.to_le h.layer_le_T)
    (inf_le_left.trans h.sylow_normalizes_layer) h.nontrivial_action

theorem sylow_normalizes_ZS :
    (T : Subgroup G) ≤ normalizer (ZS (T : Subgroup G) L V : Set G) := by
  have hTL : (T : Subgroup G) ≤ normalizer ((T : Subgroup G) ⊓ L : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes_L).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf h.sylow_normalizes_layer
    (hTL.trans (normalizer_le_normalizer_centralizer ((T : Subgroup G) ⊓ L)))).trans
      inf_normalizer_le_normalizer_inf

theorem ZS_normalizer_mem_He : normalizer (ZS (T : Subgroup G) L V : Set G) ∈
    Chapter1.He G :=
  Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
    ⟨_, h.ZS_ne_bot, T.isPGroup'.to_le h.ZS_le_T, rfl⟩ h.sylow_normalizes_ZS

theorem source_lemma_6_1_9_3 :
    generalizedFitting (Escape.H (T : Subgroup G) L V) =
      pCore 2 (Escape.H (T : Subgroup G) L V) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp h.ZS_normalizer_mem_He)

theorem ZS_centralizer_mem_He : Escape.I (T : Subgroup G) L V ∈ Chapter1.He G := by
  change Escape.I (T : Subgroup G) L V ⊓
    centralizer ((Escape.I (T : Subgroup G) L V).pCoreIn 2 : Set G) ≤
      (Escape.I (T : Subgroup G) L V).pCoreIn 2
  have hc := pCoreIn_selfCentralizing_centralizer h.ZS_normalizer_mem_He
    (T.isPGroup'.to_le h.ZS_le_T) (ZS (T : Subgroup G) L V).le_normalizer
  simpa only [Escape.I, inf_eq_right.mpr (centralizer_le_normalizer (ZS (T : Subgroup G) L V : Set G))]
    using hc

theorem ZS_centralizer_generalizedFitting :
    generalizedFitting (Escape.I (T : Subgroup G) L V) =
      pCore 2 (Escape.I (T : Subgroup G) L V) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp h.ZS_centralizer_mem_He)

theorem layer_centralizes_ZS : layer L V ≤
    centralizer (ZS (T : Subgroup G) L V : Set G) := by
  let := h.layer_elementary
  exact (le_centralizer (H := layer L V)).trans
    (centralizer_le (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left))

theorem ZS_normal_in_escape_U :
    ((ZS (T : Subgroup G) L V).subgroupOf (Escape.U (T : Subgroup G) L V)).Normal :=
  Escape.ZS_normal_in_U h.layer_centralizes_ZS

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
