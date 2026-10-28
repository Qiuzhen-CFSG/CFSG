module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Order.Displacement
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Definitions
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Commutator

/-!
# The source five-hyperplane and its proper normalizer image

D=Q₀Q₅ has index two in the original Q. The Sylow-five normalizer acts on D,
but its H-normalizer cannot cover S₅: that would make D invariant under K,
forcing [Q,K]≤D, contrary to Q=[Q,K]. All quotient maps and the central
preimage remain the original ones.

Source: Aschbacher–Smith, J.4.4(3), printed p.441.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

abbrev fiveHyperplane (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  Q₀ d⊔Q₅ d B5

theorem fiveHyperplane_le_Q (B5 : Sylow 5 d.toTypeRuSetup.H) :
    fiveHyperplane d B5≤d.toTypeRuSetup.Q := sup_le (Q₀_le_Q d) (Q₅_le_Q d B5)

theorem U_le_fiveHyperplane (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.toTypeRuSetup.U≤fiveHyperplane d B5 := (U_le_Q₀ d).trans le_sup_left

theorem hat_fiveHyperplane (B5 : Sylow 5 d.toTypeRuSetup.H) :
    hat d (fiveHyperplane d B5)=center (Hat d)⊔hat d (Q₅ d B5) := by
  rw [fiveHyperplane,hat_sup d (Q₀_le_H d) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)),hat_Q₀]

theorem hat_fiveHyperplane_card (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (hat d (fiveHyperplane d B5))=32 := by
  have hd : Disjoint (center (Hat d)) (hat d (Q₅ d B5)) := by
    apply (hat_Q_split d B5).2.mono_left
    rw [←hat_HC_eq_hat_CQ,←hat_Q₀]
    exact hat_mono d (Q₀_le_HC d)
  rw [hat_fiveHyperplane,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (by rw [normalizer_eq_top]; exact le_top) hd,center_hat_card,hat_Q₅_card]

theorem fiveHyperplane_card (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (fiveHyperplane d B5)=1024 := by
  have h := hat_card d (fiveHyperplane d B5) ((fiveHyperplane_le_Q d B5).trans (pCoreIn_le 2 _))
  rw [hat_fiveHyperplane_card,inf_eq_right.mpr (U_le_fiveHyperplane d B5),d.ru2.card_U d.card_Z] at h
  exact h.symm

theorem fiveHyperplane_index (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (fiveHyperplane d B5).relIndex d.toTypeRuSetup.Q=2 := by
  have h := relIndex_mul_relIndex (⊥:Subgroup G) (fiveHyperplane d B5)
    d.toTypeRuSetup.Q bot_le (fiveHyperplane_le_Q d B5)
  simp only [relIndex_bot_left] at h
  rw [fiveHyperplane_card,d.ru2.card_Q d.card_Z] at h
  omega

theorem Q_normalizes_fiveHyperplane (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.toTypeRuSetup.Q≤normalizer (fiveHyperplane d B5:Set G) :=
  (le_inf ((pCoreIn_le 2 _).trans (Q₀_normalized d)) (Q₅_normalized d B5)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

abbrev fiveHyperplaneNormalizer (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup d.toTypeRuSetup.H :=
  (normalizer (fiveHyperplane d B5:Set G)).subgroupOf d.toTypeRuSetup.H

theorem fiveHyperplaneNormalizer_ker (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.ru2.quotientMap.ker≤fiveHyperplaneNormalizer d B5 := by
  rw [d.ru2.quotient_kernel]
  exact fun _ hx => Q_normalizes_fiveHyperplane d B5 hx

theorem five_normalizer_le_fiveHyperplaneNormalizer (B5 : Sylow 5 d.toTypeRuSetup.H) :
    normalizer (B5:Set d.toTypeRuSetup.H)≤fiveHyperplaneNormalizer d B5 := by
  intro h hh
  have hB : (h:G)∈normalizer (B5Image B5:Set G) :=
    (B5:Subgroup d.toTypeRuSetup.H).le_normalizer_map d.toTypeRuSetup.H.subtype
      (mem_map_of_mem _ hh)
  have hQ := d.ru2.six.normalized h.property
  have h5 : (h:G)∈normalizer (Q₅ d B5:Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,Q₅,Subgroup.map_commutator,
      mem_normalizer_iff_map_conj_eq.mp hQ,mem_normalizer_iff_map_conj_eq.mp hB]
  exact normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨Q₀_normalized d h.property,h5⟩

theorem five_quotient_normalizer_le_image (B5 : Sylow 5 d.toTypeRuSetup.H) :
    normalizer (B5.map d.ru2.quotientMap:Set S5) ≤
      (fiveHyperplaneNormalizer d B5).map d.ru2.quotientMap := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [←B5.normalizer_map_surjective d.ru2.quotientMap d.ru2.quotient_surjective]
  exact Subgroup.map_mono (five_normalizer_le_fiveHyperplaneNormalizer d B5)

theorem fiveHyperplaneNormalizer_image_ne_top (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (fiveHyperplaneNormalizer d B5).map d.ru2.quotientMap ≠ ⊤ := by
  intro he
  have hn : fiveHyperplaneNormalizer d B5=⊤ := by
    have hh := congrArg (Subgroup.comap d.ru2.quotientMap) he
    rwa [comap_map_eq_self (fiveHyperplaneNormalizer_ker d B5),comap_top] at hh
  have hHD : d.toTypeRuSetup.H≤normalizer (fiveHyperplane d B5:Set G) := by
    intro x hx
    exact (show (⟨x,hx⟩:d.toTypeRuSetup.H)∈fiveHyperplaneNormalizer d B5 by rw [hn]; trivial)
  have hc := commutator_le_of_normalized_index_two d.toTypeRuSetup.Q
    (fiveHyperplane d B5) d.toTypeRuSetup.K (fiveHyperplane_le_Q d B5)
    (fiveHyperplane_index d B5) (d.toTypeRuSetup.K_le_H.trans d.ru2.six.normalized)
    (d.toTypeRuSetup.K_le_H.trans hHD)
  rw [commutator_Q_K d] at hc
  have hh := card_le_of_le hc
  rw [d.ru2.card_Q d.card_Z,fiveHyperplane_card] at hh
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup
