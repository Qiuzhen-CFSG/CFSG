module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling

/-!
# Construct the earlier local data used by the rank argument

The original natural L-action and its Sylow flag give the literal I₂ and L₂
identities by the proved applicability of 13.5.4. The source action on U_H/V₁
factors through H/O₂(H), which proves [U_H,Q_H] ≤ V₁. Since Q_H lies in T,
its action on the invariant index-two quotient V/V₃ is trivial. Thus the two
commutator bounds used by dimension doubling are derived here.

Source: Aschbacher–Smith, 13.5.4, p.916; 13.7.3(6), p.936;
and the argument for 13.8.6, p.948. These constructions do not supply the
compatible local quotient and plane marking required by the rank argument.
-/

public section
open Subgroup Module BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
open TransvectionRecognition EarlierCore RankDoubling.SourceAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual flag orders give the relative index. -/
theorem flag_index_two {A B : Subgroup G} (hAB : A ≤ B) {n : ℕ}
    (hn : n ≠ 0) (hA : Nat.card A = n) (hB : Nat.card B = 2 * n) :
    A.relIndex B = 2 := by
  have h := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv, hA, hB] at h
  change n * A.relIndex B = 2 * n at h
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) (h.trans (Nat.mul_comm 2 n))

omit [Finite G] in
/-- An invariant quotient of order two admits only the trivial action. -/
theorem commutator_le_index_two {V W A : Subgroup G}
    (hAV : A ≤ normalizer (V : Set G)) (hAW : A ≤ normalizer (W : Set G))
    (hi : W.relIndex V = 2) : ⁅V, A⁆ ≤ W := by
  apply commutator_le.mpr
  intro v hv a ha
  have haV := mem_normalizer_iff.mp (hAV ha)
  have haW := mem_normalizer_iff.mp (hAW ha)
  let w : V := ⟨a * v * a⁻¹, (haV v).mp hv⟩
  have hm : (⟨v, hv⟩ : V) * w⁻¹ ∈ W.subgroupOf V := by
    apply (W.subgroupOf V).mul_mem_iff_of_index_two hi |>.mpr
    change v ∈ W ↔ (w : G)⁻¹ ∈ W
    rw [inv_mem_iff]
    exact haW v
  change v * (a * v * a⁻¹)⁻¹ ∈ W at hm
  simpa only [mul_inv_rev, inv_inv, mul_assoc, commutatorElement_def] using hm

variable {H V₁ V₃ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
/-- Factoring actual conjugation through H* kills Q_H on the literal section. -/
theorem point_core_action_of_conjugation
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := by
  apply commutator_le.mpr
  rintro u hu _ ⟨q, hq, rfl⟩
  have h := vector_commutator ρ hρ ⟨u, hu⟩ q
  have hq' : QuotientGroup.mk' (pCore 2 H) q = 1 :=
    (QuotientGroup.eq_one_iff q).mpr hq
  rw [hq', map_one, Module.End.one_apply, sub_self] at h
  exact (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Source.UH H V₃))
    ⟨⁅u, (q : G)⁆, le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_conjugateSpanBy V₃ H)
      (commutator_mem_commutator hu q.property)⟩).mp h

/-- Construct every local subgroup premise of the dimension-doubling theorem. -/
noncomputable def localData_of_naturalSetup
    {T : Sylow 2 G} {L V V₂ : Subgroup G}
    (s : NaturalSetup T L V V₁ V₂ V₃) (earlier : Earlier1354 T L V)
    (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ normalizer (V₁ : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂) := {
  sylow := T
  sylow_le_H := hTH
  H_le_G1 := hHZ
  sylow_le_G2 := s.plane_stable
  flag12 := s.line_le_plane
  flag23 := s.plane_le_seed
  flag3V := s.seed_le
  normalClosure := (s.apply_earlier earlier).1
  residual := s.localI_residual.symm
  product := rfl
  centralizer := (s.apply_earlier earlier).2
  generation := s.plane_generation.1
  point_core_action := point_core_action_of_conjugation ρ hρ }

omit [Finite G] [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)] in
/-- The source hyperplane contains every Q_H-displacement of V. -/
theorem seed_core_commutator {T : Sylow 2 G} {L V V₂ : Subgroup G}
    (s : NaturalSetup T L V V₁ V₂ V₃) (hTH : (T : Subgroup G) ≤ H) :
    ⁅V, Source.QH H⁆ ≤ V₃ := by
  have hQ : Source.QH H ≤ T := by
    have h := pCoreIn_le_sylow H (T.subtype hTH)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at h
  apply commutator_le_index_two
    (hQ.trans (le_sup_right.trans s.normalizes_V)) (hQ.trans s.seed_stable)
  exact flag_index_two s.seed_le (by decide : (8 : ℕ) ≠ 0)
    s.flag_orders.2.2 (s.natural_order.trans (by decide))

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
