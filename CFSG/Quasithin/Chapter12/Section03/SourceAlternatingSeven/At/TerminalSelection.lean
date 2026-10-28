module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalSelection
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Intersections
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalContainment

/-!
# TerminalSelection at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalSelection`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} (S : Setup T L V) (D : S.LocalAnalysis)

include S D in

theorem all_weight_four_escape_at (escape : CentralizerEscape T)
    (v : V) (hv : weight (D.model.coordinates v).toAdd.val = 4) :
    ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x, _, hxw, hx⟩ := weight_four_escape_at S D (escape L V S.hypothesis S.chosen)
  obtain ⟨a, ha⟩ := weight_four_transitive (D.model.coordinates x).toAdd
    (D.model.coordinates v).toAdd hxw hv
  obtain ⟨l, hl⟩ := S.projection_surjective a
  have he := D.model.equivariant ⟨l, S.chosen.normalizes l.property⟩ x
  rw [D.component_action, hl, ha] at he
  have hxv : (l : G) * (x : G) * (l : G)⁻¹ = v :=
    congrArg Subtype.val (D.model.coordinates.injective (Multiplicative.toAdd.injective he))
  intro hc
  apply hx
  intro y hy
  have hym := map_centralizer_le_centralizer_image ({(x : G)} : Set G)
    (MulAut.conj (l : G)).toMonoidHom (mem_map_of_mem _ hy)
  have hyc : (l : G) * y * (l : G)⁻¹ ∈ centralizer ({(v : G)} : Set G) := by
    simpa only [Set.image_singleton, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, hxv] using hym
  have hlm : (l : G) ∈ normalizer (L : Set G) := L.le_normalizer l.property
  have h := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem (inv_mem hlm) (hc hyc)) hlm
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

include S D in

private theorem exists_central_weight_at
    (n : ℕ) (hn : n ≠ 0) (hc : ¬ 2 ∣ Nat.card (WeightWord n))
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = n ∧
      (v : G) ∈ omegaCenterIn (T : Subgroup G) := by
  have hTN := ((structural L S.hypothesis).2.2 V S.chosen).1
  let f : T →* normalizer (V : Set G) := (T : Subgroup G).subtype.codRestrict _ fun t => hTN t.property
  let : MulAction T (WeightWord n) := MulAction.compHom _ (D.model.permutation.comp f)
  obtain ⟨w, hw⟩ := T.2.nonempty_fixed_point_of_prime_not_dvd_card (WeightWord n) hc
  let v : V := D.model.coordinates.symm (Multiplicative.ofAdd w.val)
  have hvw : weight (D.model.coordinates v).toAdd.val = n := by
    simpa only [v, D.model.coordinates.apply_symm_apply, toAdd_ofAdd] using w.property
  have hv1 : v ≠ 1 := by
    intro he
    simp only [he, map_one] at hvw
    have hwzero : weight (0 : Word) = 0 := by decide
    exact hn (hvw.symm.trans hwzero)
  refine ⟨v, hv1, hvw, (mem_omegaCenterIn_iff _ _).mpr
    ⟨S.chosen.le_sylow v.property, ?_, ?_⟩⟩
  · intro t ht
    have hf : evenRepresentation (D.model.permutation (f ⟨t, ht⟩)) w.val = w.val :=
      congrArg Subtype.val (hw ⟨t, ht⟩)
    have he := D.model.equivariant (f ⟨t, ht⟩) v
    simp only [v, D.model.coordinates.apply_symm_apply, toAdd_ofAdd] at he
    rw [hf] at he
    have hv : V.normalizerMonoidHom (f ⟨t, ht⟩) v = v := by
      apply D.model.coordinates.injective
      apply Multiplicative.toAdd.injective
      simpa only [v, D.model.coordinates.apply_symm_apply, toAdd_ofAdd] using he
    have hv' := congrArg Subtype.val hv
    change t * (v : G) * t⁻¹ = (v : G) at hv'
    exact mul_inv_eq_iff_eq_mul.mp hv'
  · let := S.chosen.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ v.property

include S D in

theorem exists_central_weight_four_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 4 ∧
      (v : G) ∈ omegaCenterIn (T : Subgroup G) :=
  exists_central_weight_at S D 4 (by decide) (by rw [card_weightFourWord]; decide) structural

include S D in

theorem omega_center_centralizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv1, hvw, hvZ⟩ := exists_central_weight_at S D 6 (by decide)
    (by rw [card_weightSixWord]; decide) structural
  exact (centralizer_le (Set.singleton_subset_iff.mpr hvZ)).trans
    (D.pointCentralizers v hv1 (Or.inr hvw))

namespace TerminalPoint

variable {S D} (P : TerminalPoint S D)

theorem residual_escape_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ¬ P.K ≤ normalizer (L : Set G) := by
  intro hk
  have hTH : (T : Subgroup G) ≤ P.H := P.minimal.1.1.2
  have hHM : ¬ P.H ≤ normalizer (L : Set G) := P.minimal.1.2
  have he := congrArg (map P.H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTH] at he
  apply hHM
  rw [← he]
  exact sup_le hk (S.hypothesis.source_sylow_normalizes_at structural)

theorem not_solvable_at (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ¬ Group.IsSolvable P.H :=
  hstar_not_solvable_at S structural P.minimal hr hw

end TerminalPoint

include S D in

theorem exists_terminalPoint_at (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : Nonempty (TerminalPoint S D) := by
  obtain ⟨v, hv1, hvw, hvZ⟩ := exists_central_weight_four_at S D structural
  have hvc := (mem_omegaCenterIn_iff _ _).mp hvZ
  have hout := all_weight_four_escape_at S D escape v hvw
  have hTC : (T : Subgroup G) ≤ centralizer ({(v : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hvc.2.1) t ht)
  have ho : orderOf (v : G) = 2 := orderOf_eq_prime hvc.2.2 (by
    intro he
    exact hv1 (Subtype.ext he))
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ho)
  have hzC : zpowers (v : G) ≤ centralizer ({(v : G)} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCN : centralizer ({(v : G)} : Set G) ≤ normalizer (zpowers (v : G) : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hcore := le_pCoreIn_of_normalizes hp hzC hCN
  have hne : (centralizer ({(v : G)} : Set G)).pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hv1 (Subtype.ext (mem_bot.mp (he ▸ hcore (mem_zpowers (v : G)))))
  obtain ⟨H, hHC, hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧
      ¬ H ≤ normalizer (L : Set G))
    (centralizer ({(v : G)} : Set G)) ⟨⟨hne, hTC⟩, hout⟩
  exact ⟨⟨v, hv1, hvw, hvZ, H, hH, hHC⟩⟩

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

