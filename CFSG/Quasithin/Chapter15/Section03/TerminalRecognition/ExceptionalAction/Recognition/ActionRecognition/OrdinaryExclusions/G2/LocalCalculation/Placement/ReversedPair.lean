module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.AlignedPair
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.MarkedFactor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.ReversedPair.Model

/-!
# Excluding the reversed binary G₂ parabolic assignment

The image of J(T) is a normal two-subgroup of the first local image and
centralizes V, by the relative Thompson normalization and J(T) = J(R).
The core of the first residual centralizes V as well, whereas the whole
first local core does not: its commutator with V is the marked nontrivial F.

If the first local image were the second model parabolic, the concrete
involution test in Model would place every elementary generator of J(T)
in the first model core. The source identity XE = [XE, J(T)] would then
put the whole image of XE in that two-group. This is impossible because
XE maps onto the first model residual, which contains the specified cubic.
Combining this exclusion with AlignedPair gives the standard orientation.

All transports use the original core projection and the supplied model
isomorphism. Only genuine group-theoretic SourceInput clauses are needed;
no representation classification or action identification is used.

Source: Aschbacher–Smith, 15.3.66–68 and the final proof of 15.3.1,
printed pp.1152–1155 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair
open Representation.BinaryOffender
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}

/-- The relative Thompson and commutator hypotheses exclude the reversed
assignment of the two source local groups. -/
theorem not_reversed_source_pair (d : SourceInput V)
    (e : coreQuotient H ≃* (Model (ZMod 2)))
    (_hT : ((d.T : Subgroup H).map coreProjection).map e.toMonoidHom = unipotent)
    (h₁ : (d.G1.map coreProjection).map e.toMonoidHom = BinaryCore.secondParabolic)
    (h₂ : (d.G2.map coreProjection).map e.toMonoidHom = firstParabolic) : False := by
  let q : H →* Model (ZMod 2) := e.toMonoidHom.comp coreProjection
  have hqker : q.ker = pCore 2 H := by
    ext x
    change e (coreProjection x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hqcore (L : Subgroup H) : (L.pCoreIn 2).map q = (L.map q).pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup q (by rw [hqker]; exact pCore_isPGroup) L
  have hG₁ : d.G1.map q = BinaryCore.secondParabolic := by
    simpa only [q, map_map] using h₁
  have hG₂ : d.G2.map q = firstParabolic := by
    simpa only [q, map_map] using h₂
  have hY : d.YF.map q = (pResidual 2 BinaryCore.secondParabolic).map
      BinaryCore.secondParabolic.subtype := by
    rw [← d.first_residual, map_embedded_pResidual, hG₁]
  have hX : d.XE.map q = (pResidual 2 firstParabolic).map firstParabolic.subtype := by
    rw [← d.second_residual, map_embedded_pResidual, hG₂]
  let C := d.R.map q
  have hres : ((pResidual 2 BinaryCore.secondParabolic).map
      BinaryCore.secondParabolic.subtype).pCoreIn 2 ≤ C := by
    rw [← hY, ← hqcore]
    exact map_mono (le_sup_right.trans d.core_bound)
  have hproper : ¬ BinaryCore.secondParabolic.pCoreIn 2 ≤ C := by
    intro hc
    rw [← hG₁, ← hqcore] at hc
    have hc' := map_le_map_iff.mp hc
    rw [hqker, sup_eq_left.mpr (le_sup_left.trans d.core_bound)] at hc'
    apply d.singular_nontrivial
    rw [← d.local_commutator, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    exact hc'.trans d.centralizer_eq.le
  let J := Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)
  have hJT : J ≤ (d.T : Subgroup H) := sSup_le fun _ hA => hA.1
  have hJR : J ≤ d.R := by
    dsimp only [J]
    rw [d.sylow_thompson]
    exact sSup_le fun _ hA => hA.1
  have hJG₁ : J ≤ d.G1 := hJT.trans (by rw [d.first_local]; exact le_sup_right)
  have hJq : J.map q ≤ BinaryCore.secondParabolic.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((d.T.isPGroup'.to_le hJT).map q)
      ((map_mono hJG₁).trans hG₁.le)
    rw [← hG₁]
    exact (map_mono d.thompson_normalized).trans (J.le_normalizer_map q)
  have hJfirst : J.map q ≤ firstParabolic.pCoreIn 2 := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA x hx
    let _ : IsElementaryAbelian 2 A := hA.2.1
    have hxJ : x ∈ J := (le_sSup hA) hx
    apply ReversedPair.involution_mem_first_core C hres hproper
      (hJq (mem_map_of_mem q hxJ)) ?_ (mem_map_of_mem q (hJR hxJ))
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx, map_one]
  have hXcore : d.XE.map q ≤ firstParabolic.pCoreIn 2 := by
    conv_lhs => rw [d.second_commutator]
    rw [map_commutator]
    apply (commutator_mono ?_ hJfirst).trans
      (le_normalizer_iff_commutator_le_right.mp
        (firstParabolic.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image firstParabolic
            (pCore 2 firstParabolic))))
    exact (map_mono (show d.XE ≤ d.G2 by rw [d.second_local]; exact le_sup_left)).trans hG₂.le
  have hc : cubicActor ∈ firstParabolic.pCoreIn 2 := by
    apply hXcore
    rw [hX]
    exact mem_map_of_mem firstParabolic.subtype cubicActor_residual
  rw [firstParabolic_pCore] at hc
  have hd := orderOf_dvd_natCard (⟨cubicActor, hc⟩ : BinaryCore.core)
  rw [← orderOf_injective BinaryCore.core.subtype BinaryCore.core.subtype_injective,
    BinaryCore.card_core] at hd
  change orderOf cubicActor ∣ 32 at hd
  rw [cubicActor_order] at hd
  norm_num at hd

/-- The actual source pair admits a simultaneous standard marking. This
applies the exclusion to the two alternatives from AlignedPair. -/
theorem aligned_source_pair_standard (d : SourceInput V)
    (e0 : coreQuotient H ≃* (Model (ZMod 2))) :
    ∃ e : coreQuotient H ≃* (Model (ZMod 2)),
      ((d.T : Subgroup H).map coreProjection).map e.toMonoidHom = unipotent ∧
      (d.G1.map coreProjection).map e.toMonoidHom = firstParabolic ∧
      (d.G2.map coreProjection).map e.toMonoidHom = BinaryCore.secondParabolic := by
  obtain ⟨e, hT, hp⟩ := aligned_source_pair d e0
  rcases hp with hp | hp
  · exact ⟨e, hT, hp⟩
  · exact (not_reversed_source_pair d e hT hp.1 hp.2).elim

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
