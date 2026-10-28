module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer
public import Theory.Representation.BinaryOffender.CubicMarker

/-!
# The preceding no-cubic hypothesis on the literal temporary actor

Apply the section-lifting calculation to q:H→H/Q and I=q(J(C_H(E))).
The full core is a two-group and lies in C_H(E), so the cubic lift lies in
that same centralizer. The marker comparison here is the exact preceding
paired-coordinate identity C_I(P)=C_I(V/E), written as displacement on the
original V; it remains a source-assembly input, along with the ambient 15.3.49(5).

This proves the prime-to-three conclusion before any classification and
without a prior stabilization hypothesis on the lifted cubic.
Source: Aschbacher–Smith, proof of 15.3.67, pp.1153–1154, combined manuscript
of 1 March 2004.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open Replacement.Transvections
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

/-- Actual temporary-group application of the preceding 15.3.49(5) input.
The projection of V/E, encoded by `hmarker`, is retained inside the original
first-summand action; no final no-cubic premise is assumed. -/
theorem temporary_markerCentralizer_coprime_three
    (Y T V E Z : Subgroup G) [IsMulCommutative V]
    [IsElementaryAbelian 2 (localLine T V E)]
    (d : TemporaryData Y T V E) (hZV : Z ≤ V)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (P : Submodule (ZMod 2) W)
    (hmarker : ∀ x ∈ localCentralizer T V E,
      QuotientGroup.mk' (localCore T V E) x ∈ thompsonImage T V E →
      (∀ w ∈ P, σ (QuotientGroup.mk' (localCore T V E) x) w = w) →
        ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E) :
    Nat.Coprime 3 (Nat.card
      (subspaceKernel (σ.comp (thompsonImage T V E).subtype) P ⊤)) := by
  have hZH : Z ≤ temporaryLineNormalizer T V E := hZV.trans
    ((le_conjugateSpanBy V (lineNormalizer E)).trans
      (d.span_le_sylow.trans (Replacement.lineT_le_temporary T V E d.line_le)))
  have hNZ : Nat.Coprime 3 (Nat.card
      (normalizer (Z.subgroupOf (temporaryLineNormalizer T V E) :
        Set (temporaryLineNormalizer T V E)))) := by
    rw [← subgroupOf_normalizer_eq hZH]
    let j : ((normalizer (Z : Set G)).subgroupOf (temporaryLineNormalizer T V E)) →*
        normalizer (Z : Set G) := {
      toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply hZ.of_dvd_right (Subgroup.card_dvd_of_injective j ?_)
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : normalizer (Z : Set G) => (z : G)) h
  have hQ : IsPGroup 2 (QuotientGroup.mk' (localCore T V E)).ker := by
    rw [QuotientGroup.ker_mk', localCore_eq_pCore]
    exact pCore_isPGroup
  have hQC : (QuotientGroup.mk' (localCore T V E)).ker ≤ localCentralizer T V E := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact ⟨x.property, d.core_centralizes_line Y T V E hx⟩
  have hCE : localCentralizer T V E ≤
      centralizer (localLine T V E : Set (temporaryLineNormalizer T V E)) := by
    rw [localCentralizer_eq T V E (line_le_temporary T V E d.line_le d.span_le_sylow)]
  have hIC : thompsonImage T V E ≤
      (localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E)) :=
    map_mono (sSup_le (fun A hA => hA.1))
  exact markerCentralizer_coprime_three_of_section
    (QuotientGroup.mk' (localCore T V E)) (QuotientGroup.mk'_surjective _)
    hQ (localLine T V E) (V.subgroupOf (temporaryLineNormalizer T V E))
    (Z.subgroupOf (temporaryLineNormalizer T V E)) (localCentralizer T V E)
    hQC hCE (fun _ hv => hZV hv) hNZ σ (thompsonImage T V E) hIC P hmarker

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
