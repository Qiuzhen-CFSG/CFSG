module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.AssemblyBridges
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverAlgebra
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne
/-!
# Completing the five-dimensional cover contradiction

Starting with the genuine transported pair, choose the two H-adjustments and
obtain the noncommuting seed V₃^g and strict symplectic displacement. The actual
S₆ augmentation action makes Uα* have order two, so its two-core intersection
is a hyperplane and V₃^g* = Uα*. The fixed preimage therefore centralizes Uα.
Its inclusion in H_C^g lets 13.7.3(7) bound [V^g,C] by V₁^g. The concrete
fixed-hyperplane comparison gives V^g* = V₃^g*, hence the kernel factorization.
The intersecting-conjugates argument of 13.8.3 and 13.7.3(6) centralize that
kernel factor, contradicting the strict displacement.

All occurrences of g after the seed choice denote the same adjusted element.
F.9.13(2) is used on the full V_H, which is H-invariant, so V^g remains in H
under both adjustments. No star-image equality, seed, fixed-space bound or
strict displacement is an input.

Earlier inputs: the natural V and flag of 13.2/13.5; transitivity on V minus
1; abelian V_H from 13.7.8 in the standing §13.8 counterexample; the 13.5.5
normalizer intersection; [V_H,H_C]≤V₁ and [Q_H,V₃]≤V₁ from 13.7.3(6),(7);
and the literal transported F.9 configuration. The cover coordinates are
the concrete module alternative supplied by 13.8.5–6.

Source: Aschbacher–Smith 13.8.7, printed p.949 (PDF p.966).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G] [Finite G]

/-- The cover branch, using only the transported configuration and earlier
local and natural-module inputs. Both seed choices and the image comparison
are derived within the proof. -/
theorem no_asymmetric_cover
    (L H T V V₃ M : Subgroup G) (z g : G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)]
    [((zpowers z).subgroupOf (Source.UH H V₃)).Normal]
    (d : CoverHyperplanes.CoverCoordinates H V₃ (zpowers z))
    (hH : H = centralizer ({z} : Set G))
    (hcard : Nat.card (zpowers z) = 2) (hZC : zpowers z ≤ V₃)
    (hM : normalizer (zpowers z) ⊓ normalizer V₃ ≤ M)
    (a : CoverGeometry.NaturalAction M V)
    (f : CoverGeometry.NaturalFlag a T (zpowers z) V₃)
    (hLV : L ≤ normalizer V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l z = x)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ zpowers z)
    (hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers z)
    (hVH : (Source.VH H V).conjBy g ≤ H)
    (cfg : CoverGeometry.Configuration H V₃ (zpowers z) (Source.QH H) g)
    (hg : g ∈ G0 L T H) : False := by
  obtain ⟨h, hh, k, hk, hg', cfg', _, _, _, _, hnorm, _, hBstar, hBCne,
      hBC, hAB, hBW, _, _, hCW, _, hstrict⟩ :=
    CoverGeometry.prepare_cover_geometry H T V₃ M V (G0 L T H) z g hH hcard hZC
      (commutator_self_eq_bot_iff.mpr inferInstance) hM cfg a f le_sup_right hg
  let adjusted : G0 L T H := ⟨k⁻¹ * (g * h), hg'⟩
  let g' : G := adjusted
  let P := (Source.UH H V₃).conjBy g'
  let A := (zpowers z).conjBy g'
  let B := V₃.conjBy g'
  let W := V.conjBy g'
  change CoverGeometry.Configuration H V₃ (zpowers z) (Source.QH H) g' at cfg'
  change normalizer A = H.conjBy g' at hnorm
  change Source.starImage H B ≠ ⊥ at hBstar
  change ⁅B, V₃⁆ ≠ ⊥ at hBCne
  change ⁅B, V₃⁆ = A at hBC
  change A ≤ B at hAB
  change B ≤ W at hBW
  change V₃ ≤ normalizer W at hCW
  change A < ⁅W, V₃⁆ at hstrict
  have hBU : B ≤ P := map_mono (le_conjugateSpanBy V₃ H)
  have hWH : W ≤ H := by
    have hVHg : (Source.VH H V).conjBy g' ≤ H := by
      rw [CoverGeometry.double_adjustment_conjugate H (Source.VH H V) g h k
        (le_normalizer_conjugateSpanBy V H) hh]
      have hm := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hVH
      change ((Source.VH H V).conjBy g).conjBy k⁻¹ ≤ H.conjBy k⁻¹ at hm
      have hHi : H.conjBy k⁻¹ = H :=
        mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (H.inv_mem hk))
      rwa [hHi] at hm
    exact (map_mono (le_conjugateSpanBy V H)).trans hVHg
  have hAsize : Nat.card A = 2 := by
    change Nat.card ((zpowers z).map _) = 2
    rw [card_map_of_injective (MulAut.conj g').injective, hcard]
  have hPstar : Source.starImage H P ≠ ⊥ :=
    CoverGeometry.starImage_ne_bot_of_not_le H P cfg'.in_H cfg'.outside
  obtain ⟨hPsize, _⟩ := d.starImage_order_two_of_commutator_line P A cfg'.in_H
    hPstar hAsize (inf_comm A _ ▸ cfg'.disjoint) cfg'.commutator_eq
  -- The literal denominator is a hyperplane, and F.9.13(7) centralizes it.
  have hindex : (P ⊓ Source.QH H).relIndex P = 2 := by
    rw [inf_relIndex_left, ← starImage_card H P cfg'.in_H, hPsize]
  have hBPstar : Source.starImage H B = Source.starImage H P := by
    apply eq_of_le_of_card_ge (map_mono (subgroupOf_mono H hBU))
    change Nat.card (Source.starImage H P) ≤ Nat.card (Source.starImage H B)
    rw [starImage_card H P cfg'.in_H, ← inf_relIndex_left, hindex]
    exact (one_lt_card_iff_ne_bot _).mpr hBstar
  let E := d.fixedPreimage B
  have hPE : ⁅P, E⁆ = ⊥ :=
    d.fixedPreimage_centralizes P B A cfg'.in_H hBPstar.symm cfg'.commutator_eq
      (inf_comm A _ ▸ cfg'.disjoint)
  have hEH : E ≤ H.conjBy g' := by
    rw [← hnorm]
    apply le_trans _ (centralizer_le_normalizer (A : Set G))
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [commutator_comm P E] at hPE
    exact (commutator_mono le_rfl (hAB.trans hBU)).trans hPE.le
  have hEHC : E ≤ (Source.HC H V₃).conjBy g' :=
    le_conjugate_HC g' hEH (by rwa [commutator_comm])
  have hWE : ⁅W, E⁆ ≤ A := by
    have hm := map_mono (f := (MulAut.conj g').toMonoidHom) hHC
    rw [map_commutator] at hm
    exact (commutator_mono (map_mono (le_conjugateSpanBy V H)) hEHC).trans hm
  have he := d.starImage_comparison_of_commutator_line P B W A cfg'.in_H hBW hWH
    (map_mono (subgroupOf_mono H hBU)) hBstar hAsize
    (inf_comm A _ ▸ cfg'.disjoint) cfg'.commutator_eq hWE
  have hz : z ≠ 1 := by
    intro hz
    subst z
    simp at hcard
  let _ : IsMulCommutative (centralizerConjugateClosure V z) :=
    centralizerClosure_abelian hH
  have hVW : V ⊓ W = ⊥ :=
    disjoint_of_noncommuting_seeds V W V₃ B f.hyperplane_le hBW
      (by rwa [commutator_comm])
      (fun hi => intersecting_conjugates_commute L V hz hLV htrans g' hi)
  have hWZ : W ⊓ zpowers z = ⊥ := by
    apply le_bot_iff.mp
    rw [← hVW, inf_comm V W]
    exact inf_le_inf_left W f.line_le
  have hWW : ⁅W, W⁆ = ⊥ := by
    have hm := congrArg (fun X : Subgroup G => X.map (MulAut.conj g').toMonoidHom)
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V))
    rw [map_commutator, Subgroup.map_bot] at hm
    exact hm
  have hWA : W ≤ normalizer A := by
    apply le_trans _ (centralizer_le_normalizer (A : Set G))
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact le_bot_iff.mp ((commutator_mono le_rfl (hAB.trans hBW)).trans hWW.le)
  exact cover_contradiction_of_starImage_eq H W B V₃ (zpowers z) A
    hBW hWH he.symm hCW hQ hWZ hWA hBC hstrict

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
