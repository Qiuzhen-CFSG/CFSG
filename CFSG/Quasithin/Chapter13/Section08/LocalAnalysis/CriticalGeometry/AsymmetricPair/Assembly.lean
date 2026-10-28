module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverAssembly
/-!
# The oriented impossibility in Aschbacher–Smith 13.8.7

For the genuine critical pair, D_H<U_H and Dγ=Uγ give an order-two
commutator line after conjugation by the inverse endpoint. This supplies a
nonidentity transvection in the actual H-action on U_H/V₁. Apply the complete
module alternatives of 13.8.5. In the three irreducible cases the center orbit
and the marked L₂T action construct a square conjugator, contradicting the
asymmetric two-core containments. The five-dimensional cover is excluded by
`no_asymmetric_cover`, including its two explicit H-adjustments.

The theorem is the oriented local deduction requested here. Its parent supplies
the following precise earlier source conclusions; no later §13.8 result is used:

* Notation 13.2.1 and 13.5.2–3: the genuine natural action on V, the marked
  line/plane/hyperplane, the L₂T parabolic action, and transitivity on V minus 1.
  The inputs `P`, `a`, `f`, `hz`, `hZ₂`, `hZ₃`, `b`, `hb`, `hbZ`, `hLV`, and
  `htrans` retain these coordinates, actions and containments.
* H=G₁=C_G(z), V₁=⟨z⟩ of order two, with V and U_H elementary abelian.
  Abelian V_H is the conclusion of 13.7.8 under the standing counterexample,
  recorded at the start of §13.8 as 13.8.2.
* `hM` is N_G(V₁)∩N_G(V₃)≤M_V from 13.5.5. The two commutator bounds `hHC`
  and `hQ` are the consequences of 13.7.3(6),(7).
* `Q` is genuine conjugation on the literal U_H/V₁; F.9.2(3) identifies its
  faithful action image with H/O₂(H). The denominator equalities `hDH`, `hDγ`,
  the full V_H and Vγ containments `hVHend`, `hVγH`, the disjoint central lines
  and cross-centralization are F.9.13(2),(5),(7) with that kernel identity.
* `hmodels` is exactly the module conclusion needed from 13.8.5(2),(3),
  triggered by an actual nonidentity transvection (constructed in the proof).
  Every alternative has a group equivalence and an intertwining linear
  equivalence. The S₇ alternative additionally retains the marked weight-two
  vector of 13.7.6(3b). The cover uses the canonical H/O₂(H) quotient.

No center conjugator, symmetry, noncommuting seed, symplectic displacement or
star-image comparison is an input. The opposite orientation, the full iff,
and the standing-counterexample assembly remain with the parent source owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.7,
printed pp.948–949, PDF pp.965–966.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The oriented impossibility in 13.8.7, with its earlier source inputs
explicit. In particular neither symmetry nor a line conjugator is assumed. -/
theorem no_asymmetric_criticalPair
    {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (V₂ V₃ L₂ M : Subgroup G) (z : V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)]
    [((zpowers (z : G)).subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) (zpowers (z : G)))
    (P : MarkedPlaneAction L₂ T V V₂)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hcard : Nat.card (zpowers (z : G)) = 2)
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hZ₂ : zpowers (z : G) ≤ V₂) (hZ₃ : zpowers (z : G) ≤ V₃)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G))
    (hM : normalizer (zpowers (z : G)) ⊓ normalizer V₃ ≤ M)
    (a : CoverGeometry.NaturalAction M V)
    (f : CoverGeometry.NaturalFlag a T (zpowers (z : G)) V₃)
    (hLV : L ≤ normalizer V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l (z : G) = x)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ zpowers (z : G))
    (hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers (z : G))
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hVγH : c.Vgamma ≤ H)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hdisj : zpowers (z : G) ⊓ c.Aone (zpowers (z : G)) = ⊥)
    (hcross : ⁅Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))),
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G))⁆ = ⊥)
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ (zpowers (z : G))))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            Pi.single (4 : Fin 7) 1 + Pi.single 5 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ (zpowers (z : G)))) :
    ¬ (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) <
        Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) = c.Ugamma V₃) := by
  rintro ⟨hstrict, hfull⟩
  have hUV : Source.UH H V₃ ≤ Source.VH H V :=
    conjugateSpanBy_mono f.hyperplane_le le_rfl
  have hγH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans hVγH
  have hHN : H ≤ normalizer (zpowers (z : G)) := by
    intro h hh
    exact mem_normalizer_iff_map_conj_eq.mpr
      (CoverGeometry.fixes_central_line H (z : G) h hH hh)
  have cfg := CoverGeometry.Configuration.of_criticalPair c V₃ (zpowers (z : G))
    hcard (hγH.trans hHN) hstrict hfull hDH hDγ hdisj (hUV.trans hVHend) hcross
  have hAsize : Nat.card (centerAlpha c (zpowers (z : G))) = 2 := by
    change Nat.card ((zpowers (z : G)).map _) = 2
    rw [card_map_of_injective (MulAut.conj (returnElement c : G)).injective, hcard]
  have hdis : zpowers (z : G) ⊓ centerAlpha c (zpowers (z : G)) = ⊥ := by
    rw [inf_comm]
    exact cfg.disjoint
  have ht := transvection_actor_of_commutator Q cfg.in_H cfg.commutator_eq hAsize hdis
  rcases hmodels ht with hirred | hcover
  · have hAU : centerAlpha c (zpowers (z : G)) ≤ Source.UH H V₃ := by
      change (zpowers (z : G)).conjBy (returnElement c : G) ≤ Source.UH H V₃
      rw [← cfg.commutator_eq]
      exact le_normalizer_iff_commutator_le_left.mp (cfg.in_H.trans Q.normalizes)
    have hcenter := nontrivialCenter_of_commutator Q cfg.in_H cfg.commutator_eq hAsize hdis
    obtain ⟨h, hh, l, _, hline, hsquare⟩ := center_conjugator_irreducible z Q P
      (centerAlpha c (zpowers (z : G))) hH hz hAU hAsize cfg.disjoint hcenter
      hZ₂ b hb hbZ hirred
    have hz1 : (z : G) ≠ 1 := by
      intro he
      rw [he] at hcard
      simp at hcard
    exact no_asymmetric_pair_of_center_conjugator H V₃ (z : G) (returnElement c : G)
      h l hH hz1 hcard hh hline hsquare cfg.inside cfg.outside
  · obtain ⟨d⟩ := hcover
    exact no_asymmetric_cover L H T V V₃ M (z : G) (returnElement c : G)
      d hH hcard hZ₃ hM a f hLV htrans hHC hQ
      (return_conjugate_le_H c _ hVHend) cfg (returnElement c).property

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
