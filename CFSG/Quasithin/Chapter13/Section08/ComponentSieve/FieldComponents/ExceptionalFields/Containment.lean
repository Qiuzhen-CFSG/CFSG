module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# Containment and five-point geometry in the exceptional branch of 13.8.20

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed p.955 (PDF p.972), with the overlap identities from 13.7.3(6),(9).

This module constructs the five-point coset equivalence in the parent's
compatible H* ≃ S₅ action. It uses the actual rank-one Borel, specified as
the normalizer in K* of a Sylow two-subgroup, its residual containment in M,
and its Sylow supplement in T. The two-core containment makes the overlap
proper after passage to H*. All these source premises remain explicit.

The claim L₁ ≤ K is still open: the noncontainment reduction to the
triple-cover case, the unitary E₉ obstruction, and the two central factors
in the L₂(4) case must be assembled here. The point-coordinate result does
not assert that containment or the exceptional contradiction is proved.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The two-core belongs to the actual overlap: 13.7.3(6) says it
normalizes V, and 13.7.3(9) identifies its normalizer inside H. -/
theorem twoCore_le_overlap (H M V V₃ : Subgroup G)
    (hV₃ : V₃ ≤ V) (hcomm : ⁅V, Source.QH H⁆ = V₃)
    (hN : H ⊓ normalizer (V : Set G) = H ⊓ M) : Source.QH H ≤ H ⊓ M := by
  rw [← hN]
  refine le_inf (pCoreIn_le 2 H) ?_
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [hcomm]
  exact hV₃

/-- The source containment of B = O²(B₀), together with its Sylow
supplement inside T, places the whole Borel in M. -/
theorem borel_le_of_residual (B₀ T M : Subgroup G)
    (hB : (pResidual 2 B₀).map B₀.subtype ≤ M)
    (S : Sylow 2 B₀) (hS : (S : Subgroup B₀).map B₀.subtype ≤ T)
    (hT : T ≤ M) : B₀ ≤ M := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := congrArg (Subgroup.map B₀.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
  rw [← h]
  exact sup_le hB (hS.trans hT)

omit [Finite G] in
/-- The overlap remains proper in H/O₂(H); killing the two-core does
not lose the source hypothesis H ≰ M. -/
theorem star_overlap_ne_top (H M : Subgroup G) (hH : ¬ H ≤ M)
    (hQ : Source.QH H ≤ M) : Source.starImage H (H ⊓ M) ≠ ⊤ := by
  intro htop
  have hker : pCore 2 H ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    exact ⟨x.property, hQ (mem_map.mpr ⟨x, hx, rfl⟩)⟩
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 H))) htop
  rw [Source.starImage, comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr hker, comap_top] at h
  apply hH
  intro x hx
  have hx' : (⟨x, hx⟩ : H) ∈ (H ⊓ M).subgroupOf H := by rw [h]; trivial
  exact hx'.2

/-- The actual five-point coset coordinates in the L₂(4) branch. The
Borel is specified as the normalizer in K* of its Sylow two-subgroup.
Only the residual B is assumed contained in M; the full Borel containment
and the properness of the starred overlap are proved above. The returned
coordinates use the parent's prescribed S₅ equivalence and hence the
same K* ≃ A₅ action, without any independent relabelling of that action. -/
theorem linear_two_four_point_coordinates
    (H K M T B₀ V V₃ : Subgroup G) [(Source.starImage H K).Normal]
    (hH : ¬ H ≤ M) (hTH : T ≤ H) (hTM : T ≤ M)
    (hV₃ : V₃ ≤ V) (hcomm : ⁅V, Source.QH H⁆ = V₃)
    (hN : H ⊓ normalizer (V : Set G) = H ⊓ M)
    (hB₀H : B₀ ≤ H) (hB : (pResidual 2 B₀).map B₀.subtype ≤ M)
    (S : Sylow 2 B₀) (hS : (S : Subgroup B₀).map B₀.subtype ≤ T)
    (P : Sylow 2 (Source.starImage H K))
    (hBorel : Source.starImage H B₀ =
      (normalizer (P : Set (Source.starImage H K))).map (Source.starImage H K).subtype)
    (eA : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 5))
    (he : ∀ k : Source.starImage H K, e k = eA k)
    (t : Source.Hstar H) (ht : t ∈ Source.starImage H T)
    (houter : (MulAut.conjNormal t : MulAut (Source.starImage H K)) ∉
      MulAut.innerSubgroup (Source.starImage H K)) :
    ∃ d : (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) ≃ Fin 5,
      ∀ h ω, d (h • ω) = e h (d ω) := by
  have hB₀M := borel_le_of_residual B₀ T M hB S hS hTM
  have hBstar : Source.starImage H B₀ ≤ Source.starImage H (H ⊓ M) :=
    map_mono (subgroupOf_mono H (le_inf hB₀H hB₀M))
  rw [hBorel] at hBstar
  have htJ : t ∈ Source.starImage H (H ⊓ M) :=
    map_mono (subgroupOf_mono H (le_inf hTH hTM)) ht
  have htK : t ∉ Source.starImage H K := by
    intro htK
    exact houter ⟨⟨t, htK⟩, MulAut.conjNormal_val.symm⟩
  exact Theory.SpecificGroups.Alternating.FiveBorelOvergroups.coordinates_of_borel
    (Source.starImage H K) (Source.starImage H (H ⊓ M)) e eA he P hBstar
    (star_overlap_ne_top H M hH ((twoCore_le_overlap H M V V₃ hV₃ hcomm hN).trans inf_le_right))
    t htJ htK

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment
