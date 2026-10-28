module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Interchange
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverAlgebra
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Symplectic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne

/-!
# The oriented critical-pair impossibility

For a genuine `CriticalPair`, the two denominator conditions yield the
nontrivial quotient transvection configuration at the inverse endpoint.
`no_asymmetric_criticalPair` excludes D_H<U_H together with Dγ=Uγ from
the explicit earlier source conclusions listed in `Assembly`. It constructs
the center conjugator in all three irreducible cases. In the S₆ cover it
constructs the adjusted seed, derives the orthogonal hyperplane and strict
displacement, and proves the fixed-hyperplane comparison and contradictory
commutator equality.

This is the oriented deduction in Aschbacher–Smith 13.8.7, pp.948–949.
The parent retains the opposite orientation, the full equivalence, and
instantiation of the earlier conclusions from the standing counterexample.

Exact earlier inputs used by the proved deductions:
* the elementary abelian U_H and its order-two line V₁ (13.5 and 13.7.2);
* endpoint containment and normalization, disjointness of V₁ and A₁, and
  [D_H,Dγ]=1 (F.9.13(2),(4),(5),(7));
* the two kernel identities from Q_H=C_H(U_H/V₁) (F.9.2(3));
* H=G₁=C_G(z), V₁=⟨z⟩ in the interchange theorem;
* [Q_H,V₃]≤V₁ and [V_H,H_C]≤V₁ (13.7.3(6),(7)); the needed
  commuting-intersection property is proved from abelian V_H and transitivity;
* the actual natural V and parabolic markings of §13.2/13.5, the
  normalizer intersection in 13.5.5, and the complete module alternatives
  in 13.8.5 with the S₇ marking of 13.7.6(3b).

The assembled proof uses no later §13.8 theorem.
No subgroup is required to be normal in the ambient simple group.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G] [Finite G]

/-- The cover kernel is an actual hyperplane when its actual star image has
order two. The order-two conclusion must come from the cover action. -/
theorem Dalpha_relIndex_of_star_card_two
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ : Subgroup G)
    (hH : Ualpha c V₃ ≤ H) (hstar : Nat.card (Source.starImage H (Ualpha c V₃)) = 2) :
    (Dalpha c V₃).relIndex (Ualpha c V₃) = 2 := by
  rw [Dalpha, inf_relIndex_left, ← starImage_card H (Ualpha c V₃) hH, hstar]

/-- Recognition on the literal quotient U_H/V₁ after transport of the genuine
critical pair, including its nontrivial displacement and specified center. -/
theorem transvections_at_returned_endpoint
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hcard : Nat.card V₁ = 2) (hHN : H ≤ normalizer (V₁ : Set G))
    (hγH : c.Ugamma V₃ ≤ H)
    (hUend : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hZ : (V₁.subgroupOf (Source.UH H V₃)).Normal)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) <
      Source.UH H V₃)
    (hfull : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hdisj : V₁ ⊓ c.Aone V₁ = ⊥) :
    let _ := hZ
    ∃ action : Ualpha c V₃ →* MulAut (Source.Utilde H V₃ V₁),
      (∀ p : Ualpha c V₃, ∀ u : Source.UH H V₃,
        ∃ hmem : (p : G) * (u : G) * (p : G)⁻¹ ∈ Source.UH H V₃,
          action p (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) =
            QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
              ⟨(p : G) * (u : G) * (p : G)⁻¹, hmem⟩) ∧
      commutatorAction action.range (Source.Utilde H V₃ V₁) =
        ((centerAlpha c V₁).subgroupOf (Source.UH H V₃)).map
          (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))) ∧
      Nat.card (commutatorAction action.range (Source.Utilde H V₃ V₁)) = 2 ∧
      action.range ≠ ⊥ ∧
      ∀ p : Ualpha c V₃, binaryLinear (action p) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := by
  let _ := hZ
  have hαH : Ualpha c V₃ ≤ H := return_conjugate_le_H c _ hUend
  obtain ⟨hc, _, _, hd⟩ := transported_configuration c V₃ V₁ hcard
    (hγH.trans hHN) hstrict hfull hDH hDγ hdisj
  have hsize : Nat.card (centerAlpha c V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (returnElement c : G)).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj _).injective, hcard]
  obtain ⟨action, hact, hi, hs, hn, ht⟩ := quotient_transvections_of_commutator_line
    (Ualpha c V₃) (Source.UH H V₃) V₁ (centerAlpha c V₁)
    (hαH.trans (le_normalizer_conjugateSpanBy V₃ H)) (hαH.trans hHN)
    hZ hc hsize (by rwa [inf_comm])
  exact ⟨action, fun p u => ⟨_, hact p u⟩, hi, hs, hn, ht⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
