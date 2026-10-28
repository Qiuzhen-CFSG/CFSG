module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointQuotient
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.CommutatorLifting
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Consequences

/-!
# Original commutator lifting and perpendicular centralizer

The actual Sylow image makes the original point singular. The full
normalizer action preserves the quadratic form in the unchanged full V.
Together these prove F.9.1(e) in both conjugation directions, without a
commutator-lifting or parabolic-recognition premise. The same action and
the earlier intersection bound give C_G(V5)=C_G(V).

The fixed-space vanishing and intersection bound remain explicit earlier
12.6 inputs, owned by the nonsingular-centralizer source argument.
Source: Aschbacher--Smith, 12.6.24(6--7), printed pp.830--831.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The mixed-commutator clause F.9.1(e) is proved on the unchanged V.
Both conjugation directions use the same singular point. -/
theorem SourceHypothesis.original_commutator_lifting
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∀ g ∈ H,
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ = ⊥ := by
  obtain ⟨f,_,ha⟩ := S.original_normalizer_permutation_action D hZ hTV
  have hs : BinaryPermutation.TerminalOrthogonal.Eight.form (D.fullCoordinates hZ z).toAdd=0 := by
    by_contra hn
    exact S.original_point_singular D hZ z hz hTz ((D.fullCoordinates_nonsingular_iff hZ z).mp hn)
  intro g hg hVV h₁ h₂
  exact (D.fullSetup hZ T z).commutator_lifting_of_permutation_action hz hs
    (fun a => ⟨f a,ha a⟩) g (hH.2.1 hg) hVV h₁ h₂

/-- The centralizer equality in 12.6.24(6), on the original full V and
its literal perpendicular. No centralizer-equality premise is supplied. -/
theorem SourceHypothesis.original_perpendicular_centralizer
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3) :
    centralizer ((D.fullSetup hZ T z).V₅ : Set G) = centralizer (V : Set G) := by
  obtain ⟨f,_,ha⟩ := S.original_normalizer_permutation_action D hZ hTV
  have hs : BinaryPermutation.TerminalOrthogonal.Eight.form (D.fullCoordinates hZ z).toAdd=0 := by
    by_contra hn
    exact S.original_point_singular D hZ z hz hTz ((D.fullCoordinates_nonsingular_iff hZ z).mp hn)
  exact (D.fullSetup hZ T z).perpendicular_centralizer_eq hz hs
    (fun a => ⟨f a,ha a⟩)
    ((D.fullSetup hZ T z).G₅_le_normalizer ((D.fullSetup hZ T z).perpendicular_card hz) hbound)

end CFSG.Quasithin.Chapter12.Section06
