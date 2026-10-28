module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.Commutator.ConjugateGeneration

/-!
# A component orbit meeting the rank of a normal component

Let K be a normal C-component containing B, whose center has order prime
to p. If a subgroup X of an ordinary component orbit has enough p-rank
that its rank plus that of B exceeds the ambient rank, that component is K.
Otherwise the component, and hence its whole orbit, centralizes K; the
two ranks then add. Normality is essential for centralization by the orbit.

Source application: Aschbacher--Smith, 12.5.3, printed pp.818--819,
comparing the three-space seven-radical with the original point component.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A component orbit with too much independent prime rank must be the
specified normal C-component. -/
theorem IsComponent.eq_normal_cComponent_of_orbit_rank
    {p : ℕ} [Fact p.Prime] {Q K B X A : Subgroup G}
    (hQ : IsComponent G Q) (hK : K.IsCComponent) [K.Normal]
    (hBK : B ≤ K) (hX : X ≤ componentOrbit Q A)
    (hz : Nat.Coprime p (Nat.card (center B)))
    (hr : primeRank p G < primeRank p X + primeRank p B) : Q = K := by
  by_contra hne
  have hc : ⁅Q,K⁆ = ⊥ := by
    rcases hQ.subnormal_dichotomy K hK.subnormal with hle | hc
    · exact (hne (hQ.isCComponent.eq_of_le hK hle)).elim
    · exact hc
  have hn : A ≤ normalizer (K : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hXB : X ≤ centralizer (B : Set G) :=
    (hX.trans (iSup_conjugates_le_centralizer Q A K hn hc)).trans
      (centralizer_le hBK)
  exact (Nat.not_lt_of_ge
    (ResidualCentralizerRank.primeRank_add_le_of_center_coprime X B hXB hz)) hr

end Theory.GroupTheory
