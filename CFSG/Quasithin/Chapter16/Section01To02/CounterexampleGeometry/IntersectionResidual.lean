module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.IntersectionResidual.OddLinear

/-!
# The intersection and residual argument of Lemmas 16.2.8–9

From the explicit counterexample orbit, persistence, involution witness and
earlier A.1.34 inputs, `Reduction` proves intersection control, control of
two-subgroup normalizers, and L₀ ≰ H^g outside H. The concrete model facts
below discharge every center and local-prime condition: they give tight
embedding or the nontrivial covered Sz(8) case, and O^{p′}(H) = L₀ together
with O^{p′}(L₀) = L₀ for each prime specified in 16.2.9.

All normalizers and residual images are in the actual ambient group.
SuzukiMatrixGroup m has field order 2^(2m+1). Quotients by O₂ are identified
with the central quotient before applying A.1.34; these are not interchangeable
by convention. The parent remains responsible for constructing the explicit
orbit, persistence and earlier-source inputs in the standing counterexample.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 16.2.8–9, printed p.1175 (PDF p.1192).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe v
variable {G : Type v} [Group G] [Finite G]
variable {K : GroupClass.{v}} {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

/-- Lemma 16.2.8(2), with all center conditions discharged from the actual
model alternatives of 16.2.5. -/
theorem tightlyEmbedded_or_covered_suzuki_eight
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (alt : ComponentAlternative L) (pair : ComponentPairExhaustion K G)
    (a134 : ComponentPairResidualInput (G := G) K)
    (persist : ComponentPersistence z L u)
    {v : G} (hv : v ∈ conjugate L u) (hv2 : orderOf v = 2) :
    IsTightlyEmbedded L ∨ (pCore 2 L ≠ ⊥ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) := by
  let := (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).quasisimple
  rcases alt with ⟨n, hn, h⟩ | ⟨m, hm, h⟩ | ⟨r, _, hr, h⟩ | ⟨hc, h⟩
  · exact Or.inl (tightlyEmbedded_of_center_eq_bot c o pair a134 persist hv hv2
      (center_eq_bot_of_linear_even hn h))
  · exact Or.inl (tightlyEmbedded_of_center_eq_bot c o pair a134 persist hv hv2
      (center_eq_bot_of_suzuki hm h))
  · exact Or.inl (tightlyEmbedded_of_center_eq_bot c o pair a134 persist hv hv2
      (center_eq_bot_of_linear_odd hr h))
  · exact Or.inr ⟨hc, h⟩

/-- Both residual identities of 16.2.9 for the even linear quotient. The
prime ranges over every prime divisor of q − 1, where q = 2^n. -/
theorem residual_identities_of_linear_even_quotient
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {n p : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L ∧
    primeToResidual p (localComponentClosure z L) = ⊤ := by
  let := (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).quasisimple
  have hlocal := linear_even_core_quotient_local_prime hn h hp hd
  exact ⟨localNormalizer_residual c o a134 hlocal, closure_residual_eq_top c.localSetup o hlocal⟩

/-- The even linear model alternative, without requiring the caller to
construct its quotient identification separately. -/
theorem residual_identities_of_linear_even
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {n p : ℕ} (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L ∧
    primeToResidual p (localComponentClosure z L) = ⊤ := by
  let := (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).quasisimple
  have hlocal := linear_even_quotient_local_prime hn h hp hd
  exact ⟨localNormalizer_residual c o a134 hlocal, closure_residual_eq_top c.localSetup o hlocal⟩

/-- Both residual identities of 16.2.9 for every Suzuki quotient, including
the nontrivial covered Sz(8) case. The model parameter m has n = 2m + 1. -/
theorem residual_identities_of_suzuki_quotient
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {m p : ℕ} (hm : 0 < m)
    (h : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hp : p.Prime) (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L ∧
    primeToResidual p (localComponentClosure z L) = ⊤ := by
  let := (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).quasisimple
  have hlocal := covered_suzuki_quotient_local_prime hm h hp hd
  exact ⟨localNormalizer_residual c o a134 hlocal, closure_residual_eq_top c.localSetup o hlocal⟩

/-- The simple Suzuki model alternative of 16.2.5. -/
theorem residual_identities_of_suzuki
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {m p : ℕ} (hm : 0 < m)
    (h : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hp : p.Prime) (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L ∧
    primeToResidual p (localComponentClosure z L) = ⊤ := by
  have hlocal := suzuki_quotient_local_prime hm h hp hd
  exact ⟨localNormalizer_residual c o a134 hlocal, closure_residual_eq_top c.localSetup o hlocal⟩

/-- Both residual identities of 16.2.9 for the odd linear alternative,
with the specified prime p = 3. -/
theorem residual_identities_of_linear_odd
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (h : ClassicalGroup.IsPSL L 2 r) :
    (primeToResidual 3 (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L ∧
    primeToResidual 3 (localComponentClosure z L) = ⊤ := by
  let := (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).quasisimple
  have hlocal := linear_odd_quotient_local_prime hr ho h
  exact ⟨localNormalizer_residual c o a134 hlocal, closure_residual_eq_top c.localSetup o hlocal⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
