module

public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

/-!
# Involution fusion in Suzuki matrix groups

Every involution has a unique fixed point on the concrete Suzuki ovoid.
The stabilizer of such a point is proper by transitivity, contains an
involution, and has no involutions in its intersection with any distinct
conjugate. It is therefore strongly embedded, which gives involution fusion.

The geometric input is the matrix proof of Huppert–Blackburn III, XI.3.3;
the strong-embedding implication is the proved [IG; 17.8(i)] in
`BenderSuzuki.SE.StrongEmbeddingConjugacy`. This supplies the Suzuki family
in Aschbacher–Smith, Lemma 16.2.6, printed p.1174 (combined manuscript of
1 March 2004), without a recognition or fusion assumption.
-/

namespace BenderSuzuki.MatrixGroups
open PFAppendixIII PFchapter1section1

/-- The concrete Suzuki matrix group has one conjugacy class of involutions. -/
public theorem suzuki_involutions_isConj (m : ℕ) (hm : 0 < m)
    (a b : SuzukiMatrixGroup m) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  obtain ⟨ω, haω, _⟩ := suzukiOvoid_involution_unique_fixed m hm a ha
  let M := MulAction.stabilizer (SuzukiMatrixGroup m) ω
  have hM : BenderSuzuki.IsStronglyEmbedded M := by
    refine ⟨?_, ⟨a, haω, ?_⟩, ?_⟩
    · intro htop
      have hall (v : SuzukiOvoid m) : v = ω := by
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) ω v
        have hgM : g ∈ M := by rw [htop]; trivial
        exact hg.symm.trans hgM
      exact suzukiOvoidInfinity_ne_zero m
        ((hall (suzukiOvoidInfinity m)).trans (hall (suzukiOvoidZero m)).symm)
    · exact ⟨((orderOf_eq_prime_iff (p := 2)).mp ha).2,
        ((orderOf_eq_prime_iff (p := 2)).mp ha).1⟩
    · intro g hg x hx hxg hxi
      have hxo : orderOf x = 2 := orderOf_eq_prime hxi.2 hxi.1
      have hxg' : x • (g⁻¹ • ω) = g⁻¹ • ω := by
        change x ∈ rightConjugate (MulAction.stabilizer (SuzukiMatrixGroup m) ω) g at hxg
        rwa [rightConjugate_stabilizer] at hxg
      have he := (suzukiOvoid_involution_unique_fixed m hm x hxo).unique hxg' hx
      apply hg
      change g • ω = ω
      exact (inv_smul_eq_iff.mp he).symm
  obtain ⟨g, hg⟩ := hM.involutions_conjugate
    ⟨((orderOf_eq_prime_iff (p := 2)).mp ha).2, ((orderOf_eq_prime_iff (p := 2)).mp ha).1⟩
    ⟨((orderOf_eq_prime_iff (p := 2)).mp hb).2, ((orderOf_eq_prime_iff (p := 2)).mp hb).1⟩
  exact isConj_iff.mpr ⟨g⁻¹, by simpa [rightConjugateElem] using hg⟩
end BenderSuzuki.MatrixGroups
