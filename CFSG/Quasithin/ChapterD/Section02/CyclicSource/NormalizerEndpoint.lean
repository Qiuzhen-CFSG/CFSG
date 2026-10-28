module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import Theory.Representation.SmallBinaryPrimeNormalizer

/-!
# The cyclic source normalizer endpoint

The original rank-one minimum actors generate the group by small involutions.
Once support separation in D.2.23 or D.2.24 has made the marked prime support
the whole module, the faithful binary normalizer theorem gives the literal
join and commutator identities required by the local classification.

The representation, prime subgroup and selected involution are unchanged.
The support and normality proofs remain in the D.2.23–24 source assembly.
Source: Aschbacher–Smith D.2.23–24, printed pp.189–190.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem small_isInvolution {t : G} (ht : t ∈ smallSupportInvolutions ρ) :
    BenderSuzuki.PFAppendixIII.IsInvolution t := by
  refine ⟨?_, ?_⟩
  · intro he
    have ho := ht.1
    simp [he] at ho
  · rw [← ht.1]
    exact pow_orderOf_eq_one t

/-- The same small-support generators also give ordinary involution generation. -/
theorem CoreHypotheses.involution_generated (h : CoreHypotheses ρ) :
    closure {s : G | BenderSuzuki.PFAppendixIII.IsInvolution s} = ⊤ := by
  apply top_unique
  rw [← h.smallSupport_generated]
  exact closure_mono (fun _ hs => small_isInvolution hs)

/-- The source D.2.24 endpoint on the original binary plane. -/
theorem CoreHypotheses.three_normalizer_endpoint (h : CoreHypotheses ρ)
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ) :
    D ⊔ zpowers t = ⊤ ∧ ⁅D, zpowers t⁆ = D :=
  Representation.SmallBinaryPrimeNormalizer.three_generation ρ h.faithful hdim D hD t
    (small_isInvolution ht)

/-- The source D.2.23 endpoint on the original four-dimensional binary module. -/
theorem CoreHypotheses.five_normalizer_endpoint (h : CoreHypotheses ρ)
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 5)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ) :
    D ⊔ zpowers t = ⊤ ∧ ⁅D, zpowers t⁆ = D :=
  Representation.SmallBinaryPrimeNormalizer.five_generation ρ h.faithful hdim D hD
    h.involution_generated t (small_isInvolution ht)

end CFSG.Quasithin.ChapterD.CyclicSource
