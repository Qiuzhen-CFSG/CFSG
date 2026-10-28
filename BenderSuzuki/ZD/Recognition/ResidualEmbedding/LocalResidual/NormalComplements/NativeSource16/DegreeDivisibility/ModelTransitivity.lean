module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity.LinearSuzuki
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity.Unitary
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Source

/-!
# Sylow-normalizer transitivity in the original odd central cover

The actual covering-model alternatives identify L with PSL₂, Suzuki, PSU₃
or SU₃. Concrete involution fusion or the fixed-field torus gives fusion
of every pair of nonidentity omega elements. The source omega-center
equality and Burnside's lemma then put the conjugator in N_L(P), for the
original specified Sylow P. This is the model transitivity used on Q#u
in GLS4, Chapter 2, Lemma 16.4(c).

No root-transitivity, involution-class or normalizer-action conclusion is
assumed. Source: GLS4, Chapter 4, Lemmas 2.8 and 3.2(b,c).
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup Source16ModelTransitivity
variable {L : Type*} [Group L] [Finite L] {n : ℕ}

/-- The actual Sylow normalizer is transitive on the nonidentity elements
of its ambient first omega subgroup, in all four odd-central-cover models. -/
public theorem oddCentralCover_omega_normalizer_transitive (hn : 2 ≤ n)
    (hperfect : commutator L = ⊤) (hodd : Odd (Nat.card (center L)))
    (hmodel : IsSimpleBenderGroupAtExponent n (L ⧸ center L))
    (P : Sylow 2 L) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup L), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup L), x ≠ 1 →
        ∃ g ∈ normalizer (P : Set L), MulAut.conj g z = x := by
  apply normalizer_transitive_of_omega_fusion P
    (oddCentralCover_omega_geometry hn hperfect hodd hmodel P).1
  rcases oddCentralCover_model_cases hn hperfect hodd hmodel with
    ⟨_,⟨e⟩⟩ | ⟨_,m,hm,rfl,⟨e⟩⟩ | ⟨E,hfield,hfinite,J,hJ,hcard,hfixed,he⟩
  · exact linear_omega_fusion (by omega) e P
  · exact suzuki_omega_fusion hm e P
  · rcases he with ⟨_,⟨e⟩⟩ | ⟨_,_,⟨e⟩⟩
    · exact unitary_projective_omega_fusion J hJ hn hcard hfixed e P
    · exact unitary_special_omega_fusion J hJ hn hcard hfixed e P

end BenderSuzuki.ZD.RankOneModelGeometry
