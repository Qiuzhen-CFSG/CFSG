module
public import Theory.SpecificGroups.AlternatingSix.PGLNineTwentyConjugacy

/-!
# Conjugacy of the full pair subgroups in the cubic normalizer

For a projection onto PGL₂(9) with kernel of order three, any subgroup of
order sixty containing that kernel is its full preimage of an order-twenty
subgroup. Those quotient subgroups are conjugate Sylow-five normalizers.
Lifting the conjugating element therefore aligns the entire pair subgroup.
-/

public noncomputable section
open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter
namespace Sporadic.Janko3.SourceRecognition

private theorem card_kernel_image {E : Type*} [Group E] [Finite E]
    (f : E →* PGL2 Nine.F) (H : Subgroup E) :
    Nat.card (f.ker.subgroupOf H) * Nat.card (H.map f) = Nat.card H := by
  have hh := (f.comp H.subtype).ker.card_mul_index
  rw [index_ker] at hh
  have hr : (f.comp H.subtype).range = H.map f := by
    rw [←MonoidHom.map_range,H.range_subtype]
  rwa [hr] at hh

/-- All full order-sixty pair subgroups containing the same cubic kernel
are conjugate inside the actual cubic normalizer. -/
theorem cubic_pair_overgroups_conjugate
    {E : Type*} [Group E] [Finite E]
    (f : E →* PGL2 Nine.F) (hf : Function.Surjective f) (hker : Nat.card f.ker = 3)
    (H K : Subgroup E) (hH : f.ker ≤ H) (hK : f.ker ≤ K)
    (hcH : Nat.card H = 60) (hcK : Nat.card K = 60) :
    ∃ g : E, H.map (MulAut.conj g).toMonoidHom = K := by
  have hcard (J : Subgroup E) (hJ : f.ker ≤ J) (hcJ : Nat.card J = 60) :
      Nat.card (J.map f) = 20 := by
    have hh := card_kernel_image f J
    rw [Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv,hker,hcJ] at hh
    omega
  obtain ⟨g,hg⟩ := AlternatingSix.PGLNineFiveNormalizer.twenty_subgroups_conjugate
    (H.map f) (K.map f) (hcard H hH hcH) (hcard K hK hcK)
  obtain ⟨x,rfl⟩ := hf g
  have hcomp : f.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (f x)).toMonoidHom.comp f := by
    apply MonoidHom.ext
    intro y
    change f (x * y * x⁻¹) = f x * f y * (f x)⁻¹
    simp only [map_mul,map_inv]
  have himage : (H.map (MulAut.conj x).toMonoidHom).map f = K.map f := by
    rw [map_map,hcomp,←map_map]
    exact hg
  have hconj : f.ker ≤ H.map (MulAut.conj x).toMonoidHom := by
    rw [←Subgroup.Normal.map_conj_eq f.ker x]
    exact map_mono hH
  exact ⟨x,map_injective_of_ker_le f hconj hK himage⟩

end Sporadic.Janko3.SourceRecognition
