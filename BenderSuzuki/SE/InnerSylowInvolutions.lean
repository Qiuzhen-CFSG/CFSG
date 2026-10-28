module
public import BenderSuzuki.SE.ModelSylowInvolutions
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Inner involutions in a Bender two-subgroup of automorphisms

For a center-free Bender model, pull an automorphism two-subgroup back along
faithful inner conjugation. Its square-one inner elements commute by the
model Sylow calculation. The ambient automorphism subgroup need not itself
be inner. This supplies the actual paired-cubic application in
Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace BenderSuzuki

/-- Square-one inner elements of a common automorphism two-subgroup commute. -/
theorem IsSimpleBenderGroup.inner_squares_commute_in_twoSubgroup
    {K : Type*} [Group K] [Finite K] (hK : IsSimpleBenderGroup K)
    (hz : center K = ⊥) (P : Subgroup (MulAut K)) (hp : IsPGroup 2 P)
    (a b : MulAut K) (ha : a ∈ P) (hb : b ∈ P)
    (hai : a ∈ (MulAut.conj : K →* MulAut K).range)
    (hbi : b ∈ (MulAut.conj : K →* MulAut K).range)
    (ha2 : a^2=1) (hb2 : b^2=1) : Commute a b := by
  let f : K →* MulAut K := MulAut.conj
  have hf : Function.Injective f := conj_injective_of_center_eq_bot hz
  obtain ⟨u,rfl⟩ := hai
  obtain ⟨v,rfl⟩ := hbi
  exact (hK.squares_commute_in_twoSubgroup (P.comap f)
    (hp.comap_of_injective f hf) u v ha hb
    (hf (by simpa only [map_pow,map_one] using ha2))
    (hf (by simpa only [map_pow,map_one] using hb2))).map f
end BenderSuzuki

