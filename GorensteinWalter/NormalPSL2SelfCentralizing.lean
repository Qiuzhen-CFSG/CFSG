module
public import GorensteinWalter.NormalPSL2PrescribedField
public import GorensteinWalter.PGL2ThreeAutomorphism
public import GorensteinWalter.PSL2ThreeNormalExtension
public import Mathlib.Algebra.Group.Shrink

/-!
# Semilinear realization of a prescribed self-centralizing PSL2 core

A finite group with a specified normal PSL2(K) subgroup and trivial core
centralizer embeds faithfully in PGammaL2(K), with the specified subgroup
mapped by the canonical PSL2 inclusion. No Sylow or field-image parity
hypothesis is imposed. The ambient group and field have independent universes.

In field order three, the actual compatible PGL2-to-AutPSL2 equivalence
and the shared linear realization give the map. Above three, the proved
semilinear automorphism theorem realizes the faithful normal-core conjugation
action. A final Shrink transport changes only the ambient universe, using
the actual comap core equivalence to preserve the pointwise equation.

This isolates the automorphism-theoretic part of the semidihedral normal-core
step in Alperin--Brauer--Gorenstein II.3, Proposition 4, article page 29;
local Sylow geometry separately proves the required centralizer triviality.
-/

namespace GorensteinWalter
universe u v

private theorem same_universe
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧ ∀ n : N,
      f n = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)) := by
  by_cases hthree : Nat.card K = 3
  · obtain ⟨eAut, heAut⟩ := exists_pgl2_equiv_aut_psl2_of_card_three K hthree
    obtain ⟨f, hf, hn, _⟩ := exists_normal_psl2_linear_embedding_of_aut_equiv
      N K e hC eAut heAut
    exact ⟨f, hf, hn⟩
  · have hlarge : 3 < Nat.card K := lt_of_le_of_ne
      (odd_prime_power_three_le _ hK) (Ne.symm hthree)
    obtain ⟨p, d, hp, hpodd, hd, hKd⟩ := hK
    have hK : IsOddPrimePower (Nat.card K) := ⟨p, d, hp, hpodd, hd, hKd⟩
    let : Fact p.Prime := ⟨hp⟩
    have hsurj := pGammaL2ToMulAutPSL2_surjective K hKd hK hlarge
    exact ⟨normalPSL2ToPGammaL2 N K hK hlarge e hsurj,
      normalPSL2ToPGammaL2_injective N K hK hlarge e hC hsurj,
      normalPSL2ToPGammaL2_apply_subtype N K hK hlarge e hsurj⟩

public theorem exists_normal_psl2_semilinear_embedding_of_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (K : Type v) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (eN : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧ ∀ n : N,
      f n = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (eN n)) := by
  classical
  let eG : Shrink.{v} G ≃* G := Shrink.mulEquiv
  let : Finite (Shrink.{v} G) := Finite.of_injective eG eG.injective
  let M := N.comap eG.toMonoidHom
  let eM : M ≃* N := MulEquiv.ofBijective (eG.toMonoidHom.subgroupComap N)
    ⟨fun _ _ h => Subtype.ext (eG.injective (congrArg Subtype.val h)),
      eG.toMonoidHom.subgroupComap_surjective_of_surjective N eG.surjective⟩
  have hMC : Subgroup.centralizer (M : Set (Shrink.{v} G)) = ⊥ := by
    apply le_bot_iff.mp
    intro g hg
    apply eG.injective
    rw [map_one]
    apply Subgroup.mem_bot.mp
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have hnm : eG.symm n ∈ M := by
      change eG (eG.symm n) ∈ N
      rw [eG.apply_symm_apply]
      exact hn
    have hh := Subgroup.mem_centralizer_iff.mp hg (eG.symm n) hnm
    simpa only [map_mul, eG.apply_symm_apply] using congrArg eG hh
  obtain ⟨f, hf, he⟩ := same_universe M K hK (eM.trans eN) hMC
  refine ⟨f.comp eG.symm.toMonoidHom, hf.comp eG.symm.injective, fun n => ?_⟩
  have hn : eG.symm n ∈ M := by
    change eG (eG.symm n) ∈ N
    simp
  change f (eG.symm n) = _
  rw [he ⟨eG.symm n, hn⟩]
  have hval : eM ⟨eG.symm n, hn⟩ = n := Subtype.ext (eG.apply_symm_apply n)
  simp only [MulEquiv.trans_apply, hval]

end GorensteinWalter
