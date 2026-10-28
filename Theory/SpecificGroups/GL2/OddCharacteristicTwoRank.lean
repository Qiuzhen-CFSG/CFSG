module
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.GL2.OddPrimeRank
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates

/-!
# Two-rank of automorphisms of an odd prime plane

A faithful elementary binary subgroup of GL₂ in odd characteristic has at
most two character weights after extending the scalars to an algebraic
closure. Evaluation on those weights embeds it into at most two copies of
the two roots of unity. Coordinates give the same bound for automorphisms
of an elementary abelian group of order p², for odd p.

Source application: Aschbacher–Smith 15.1.7(7), used in15.1.13, p.1091.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Matrix.GeneralLinearGroup

theorem twoRank_le_two_of_two_ne_zero
    (F : Type*) [Field F] [Finite F] (hF : (2 : F) ≠ 0) :
    primeRank 2 (GL (Fin 2) F) ≤ 2 := by
  classical
  apply (primeRank_le_iff_elementary_card_le (GL (Fin 2) F)).mpr
  intro A hA
  let := hA
  let E := AlgebraicClosure F
  let f : GL (Fin 2) F →* GL (Fin 2) E := map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 2) E => c i j) h
  let sigma : Representation E A (Fin 2 → E) :=
    (Representation.generalLinearNatural 2).comp (f.comp A.subtype)
  have hsigma : Function.Injective sigma :=
    (Representation.generalLinearNatural_injective 2).comp (hf.comp A.subtype_injective)
  have horderF : (Nat.card A : F) ≠ 0 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hF
  have horder : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horderF
    apply (algebraMap F E).injective
    simpa using h
  obtain ⟨hfinite, hweights⟩ := sigma.characterWeight_card_le horder
  let := hfinite
  have hweights2 : Nat.card sigma.CharacterWeight ≤ 2 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hweights
  let evaluate : A → (sigma.CharacterWeight → rootsOfUnity 2 E) := fun a chi =>
    ⟨chi.val a, by
      rw [mem_rootsOfUnity, ← map_pow]
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, map_one]⟩
  have hevaluate : Function.Injective evaluate := by
    intro a b hab
    apply sigma.eq_of_characterWeight_values hsigma horder a b
    intro chi
    exact congrArg Subtype.val (congrFun hab chi)
  calc
    Nat.card A ≤ Nat.card (sigma.CharacterWeight → rootsOfUnity 2 E) :=
      Nat.card_le_card_of_injective evaluate hevaluate
    _ = Nat.card (rootsOfUnity 2 E) ^ Nat.card sigma.CharacterWeight := Nat.card_fun
    _ ≤ 2 ^ Nat.card sigma.CharacterWeight :=
      Nat.pow_le_pow_left (card_rootsOfUnity E 2) _
    _ ≤ 2 ^ 2 := pow_le_pow_right' (by decide) hweights2

end Matrix.GeneralLinearGroup

namespace IsElementaryAbelian

theorem automorphism_twoRank_le_two_of_odd_plane {p : ℕ} [Fact p.Prime]
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hp : p ≠ 2) (hc : Nat.card V = p ^ 2) :
    primeRank 2 (MulAut V) ≤ 2 := by
  obtain ⟨c,e,_⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates hc
  rw [primeRank_equiv 2 e]
  apply Matrix.GeneralLinearGroup.twoRank_le_two_of_two_ne_zero
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  exact hp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (Fact.out : p.Prime).ne_one)
end IsElementaryAbelian
