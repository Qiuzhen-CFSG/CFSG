module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.Coordinates
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Three-parameter tori in literal orthogonal root normalizers

For a subgroup of the full split isometry group containing the displayed root
and all squared diagonals, any injective homomorphism transports these to a
nontrivial root two-subgroup and a faithful diagonal subgroup of its actual
normalizer. Squaring is injective in characteristic two. Three independent
hyperbolic pairs therefore supply an elementary subgroup of order `p³` for
every prime dividing the multiplicative field order. If `|F| > 2`, one such
prime is odd, contradicting the two-local formulation of quasithinness.

The subgroup membership premises are discharged for the two actual Omega
conventions in `HigherRanks.lean`. This common argument is the Cartan
obstruction of quasithin A.2.18 (printed p.40), with the normalizer and the
rank-three subgroup constructed explicitly, rather than assumed as source data.
-/

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
variable {F : Type u} [Field F] {r : ℕ}


/-- An even finite field of order greater than two has an odd prime dividing its unit order. -/
theorem exists_odd_prime_dvd_card_sub_one [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) : ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card F - 1 := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  refine ⟨p, hp, hp.odd_of_ne_two ?_, hd⟩
  intro he
  subst p
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := hd
  omega

/-- The three root-of-unity parameters really form an elementary group of order `p³`. -/
theorem elementary_torus_parameters [Finite F] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card F - 1) :
    (∀ a : Fin 3 → rootsOfUnity p F, a ^ p = 1) ∧
      Nat.card (Fin 3 → rootsOfUnity p F) = p ^ 3 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hprim : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hprim.card_rootsOfUnity'
  constructor
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p (a i).val).mp (a i).property)
  · rw [Nat.card_fun, hc, Nat.card_fin]

section Local
variable (S : Subgroup (O r F))
variable {G : Type*} [Group G]
variable (π : S →* G) {i j : Fin r} (hij : i ≠ j)
variable (hroot : ∀ a : F, root hij a ∈ S)
variable (hdiag : ∀ d : Fin r → Fˣ, diagonal (d ^ 2) ∈ S)

/-- The root in a chosen genuine subgroup of the full isometry group. -/
def restrictedRootHom : Multiplicative F →* S :=
  (rootHom hij).codRestrict S (fun a => hroot a.toAdd)

/-- Squared diagonal parameters in a subgroup with proved torus membership. -/
def squareDiagonalHom : (Fin r → Fˣ) →* S where
  toFun d := ⟨diagonal (d ^ 2), hdiag d⟩
  map_one' := by
    apply Subtype.ext
    change diagonalHom ((1 : Fin r → Fˣ) ^ 2) = 1
    rw [one_pow, map_one]
  map_mul' a b := by
    apply Subtype.ext
    change diagonalHom ((a*b)^2) = diagonalHom (a^2) * diagonalHom (b^2)
    rw [mul_pow, map_mul]

def liftedRootHom : Multiplicative F →* G := π.comp (restrictedRootHom S hij hroot)

def liftedRootSubgroup : Subgroup G := (liftedRootHom S π hij hroot).range

abbrev liftedRootNormalizer : Subgroup G :=
  Subgroup.normalizer (liftedRootSubgroup S π hij hroot : Set G)

theorem liftedRootHom_injective (hπ : Function.Injective π) :
    Function.Injective (liftedRootHom S π hij hroot) := by
  intro a b hab
  exact rootHom_injective hij (congrArg Subtype.val (hπ hab))

theorem liftedRootSubgroup_ne_bot (hπ : Function.Injective π) :
    liftedRootSubgroup S π hij hroot ≠ ⊥ := by
  intro he
  have h : liftedRootHom S π hij hroot (Multiplicative.ofAdd 1) = 1 := by
    have hm : liftedRootHom S π hij hroot (Multiplicative.ofAdd 1) ∈
        liftedRootSubgroup S π hij hroot := ⟨_, rfl⟩
    simpa [he] using hm
  have hz := liftedRootHom_injective S π hij hroot hπ (h.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd hz)

theorem liftedRootSubgroup_isTwoGroup [CharP F 2] :
    IsPGroup 2 (liftedRootSubgroup S π hij hroot) := by
  have h : IsPGroup 2 (Multiplicative F) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
  exact h.of_surjective (liftedRootHom S π hij hroot).rangeRestrict
    (liftedRootHom S π hij hroot).rangeRestrict_surjective

theorem liftedRootNormalizer_isTwoLocal [CharP F 2] (hπ : Function.Injective π) :
    IsTwoLocal ((liftedRootNormalizer S π hij hroot)) :=
  ⟨liftedRootSubgroup S π hij hroot, liftedRootSubgroup_ne_bot S π hij hroot hπ,
    liftedRootSubgroup_isTwoGroup S π hij hroot, rfl⟩

theorem squareDiagonal_conj_root (d : Fin r → Fˣ) (a : Multiplicative F) :
    squareDiagonalHom S hdiag d * restrictedRootHom S hij hroot a *
      (squareDiagonalHom S hdiag d)⁻¹ = restrictedRootHom S hij hroot
        (Multiplicative.ofAdd (((d i ^ 2 : Fˣ) : F) * a.toAdd * ((d j ^ 2)⁻¹ : Fˣ))) := by
  apply Subtype.ext
  exact diagonal_conj_root (d ^ 2) hij a.toAdd

theorem squareDiagonal_mem_normalizer (d : Fin r → Fˣ) :
    π (squareDiagonalHom S hdiag d) ∈ (liftedRootNormalizer S π hij hroot) := by
  have hf (d : Fin r → Fˣ) (g : G) (hg : g ∈ liftedRootSubgroup S π hij hroot) :
      π (squareDiagonalHom S hdiag d) * g * (π (squareDiagonalHom S hdiag d))⁻¹ ∈
        liftedRootSubgroup S π hij hroot := by
    obtain ⟨a, rfl⟩ := hg
    have he := congrArg π (squareDiagonal_conj_root S hij hroot hdiag d a)
    simp only [map_mul, map_inv] at he
    change π (squareDiagonalHom S hdiag d) * π (restrictedRootHom S hij hroot a) * _ ∈ _
    rw [he]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hf d g, fun hg => ?_⟩
  simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
    mul_one] using hf d⁻¹ _ hg

/-- All squared diagonal parameters, with codomain the literal root normalizer. -/
def normalizerDiagonalHom : (Fin r → Fˣ) →*
    (liftedRootNormalizer S π hij hroot) :=
  (π.comp (squareDiagonalHom S hdiag)).codRestrict _
    (squareDiagonal_mem_normalizer S π hij hroot hdiag)

theorem normalizerDiagonalHom_injective [CharP F 2] (hπ : Function.Injective π) :
    Function.Injective (normalizerDiagonalHom S π hij hroot hdiag) := by
  intro a b hab
  have he : a ^ 2 = b ^ 2 := diagonalHom_injective
    (congrArg Subtype.val (hπ (congrArg Subtype.val hab)))
  funext i
  apply Units.ext
  apply CharTwo.sq_injective
  exact congrArg (fun d : Fin r → Fˣ => (d i : F)) he

/-- Extend the three free parameters by identity on the other hyperbolic pairs. -/
def torusEntriesHom (C : Subgroup Fˣ) : (Fin 3 → C) →* (Fin r → Fˣ) where
  toFun a i := if h : i.val < 3 then (a ⟨i.val, h⟩).val else 1
  map_one' := by funext i; dsimp; split_ifs <;> rfl
  map_mul' a b := by funext i; dsimp; split_ifs <;> simp

theorem torusEntriesHom_injective (hr : 3 ≤ r) (C : Subgroup Fˣ) :
    Function.Injective (torusEntriesHom (r := r) C) := by
  intro a b hab
  funext i
  apply Subtype.ext
  have he := congrFun hab (Fin.castLE hr i)
  simpa [torusEntriesHom, i.isLt] using he

/-- The three-parameter torus lies in the actual normalizer of the root image. -/
def torusNormalizerHom (C : Subgroup Fˣ) : (Fin 3 → C) →*
    (liftedRootNormalizer S π hij hroot) :=
  (normalizerDiagonalHom S π hij hroot hdiag).comp (torusEntriesHom C)

theorem torusNormalizerHom_injective [CharP F 2] (hr : 3 ≤ r)
    (hπ : Function.Injective π) (C : Subgroup Fˣ) :
    Function.Injective (torusNormalizerHom S π hij hroot hdiag C) :=
  (normalizerDiagonalHom_injective S π hij hroot hdiag hπ).comp
    (torusEntriesHom_injective hr C)

include hdiag in
theorem primeRank_liftedRootNormalizer_ge_three [Finite F] [CharP F 2] [Finite G]
    (hr : 3 ≤ r) (hπ : Function.Injective π) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card F - 1) :
    3 ≤ primeRank p (liftedRootNormalizer S π hij hroot) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpow, hcard⟩ := elementary_torus_parameters (F := F) hp hd
  exact primeRank_ge_of_elementary_embedding hpow hcard
    (torusNormalizerHom S π hij hroot hdiag (rootsOfUnity p F))
    (torusNormalizerHom_injective S π hij hroot hdiag hr hπ _)


include hdiag in
/-- An actual elementary odd-prime rank-three embedding in the displayed root normalizer. -/
theorem liftedRootNormalizer_witness [Finite F] [CharP F 2]
    (hr : 3 ≤ r) (hπ : Function.Injective π) (hq : 2 < Nat.card F) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card F - 1 ∧
      ∃ f : (Fin 3 → rootsOfUnity p F) →* liftedRootNormalizer S π hij hroot,
        Function.Injective f ∧ (∀ a : Fin 3 → rootsOfUnity p F, a ^ p = 1) ∧
          Nat.card (Fin 3 → rootsOfUnity p F) = p ^ 3 := by
  obtain ⟨p, hp, ho, hd⟩ := exists_odd_prime_dvd_card_sub_one hq
  exact ⟨p, hp, ho, hd, torusNormalizerHom S π hij hroot hdiag (rootsOfUnity p F),
    torusNormalizerHom_injective S π hij hroot hdiag hr hπ _, elementary_torus_parameters hp hd⟩

include hij hroot hdiag in
/-- The common local contradiction, with all subgroup membership premises explicit. -/
theorem not_quasithin_of_coordinates [Finite F] [CharP F 2] [Finite G]
    (hr : 3 ≤ r) (hπ : Function.Injective π) (hq : 2 < Nat.card F) :
    ¬ IsQuasithin G := by
  intro hG
  obtain ⟨p, hp, ho, hd⟩ := exists_odd_prime_dvd_card_sub_one hq
  have hl := primeRank_liftedRootNormalizer_ge_three S π hij hroot hdiag hr hπ hp hd
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (liftedRootNormalizer_isTwoLocal S π hij hroot hπ) p hp ho
  omega
end Local

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
