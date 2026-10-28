module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.SplitNormalizer
import Mathlib.Tactic

/-!
# Three coroot parameters obstruct quasithinness

Three chosen simple-coroot coordinates define a homomorphism into the actual
normalizer of any root subgroup. A separation calculation on three root
characters makes that homomorphism injective after the center quotient.
Restricting to p-th roots of unity, for an odd prime dividing |F|-1, gives
an elementary abelian subgroup of rank three in a genuine two-local subgroup.

Pairwise orthogonal simple coroots satisfy the separation criterion in
characteristic two, since Frobenius is injective. The separate F4 application
uses its three-node Cartan matrix instead. This realizes the torus argument
of Aschbacher–Smith A.2.18 (printed p.40) without induction or parabolic theory.
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction
noncomputable section
namespace ExceptionalSplit.TheoremDRootNormalizer
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F] [Finite F] [CharP F 2]

def threeParameters (j : Fin 3 → b.support) : (Fin 3 → Fˣ) →* (b.support → Fˣ) where
  toFun a := integralChevalleySimpleCorootParameter (j 0) (a 0) *
    integralChevalleySimpleCorootParameter (j 1) (a 1) *
    integralChevalleySimpleCorootParameter (j 2) (a 2)
  map_one' := by ext i; simp [integralChevalleySimpleCorootParameter]
  map_mul' a c := by
    have hs (i : b.support) (u v : Fˣ) :
        integralChevalleySimpleCorootParameter i (u * v) =
          integralChevalleySimpleCorootParameter i u *
          integralChevalleySimpleCorootParameter i v := by
      funext k
      dsimp [integralChevalleySimpleCorootParameter]
      split_ifs <;> simp
    change integralChevalleySimpleCorootParameter (j 0) (a 0 * c 0) *
      integralChevalleySimpleCorootParameter (j 1) (a 1 * c 1) *
      integralChevalleySimpleCorootParameter (j 2) (a 2 * c 2) = _
    rw [hs, hs, hs]
    ac_rfl

omit [CharP F 2] in
theorem threeParameters_scale (j : Fin 3 → b.support) (a : Fin 3 → Fˣ) (r : ι) :
    integralChevalleyRootScale (P := P) (threeParameters j a) r =
      a 0 ^ P.pairingIn ℤ r (j 0) * a 1 ^ P.pairingIn ℤ r (j 1) *
        a 2 ^ P.pairingIn ℤ r (j 2) := by
  simp only [threeParameters, MonoidHom.coe_mk, OneHom.coe_mk,
    integralChevalleyRootScale_mul, integralChevalleyRootScale_simpleCorootParameter]

def threeTorusNormalizer (j : Fin 3 → b.support) (r : ι) : (Fin 3 → Fˣ) →*
    Subgroup.normalizer (rootSubgroup (b := b) (F := F) r : Set (Model P b F)) :=
  (torusNormalizer r).comp (threeParameters j)

theorem threeTorusNormalizer_injective (j : Fin 3 → b.support)
    (hsep : ∀ a : Fin 3 → Fˣ,
      (∀ i : Fin 3, a 0 ^ P.pairingIn ℤ (j i) (j 0) *
        a 1 ^ P.pairingIn ℤ (j i) (j 1) * a 2 ^ P.pairingIn ℤ (j i) (j 2) = 1) → a = 1)
    (r : ι) : Function.Injective (threeTorusNormalizer (F := F) j r) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply hsep a
  intro i
  have he : projectiveTorus (P := P) (threeParameters j a) = 1 := congrArg Subtype.val ha
  simpa only [threeParameters_scale] using
    rootScale_eq_one_of_projectiveTorus_eq_one he (j i)

omit [Finite F] in
theorem unit_square_eq_one {u : Fˣ} (h : u ^ 2 = 1) : u = 1 := by
  apply Units.ext
  apply (frobenius_inj F 2)
  change (u : F) ^ 2 = (1 : F) ^ 2
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using congrArg Units.val h

omit [P.IsReduced] [Fintype ι] [DecidableEq ι] [Finite F] in
theorem orthogonal_three_separate (j : Fin 3 → b.support)
    (hj : ∀ i k : Fin 3, P.pairingIn ℤ (j i) (j k) = if i = k then 2 else 0)
    (a : Fin 3 → Fˣ)
    (ha : ∀ i : Fin 3, a 0 ^ P.pairingIn ℤ (j i) (j 0) *
      a 1 ^ P.pairingIn ℤ (j i) (j 1) * a 2 ^ P.pairingIn ℤ (j i) (j 2) = 1) : a = 1 := by
  funext i
  apply unit_square_eq_one
  have he := ha i
  fin_cases i <;> simpa [hj] using he

def torsionCoordinates (p : ℕ) : (Fin 3 → rootsOfUnity p F) →* (Fin 3 → Fˣ) where
  toFun a i := (a i).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem not_quasithin_of_three (hq : 2 < Nat.card F) (j : Fin 3 → b.support)
    (hsep : ∀ a : Fin 3 → Fˣ,
      (∀ i : Fin 3, a 0 ^ P.pairingIn ℤ (j i) (j 0) *
        a 1 ^ P.pairingIn ℤ (j i) (j 1) * a 2 ^ P.pairingIn ℤ (j i) (j 2) = 1) → a = 1) :
    ¬ IsQuasithin (Model P b F) := by
  intro hG
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hd
    omega)
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  have hpow (u : rootsOfUnity p F) : u ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
  have hr : 3 ≤ primeRank p (Subgroup.normalizer
      (rootSubgroup (b := b) (F := F) (j 0) : Set (Model P b F))) := by
    apply primeRank_ge_of_elementary_embedding
      (A := Fin 3 → rootsOfUnity p F)
      (fun a => funext (fun i => hpow (a i)))
      (by rw [Nat.card_fun, hc, Nat.card_fin])
      ((threeTorusNormalizer j (j 0)).comp (torsionCoordinates p))
    apply (threeTorusNormalizer_injective j hsep (j 0)).comp
    intro a c he
    funext i
    exact Subtype.ext (congrFun he i)
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (rootNormalizer_isTwoLocal hq (j 0)) p hp ho
  omega

end ExceptionalSplit.TheoremDRootNormalizer
