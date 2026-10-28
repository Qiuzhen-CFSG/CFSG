module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation

/-!
# Transporting the local cubic quotient into the Borel quotient

The character kernel in every subgroup of the actual Borel is its
two-core. Thus an embedding D → B induces a faithful map
D/O₂(D) → B/O₂(B). Cauchy's theorem supplies an element of order
three when the first quotient has order three, and equivariance
transports inversion by the same actor. `borelLift` uses the literal
ambient inclusion, so it applies to Lᵥ once its Borel placement is given.

The local construction of that actor remains a separate obligation.
Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
variable {H F D : Type*} [Group H] [Field F] [Finite F] [Group D]
variable (K : Subgroup H) (e : K ≃* Sp F)

/-- Every faithful subgroup embedding in B retains precisely its own two-core. -/
theorem core_comap {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (f : D →* localBorel K e S) (hf : Function.Injective f) :
    (pCore 2 (localBorel K e S)).comap f = pCore 2 D := by
  let q := (characters K e hF hn S).comp f
  have hk : q.ker = (pCore 2 (localBorel K e S)).comap f := by
    rw [← characters_ker K e hF hn S, MonoidHom.comap_ker]
  have hp : IsPGroup 2 q.ker := by
    let i : q.ker →* pCore 2 (localBorel K e S) := {
      toFun x := ⟨f x, show x.val ∈ (pCore 2 (localBorel K e S)).comap f from
        hk ▸ x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' _ _ := Subtype.ext (f.map_mul _ _) }
    exact (pCore_isPGroup (p := 2) (G := localBorel K e S)).of_injective i
      (fun x y h => Subtype.ext (hf (congrArg Subtype.val h)))
  rw [← hk]
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hp⟩
  have he : (pCore 2 D).map q = ⊥ := by
    apply card_eq_one.mp
    exact (pCore_isPGroup.map q : IsPGroup 2 ((pCore 2 D).map q)).card_eq_or_dvd.resolve_right
      (fun h => (Nat.prime_two.coprime_iff_not_dvd.mp (torus_odd hF))
        (h.trans (card_subgroup_dvd_card _)))
  intro d hd
  exact he.le (mem_map_of_mem q hd)

/-- The literal inclusion D/O₂(D) → B/O₂(B). -/
noncomputable def quotientEmbedding {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (f : D →* localBorel K e S) (hf : Function.Injective f) :
    D ⧸ pCore 2 D →* localBorel K e S ⧸ pCore 2 (localBorel K e S) :=
  QuotientGroup.map _ _ f (core_comap K e hF hn S f hf).ge

theorem quotientEmbedding_injective {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (f : D →* localBorel K e S) (hf : Function.Injective f) :
    Function.Injective (quotientEmbedding K e hF hn S f hf) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [quotientEmbedding, QuotientGroup.ker_map, core_comap K e hF hn S f hf,
    QuotientGroup.map_mk'_self]

/-- An actual cubic local quotient supplies an element of order three in
B/O₂(B), inverted by the same Borel actor. -/
theorem exists_cubic_image [Finite D] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (f : D →* localBorel K e S) (hf : Function.Injective f)
    (hD : Nat.card (D ⧸ pCore 2 D) = 3)
    (a : MulAut D) (b : MulAut (localBorel K e S))
    (hcompat : ∀ d, f (a d) = b (f d))
    (hinv : ∀ d, QuotientGroup.mk' (pCore 2 D) (a d) =
      (QuotientGroup.mk' (pCore 2 D) d)⁻¹) :
    ∃ c : localBorel K e S,
      orderOf (QuotientGroup.mk' (pCore 2 (localBorel K e S)) c) = 3 ∧
      QuotientGroup.mk' (pCore 2 (localBorel K e S)) (b c) =
        (QuotientGroup.mk' (pCore 2 (localBorel K e S)) c)⁻¹ := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := D ⧸ pCore 2 D) 3
    (by rw [hD])
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) y
  let j := quotientEmbedding K e hF hn S f hf
  refine ⟨f d, (orderOf_injective j (quotientEmbedding_injective K e hF hn S f hf) _).trans hy, ?_⟩
  have he := congrArg j (hinv d)
  rw [map_inv] at he
  change QuotientGroup.mk' (pCore 2 (localBorel K e S)) (f (a d)) = _ at he
  rwa [hcompat d] at he

/-- Lift an ambient subgroup of B along the specified injective Borel map. -/
noncomputable def borelLift (S : Sylow 2 (Sp F)) (D : Subgroup H) (hD : D ≤ borelIn K e S) :
    D →* localBorel K e S :=
  (MonoidHom.ofInjective (borelMap_injective K e S)).symm.toMonoidHom.comp (inclusion hD)

omit [Finite F] in
theorem borelLift_apply (S : Sylow 2 (Sp F)) (D : Subgroup H) (hD : D ≤ borelIn K e S)
    (d : D) : borelMap K e S (borelLift K e S D hD d) = d :=
  congrArg Subtype.val ((MonoidHom.ofInjective (borelMap_injective K e S)).apply_symm_apply
    (inclusion hD d))

omit [Finite F] in
theorem borelLift_injective (S : Sylow 2 (Sp F)) (D : Subgroup H) (hD : D ≤ borelIn K e S) :
    Function.Injective (borelLift K e S D hD) :=
  (MonoidHom.ofInjective (borelMap_injective K e S)).symm.injective.comp (inclusion_injective hD)

/-- Apply the quotient transport to the literal Lᵥ inside this Borel.
This is a transport lemma: the local Sylow construction must still supply
`x` and its action on the Lᵥ-quotient. -/
theorem exists_local_cubic_image [Finite H] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (L : Subgroup H) (v : H) (hD : Lv L v ≤ borelIn K e S)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (x : A) (hxD : ((x : normalizer (K : Set H)) : H) ∈ normalizer (Lv L v : Set H))
    (hinv : ∀ d : Lv L v,
      QuotientGroup.mk' (pCore 2 (Lv L v))
        ((Lv L v).normalizerMonoidHom ⟨((x : normalizer (K : Set H)) : H), hxD⟩ d) =
      (QuotientGroup.mk' (pCore 2 (Lv L v)) d)⁻¹) :
    ∃ b : localBorel K e S,
      orderOf (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b) = 3 ∧
      QuotientGroup.mk' (pCore 2 (localBorel K e S))
        (borelActor K e hF hn S A hS x b) =
      (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b)⁻¹ := by
  apply exists_cubic_image K e hF hn S
    (borelLift K e S (Lv L v) hD) (borelLift_injective K e S (Lv L v) hD) hcard
    ((Lv L v).normalizerMonoidHom ⟨((x : normalizer (K : Set H)) : H), hxD⟩)
    (borelActor K e hF hn S A hS x) _ hinv
  intro d
  apply borelMap_injective K e S
  rw [borelLift_apply]
  change _ = ((borelActor K e hF hn S A hS x (borelLift K e S (Lv L v) hD d) : K) : H)
  rw [borelActor_apply]
  change _ = ((x : normalizer (K : Set H)) : H) *
    borelMap K e S (borelLift K e S (Lv L v) hD d) *
      ((x : normalizer (K : Set H)) : H)⁻¹
  rw [borelLift_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
