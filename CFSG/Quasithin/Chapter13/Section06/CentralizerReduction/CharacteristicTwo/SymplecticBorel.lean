module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport

/-!
# The terminal symplectic Borel obstruction in 13.6.6

The terminal theorem uses the actual component action, its unchanged
centralizer kernel, the specified Sylow normalizer, and B_C = O²(C_B(V)).
An index-three centralizer and an ambient conjugator fixing B_C/O₂(B_C)
cannot coexist with its inversion of a cubic B/O₂(B) image. The proof uses
the full rank-two torus and handles every field degree greater than one.

The local configuration still has to construct the index-three identity
and this conjugator after the Thompson/Baumann normalizer argument. These
are explicit premises below; this module does not claim the completed
13.6.6 symplectic exclusion until those premises have been discharged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed pp.927–928 (PDF pp.944–945).
-/

public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open ActorReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2] [Finite H]
variable (K : Subgroup H) (e : K ≃* Sp F)

omit [CharP F 2] in
/-- The source index-three step implies both the residual index and B_C ≠ 1. -/
theorem residual_index_three_and_nontrivial {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (S : Sylow 2 (Sp F)) (V : Subgroup H)
    (hi : (centralizerInBorel K e S V ⊔ pCore 2 (localBorel K e S)).index = 3) :
    (centralizingResidual K e S V ⊔ pCore 2 (localBorel K e S)).index = 3 ∧
      centralizingResidual K e S V ≠ ⊥ := by
  have hr := (residual_index K e hF hn.le S V).trans hi
  exact ⟨hr, residual_ne_bot K e hF hn S V hr⟩

/-- The terminal contradiction once the local index and actual inverter are constructed.
The actor can have any two-power order and its action on K can have a kernel. -/
theorem no_inverter_of_centralizer_index {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hA : IsPGroup 2 A)
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (V : Subgroup H) (x : A)
    (hindex : (centralizerInBorel K e S V ⊔ pCore 2 (localBorel K e S)).index = 3)
    (hfix : ∀ c ∈ centralizingResidual K e S V,
      (borelMap K e S c)⁻¹ * (x : normalizer (K : Set H)) *
        borelMap K e S c * (x : normalizer (K : Set H))⁻¹ ∈
        ((centralizingResidual K e S V).pCoreIn 2).map (borelMap K e S))
    (b : localBorel K e S)
    (horder : orderOf (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b) = 3)
    (hinv : QuotientGroup.mk' (pCore 2 (localBorel K e S))
        (borelActor K e hF hn.le S A hS x b) =
      (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b)⁻¹) : False := by
  let f := (alignActorHom hF hn.le S).comp (actors K e S A hS)
  have hp : IsPGroup 2 (zpowers (f x)) := by
    have ht := (hA.to_subgroup (zpowers x)).map f
    rw [MonoidHom.map_zpowers] at ht
    exact ht
  apply CubicInverter.no_cubic_inverter hn hF (f x) hp
    (characters K e hF hn.le S) (characters_surjective K e hF hn.le S)
    (borelActor K e hF hn.le S A hS x)
    (characters_actor K e hF hn.le S A hS x)
    (centralizingResidual K e S V) (b := b)
  · rw [characters_ker]
    exact (residual_index K e hF hn.le S V).trans hindex
  · intro c hc
    apply (mem_map_iff_mem (borelMap_injective K e S)).mp
    have h := hfix c hc
    convert h using 1
    rw [map_mul, map_inv]
    change (borelMap K e S c)⁻¹ *
      ((borelActor K e hF hn.le S A hS x c : K) : H) = _
    rw [borelActor_apply]
    change _ * ((x : normalizer (K : Set H)) * borelMap K e S c *
      (x : normalizer (K : Set H))⁻¹) = _
    simp only [mul_assoc]
  · change orderOf (quotientEquiv K e hF hn.le S
      (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b)) = 3
    rwa [MulEquiv.orderOf_eq]
  · change quotientEquiv K e hF hn.le S
      (QuotientGroup.mk' (pCore 2 (localBorel K e S))
        (borelActor K e hF hn.le S A hS x b)) = _
    rw [hinv, map_inv]
    rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
