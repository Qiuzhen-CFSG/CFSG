module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import Theory.GroupTheory.TwoByThreeDisplacement
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Centralization of the centralizer residual quotient

An actor in L normalizing B and V has its displacement on
B_C = O²(C_B(V)) in both B_C and C_L(V). The earlier local module
kernel C_L(V) ≤ O₂(L), together with B ≤ N_H(L), puts the displacement
in O₂(B_C). All cores are relative to their specified subgroup.

The resulting theorem has exactly the ambient membership conclusion
consumed by `SymplecticBorel.no_inverter_of_centralizer_index`.
It does not construct the required actor or assume a faithful K-action.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open ActorReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
variable {H F : Type*} [Group H] [Field F] [Finite H] [Finite F]
variable (K : Subgroup H) (e : K ≃* Sp F)

omit [Finite H] in
/-- The transported Borel automorphism is actual ambient normalization. -/
theorem actor_normalizes_borel {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (x : A) : ((x : normalizer (K : Set H)) : H) ∈ normalizer (borelIn K e S : Set H) := by
  have hconj (y : A) {b : H} (hb : b ∈ borelIn K e S) :
      (y : normalizer (K : Set H)) * b * (y : normalizer (K : Set H))⁻¹ ∈ borelIn K e S := by
    obtain ⟨b, rfl⟩ := hb
    refine ⟨borelActor K e hF hn S A hS y b, ?_⟩
    exact congrArg (fun b : K => (b : H)) (borelActor_apply K e hF hn S A hS y b)
  apply mem_normalizer_iff.mpr
  intro b
  constructor
  · exact hconj x
  · intro hb
    simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using hconj x⁻¹ hb

/-- Normalizing B and V normalizes its literal centralizing residual. -/
theorem actor_normalizes_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (V : Subgroup H) (x : A)
    (hxV : ((x : normalizer (K : Set H)) : H) ∈ normalizer (V : Set H)) :
    ((x : normalizer (K : Set H)) : H) ∈ normalizer
      ((centralizingResidual K e S V).map (borelMap K e S) : Set H) := by
  rw [centralizingResidual_map]
  apply normalizer_le_normalizer_characteristic_image _ (pResidual 2 _)
  exact inf_normalizer_le_normalizer_inf
    ⟨actor_normalizes_borel K e hF hn S A hS x,
      normalizer_le_normalizer_centralizer V hxV⟩

/-- The source centralization follows from the earlier local kernel and
normalizer conditions, for every actual actor in L. -/
theorem residual_displacement {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (L V : Subgroup H) (x : A)
    (hBL : borelIn K e S ≤ normalizer (L : Set H))
    (hLV : L ≤ normalizer (V : Set H))
    (hkernel : L ⊓ centralizer (V : Set H) ≤ L.pCoreIn 2)
    (hxL : ((x : normalizer (K : Set H)) : H) ∈ L) :
    ∀ c ∈ centralizingResidual K e S V,
      (borelMap K e S c)⁻¹ * ((x : normalizer (K : Set H)) : H) *
        borelMap K e S c * ((x : normalizer (K : Set H)) : H)⁻¹ ∈
        ((centralizingResidual K e S V).pCoreIn 2).map (borelMap K e S) := by
  let C := (centralizingResidual K e S V).map (borelMap K e S)
  have hCB : C ≤ borelIn K e S := map_le_range _ _
  have hCV : C ≤ centralizer (V : Set H) := by
    apply le_trans (map_mono (map_subtype_le (pResidual 2 (centralizerInBorel K e S V))))
    rw [centralizerInBorel_map]
    exact inf_le_right
  have hxC : ((x : normalizer (K : Set H)) : H) ∈ normalizer (C : Set H) :=
    actor_normalizes_residual K e hF hn S A hS V x (hLV hxL)
  intro c hc
  let b := borelMap K e S c
  have hbC : b ∈ C := mem_map_of_mem _ hc
  have hbV := hCV hbC
  have hdC : b⁻¹ * ((x : normalizer (K : Set H)) : H) * b *
      ((x : normalizer (K : Set H)) : H)⁻¹ ∈ C := by
    simpa only [mul_assoc] using C.mul_mem (C.inv_mem hbC)
      ((mem_normalizer_iff.mp hxC b).mp hbC)
  have hdL : b⁻¹ * ((x : normalizer (K : Set H)) : H) * b *
      ((x : normalizer (K : Set H)) : H)⁻¹ ∈ L :=
    L.mul_mem ((mem_normalizer_iff''.mp (hBL (hCB hbC)) _).mp hxL) (L.inv_mem hxL)
  have hdV : b⁻¹ * ((x : normalizer (K : Set H)) : H) * b *
      ((x : normalizer (K : Set H)) : H)⁻¹ ∈ centralizer (V : Set H) := by
    have hn := normalizer_le_normalizer_centralizer V (hLV hxL)
    simpa only [mul_assoc] using (centralizer (V : Set H)).mul_mem
      ((centralizer (V : Set H)).inv_mem hbV) ((mem_normalizer_iff.mp hn b).mp hbV)
  have hd := pCoreIn_inf_le_of_normalizes (hCB.trans hBL) ⟨hkernel ⟨hdL, hdV⟩, hdC⟩
  rw [map_pCoreIn_of_injective 2 _ _ (borelMap_injective K e S)]
  exact hd
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
