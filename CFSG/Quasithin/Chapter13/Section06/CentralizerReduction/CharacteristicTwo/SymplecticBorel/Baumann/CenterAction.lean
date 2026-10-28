module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction

/-!
# The ambient kernel on the symplectic Sylow center

Transport the intrinsic center-action theorem through the actual modelAction
of N_H(K). The specified Sylow equality identifies the model center with
Ω₁(Z(R ∩ K)). An actor fixing it is conjugation by a member of R ∩ K;
dividing by that member lies in the literal centralizer kernel C_H(K).
Both factors of the resulting product retain their ambient embeddings.

This discharges the center-action premise of the symplectic Baumann argument,
independently of maximum-elementary placement. In fact neither finiteness of H
nor a two-group hypothesis on R is needed once its intersection with K is the
specified Sylow. No Thompson or Baumann decomposition is used.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944).
-/

public section
open Subgroup Stellmacher
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F]
variable (K : Subgroup H) (e : K ≃* Sp F)

private theorem modelAction_embedding (x : normalizer (K : Set H)) :
    (K.subtype.comp e.symm.toMonoidHom).comp (modelAction K e x).toMonoidHom =
      (MulAut.conj (x : H)).toMonoidHom.comp (K.subtype.comp e.symm.toMonoidHom) := by
  ext y
  change ((e.symm (e (K.normalizerMonoidHom x (e.symm y)))) : H) = _
  rw [e.symm_apply_apply]
  rfl

private theorem modelAction_inner (g : Sp F) :
    modelAction K e (inclusion K.le_normalizer (e.symm g)) = MulAut.conj g := by
  apply MulEquiv.ext
  intro y
  change e (e.symm g * e.symm y * (e.symm g)⁻¹) = _
  simp only [map_mul, map_inv, e.apply_symm_apply, MulAut.conj_apply]

variable [Finite F] [CharP F 2]

/-- The kernel on Ω₁(Z(R ∩ K)) lies in the literal product of the component
Sylow and its centralizer in R. In particular this applies to the two-group R
in the Baumann decomposition; no order hypothesis on R is needed. -/
theorem centralizer_omegaCenter_le_product {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (R : Subgroup H) (hN : R ≤ normalizer (K : Set H))
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K) :
    R ⊓ centralizer (omegaOneCenterAmbient (R ⊓ K) : Set H) ≤
      (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) := by
  let f : Sp F →* H := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hSf : (S : Subgroup (Sp F)).map f = R ⊓ K :=
    (map_map _ _ _).symm.trans hSyl
  have hZ := map_subgroup_center_eq f hf (S : Subgroup (Sp F))
  rw [hSf] at hZ
  have hOmega : omegaOneCenterAmbient (R ⊓ K) =
      (center ↥(R ⊓ K)).map (R ⊓ K).subtype := by
    rw [← hSyl]
    exact localSylow_omegaCenter K e hF hn.le S
  rintro x ⟨hxR, hxZ⟩
  let xN : normalizer (K : Set H) := ⟨x, hN hxR⟩
  let a := modelAction K e xN
  have hSN : x ∈ normalizer ((R ⊓ K : Subgroup H) : Set H) :=
    inf_normalizer_le_normalizer_inf ⟨R.le_normalizer hxR, hN hxR⟩
  have hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S := by
    apply map_injective hf
    rw [map_map, modelAction_embedding, ← map_map, hSf]
    exact mem_normalizer_iff_map_conj_eq.mp hSN
  have ha : ∀ z ∈ (center S).map (S : Subgroup (Sp F)).subtype, a z = z := by
    intro z hz
    have hfz : f z ∈ omegaOneCenterAmbient (R ⊓ K) := by
      rw [hOmega]
      exact hZ.le (mem_map_of_mem f hz)
    have hc : x * f z * x⁻¹ = f z :=
      mul_inv_eq_iff_eq_mul.mpr (hxZ (f z) hfz).symm
    apply hf
    have he := DFunLike.congr_fun (modelAction_embedding K e xN) z
    exact he.trans hc
  obtain ⟨g, hg, hag⟩ := CentralRootGeometry.CenterAction.aut_fixing_sylow_center_inner
    hF hn S a hS ha
  have hgRK : f g ∈ R ⊓ K := hSf.le (mem_map_of_mem f hg)
  let gN : normalizer (K : Set H) := inclusion K.le_normalizer (e.symm g)
  have hc : ((gN⁻¹ * xN : normalizer (K : Set H)) : H) ∈ centralizer (K : Set H) := by
    change gN⁻¹ * xN ∈ NormalizerAction.C K
    rw [← modelAction_ker K e, MonoidHom.mem_ker, map_mul, map_inv]
    change (modelAction K e (inclusion K.le_normalizer (e.symm g)))⁻¹ * a = 1
    rw [modelAction_inner, hag, inv_mul_cancel]
  have hy : (f g)⁻¹ * x ∈ R ⊓ centralizer (K : Set H) :=
    ⟨R.mul_mem (R.inv_mem hgRK.1) hxR, hc⟩
  have hm := ((R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H))).mul_mem
    (mem_sup_left hgRK) (mem_sup_right hy)
  simpa only [mul_inv_cancel_left] using hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
