module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation

/-!
# The actual local Sylow actors

The actor subgroup is the given Tᵥ embedded in N_H(K), with its full
component-centralizer kernel retained. The equality T_K = Tᵥ ∩ K
proves that these actors stabilize the specified model Sylow.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
variable {H F : Type*} [Group H] [Field F] [Finite F]
variable (K : Subgroup H) (e : K ≃* Sp F)

/-- The actual Tᵥ, as an acting subgroup of N_H(K). -/
def localActors (T : Subgroup H) (v : H) : Subgroup (normalizer (K : Set H)) :=
  (Tv T v).subgroupOf (normalizer (K : Set H))

omit [Field F] [Finite F] in
theorem localActors_map (T : Subgroup H) (v : H)
    (hTK : Tv T v ≤ normalizer (K : Set H)) :
    (localActors K T v).map (normalizer (K : Set H)).subtype = Tv T v :=
  map_subgroupOf_eq_of_le hTK

omit [Field F] [Finite F] in
theorem localActors_isPGroup (T : Subgroup H) (v : H) (hT : IsPGroup 2 T) :
    IsPGroup 2 (localActors K T v) := (hT.to_le inf_le_left).comap_subtype

/-- The specified T_K = Tᵥ ∩ K is preserved by the actual Tᵥ actors. -/
theorem localActors_stabilize (S : Sylow 2 (Sp F)) (T : Subgroup H) (v : H)
    (hTK : Tv T v ≤ normalizer (K : Set H))
    (hSylow : (localSylow K e S : Subgroup K).map K.subtype = Tv T v ⊓ K) :
    ∀ x ∈ localActors K T v,
      (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S := by
  let f : Sp F →* H := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hSf : (S : Subgroup (Sp F)).map f = Tv T v ⊓ K := by
    exact (map_map _ _ _).symm.trans hSylow
  intro x hx
  have hxT : (x : H) ∈ Tv T v := hx
  have hxN : (x : H) ∈ normalizer ((Tv T v ⊓ K : Subgroup H) : Set H) :=
    inf_normalizer_le_normalizer_inf ⟨(Tv T v).le_normalizer hxT, hTK hxT⟩
  apply map_injective hf
  rw [map_map]
  have he : f.comp (modelAction K e x).toMonoidHom = (MulAut.conj (x : H)).toMonoidHom.comp f := by
    ext y
    change ((e.symm (e (K.normalizerMonoidHom x (e.symm y)))) : H) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he, ← map_map, hSf]
  exact mem_normalizer_iff_map_conj_eq.mp hxN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
