module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle
public import Mathlib.Algebra.Module.ZMod
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode

/-!
# The intrinsic core at any native sextet

The original affine coordinate map identifies the intrinsic two-core with
the literal native translations. Its order is 64. This is used for the
original Todd image of the extraspecial plane core in AS91 (6.4), p.602.
The conjugation action is the existing irreducible hexacode action, so the
core is minimal normal in the same stabilizer. This places its canonical
Todd lift inside the original extraspecial core. The imported affine
construction retains its ATLAS source attribution.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport
namespace MathieuCode.J4Fusion

lemma sextet_core_eq_translations (S : Sextet) :
    pCore 2 (sextetStabilizer S) = (nativeTranslation S).range := by
  have hh := (nativeStabilizerEquiv S).symm.toMonoidHom.comap_pCore_of_ker_isPGroup
    (p := 2) (nativeStabilizerEquiv S).symm.surjective
    (IsPGroup.ker_isPGroup_of_injective (nativeStabilizerEquiv S).symm.injective)
  rw [SextetCore.atlas_core_eq_kernel] at hh
  rw [←nativeQuotient_kernel]
  exact hh.symm

lemma sextet_core_card (S : Sextet) : Nat.card (pCore 2 (sextetStabilizer S)) = 64 := by
  rw [sextet_core_eq_translations,nativeTranslation_card]

lemma sextet_core_minimal (S : Sextet) (N : Subgroup (sextetStabilizer S))
    [N.Normal] (hle : N ≤ pCore 2 (sextetStabilizer S)) :
    N = ⊥ ∨ N = pCore 2 (sextetStabilizer S) := by
  rw [sextet_core_eq_translations] at hle ⊢
  let H : AddSubgroup Atlas.Codes.hexacode :=
    { carrier := {v | nativeTranslation S (Multiplicative.ofAdd v) ∈ N}
      zero_mem' := by change nativeTranslation S 1 ∈ N; rw [map_one]; exact N.one_mem
      add_mem' := by
        intro v w hv hw
        change nativeTranslation S (Multiplicative.ofAdd v * Multiplicative.ofAdd w) ∈ N
        rw [map_mul]; exact N.mul_mem hv hw
      neg_mem' := by
        intro v hv
        change nativeTranslation S (Multiplicative.ofAdd v)⁻¹ ∈ N
        rw [map_inv]; exact N.inv_mem hv }
  let W : Subrepresentation (SextetLayers.nativeHexacodeRepresentation S) :=
    { toSubmodule := AddSubgroup.toZModSubmodule 2 H
      apply_mem_toSubmodule := by
        intro g v hv
        change nativeTranslation S (Multiplicative.ofAdd
          (SextetLayers.nativeHexacodeRepresentation S g v)) ∈ N
        exact (SextetLayers.nativeHexacodeRepresentation_conjugation S g
          (Multiplicative.ofAdd v)) ▸ (inferInstance : N.Normal).conj_mem _ hv g }
  let : Representation.IsIrreducible (SextetLayers.nativeHexacodeRepresentation S) :=
    Representation.RepEquiv.irreducible_of_group_iso (nativeStabilizerEquiv S)
      (ρ := Representation.Hexacode.action.comp Atlas.Codes.sextetQuotient)
      (fun g v => congrArg (fun f => f v)
        (SextetLayers.nativeHexacodeRepresentation_apply S g).symm)
      Representation.Hexacode.sextet_action_isIrreducible
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply bot_unique
    intro n hn
    obtain ⟨v,rfl⟩ := hle hn
    have hv : v.toAdd ∈ W := hn
    rw [hb] at hv
    have h1 : v = 1 := Multiplicative.toAdd.injective hv
    rw [h1,map_one]
    exact one_mem _
  · right
    apply le_antisymm hle
    rintro n ⟨v,rfl⟩
    have hv : v.toAdd ∈ W := by rw [ht]; trivial
    exact hv

end MathieuCode.J4Fusion
