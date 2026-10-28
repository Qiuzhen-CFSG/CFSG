module



public import Mathlib.Tactic.Linter.FlexibleLinter
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Sylow
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers

/-!
# Unique Sylow-normal four-groups in Mathieu 22 and 23

The fixed Sylow calculation in M23 identifies its only normal elementary
four-group. Sylow conjugacy transports that calculation to every Sylow subgroup.
The point-stabilizer embedding M22 into M23 has odd index, giving the same
uniqueness statement in M22. These facts screen the paired-module source in
Chapter 2, Section 4.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu

theorem m23_sylow_normal_four_unique (P : Sylow 2 M23)
    (V W : Subgroup M23)
    (hVP : V ≤ (P : Subgroup M23)) (hPV : (P : Subgroup M23) ≤ normalizer (V : Set M23))
    (hWP : W ≤ (P : Subgroup M23)) (hPW : (P : Subgroup M23) ≤ normalizer (W : Set M23))
    (hV : IsElementaryAbelian 2 V) (hW : IsElementaryAbelian 2 W)
    (hcV : Nat.card V = 4) (hcW : Nat.card W = 4) : V = W := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 P M23Geometry.FusionCertificate.sylow
  let e := MulAut.conj g
  have hP : (P : Subgroup M23).map e.toMonoidHom =
      M23Geometry.FusionCertificate.subgroup := by
    have hh : (P : Subgroup M23).map e.toMonoidHom =
      (M23Geometry.FusionCertificate.sylow : Subgroup M23) := congrArg Sylow.toSubgroup hg
    simpa only [M23Geometry.FusionCertificate.sylow, Sylow.coe_ofCard] using hh
  have hv := M23Geometry.FourNormalizers.normal_four_eq_common (V.map e.toMonoidHom)
    (hP ▸ map_mono hVP)
    (by rw [←hP,←map_equiv_normalizer_eq]; exact map_mono hPV)
    (by let := hV; exact IsElementaryAbelian.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hcV)
  have hw := M23Geometry.FourNormalizers.normal_four_eq_common (W.map e.toMonoidHom)
    (hP ▸ map_mono hWP)
    (by rw [←hP,←map_equiv_normalizer_eq]; exact map_mono hPW)
    (by let := hW; exact IsElementaryAbelian.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hcW)
  exact map_injective e.injective (hv.trans hw.symm)

theorem m22_sylow_normal_four_unique (P : Sylow 2 M22)
    (V W : Subgroup M22)
    (hVP : V ≤ (P : Subgroup M22)) (hPV : (P : Subgroup M22) ≤ normalizer (V : Set M22))
    (hWP : W ≤ (P : Subgroup M22)) (hPW : (P : Subgroup M22) ≤ normalizer (W : Set M22))
    (hV : IsElementaryAbelian 2 V) (hW : IsElementaryAbelian 2 W)
    (hcV : Nat.card V = 4) (hcW : Nat.card W = 4) : V = W := by
  let f : M22 →* M23 := (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp m23EquivM22PointStabilizer.injective
  obtain ⟨Q,hPQ⟩ := (P.isPGroup'.map f).exists_le_sylow
  have hPcard : Nat.card P = 128 := by
    rw [P.card_eq_multiplicity,m22_order]
    decide +kernel
  have hQcard : Nat.card Q = 128 := by
    rw [Q.card_eq_multiplicity,m23_order]
    decide +kernel
  have hPQeq : (P : Subgroup M22).map f = (Q : Subgroup M23) :=
    eq_of_le_of_card_ge hPQ (by rw [card_map_of_injective hf,hPcard,hQcard])
  apply map_injective hf
  apply m23_sylow_normal_four_unique Q (V.map f) (W.map f)
  · exact hPQeq ▸ map_mono hVP
  · rw [←hPQeq]
    exact (map_mono hPV).trans (V.le_normalizer_map f)
  · exact hPQeq ▸ map_mono hWP
  · rw [←hPQeq]
    exact (map_mono hPW).trans (W.le_normalizer_map f)
  · let := hV
    exact IsElementaryAbelian.map f
  · let := hW
    exact IsElementaryAbelian.map f
  · exact (card_map_of_injective hf).trans hcV
  · exact (card_map_of_injective hf).trans hcW

end Sporadic.Mathieu
