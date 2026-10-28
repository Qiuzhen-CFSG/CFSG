module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OriginalModule

/-!
# The canonical X/O₂(X)-action on the original moved subgroup

U lies in Ω₁Z(O₂(I)). Relative normality of X puts its two-core inside
O₂(I), so this core centralizes U. Ambient conjugation therefore descends
through the literal map X → X/O₂(X), on the additive carrier of U itself.
No choice of coordinates, isomorphic replacement or star quotient is used.

Source: Aschbacher--Smith, 15.2.23, printed pp.1116--1117.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06 PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- The original U lies in the central elementary layer of the escaping I. -/
theorem U_le_omegaCore (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ZS ≤ omegaOneCenterAmbient (I.pCoreIn 2) :=
  (U_le_span X ZS).trans (conjugateSpanBy_le (d.plane_le_escape_core_omega hI hfit)
    (hXI.trans (I.le_normalizer.trans ((normalizer_le_normalizer_characteristic_image I (pCore 2 I)).trans
      (normalizer_le_normalizer_omegaCenter _)))))

include d in
/-- Core restriction retains the actual ambient embeddings. -/
theorem X_core_centralizes_U (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    X.pCoreIn 2 ≤ centralizer (U X ZS : Set G) := by
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  have hcore : X.pCoreIn 2 ≤ I.pCoreIn 2 := by
    have hh := map_mono (f := I.subtype)
      (pCoreIn_le_of_subnormal 2 (inferInstance : (X.subgroupOf I).Normal).isSubnormal)
    rwa [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hXI] at hh
  intro x hx u hu
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp
    (U_le_omegaCore d hI hfit hXI hu)).2.2 x (hcore hx)).symm

/-- Conjugation by X, acting on U with its original subgroup carrier. -/
noncomputable def U_conjugation (hI : PlaneEscapes Mc ZS I)
    (hn : I ≤ normalizer (X : Set G)) : X →* MulAut (U X ZS) :=
  (U X ZS).normalizerMonoidHom.comp
    (inclusion (le_sup_left.trans (U_normalized d hI hn)))

/-- Descent of the actual conjugation action through X/O₂(X). -/
noncomputable def U_quotientConjugation (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    (X ⧸ pCore 2 X) →* MulAut (U X ZS) :=
  QuotientGroup.lift _ (U_conjugation d hI hn) (by
    intro x hx
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (x : G) * (u : G) * (x : G)⁻¹ = u
    have hc : (u : G) * (x : G) = (x : G) * (u : G) :=
      X_core_centralizes_U d hI hfit hXI hn (mem_map_of_mem X.subtype hx) u u.property
    rw [← hc, mul_inv_cancel_right])

/-- The binary representation is constructed on Additive U itself. -/
noncomputable def U_representation (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    letI := U_elementary d hI hfit hXI
    Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ZS)) := by
  let := U_elementary d hI hfit hXI
  let a := U_quotientConjugation d hI hfit hXI hn
  exact {
    toFun g := (a g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a 1 v.toMul) = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a (g*h) v.toMul) = _
      rw [map_mul]
      rfl }

/-- The action equation uses the original core quotient, with no hidden map. -/
theorem U_representation_apply (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) (x : X) (u : Additive (U X ZS)) :
    letI := U_elementary d hI hfit hXI
    (((U_representation d hI hfit hXI hn) (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
      (x : G) * (u.toMul : G) * (x : G)⁻¹ := rfl

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
