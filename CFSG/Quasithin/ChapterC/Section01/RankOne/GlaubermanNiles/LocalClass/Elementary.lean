module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Stellmacher.OmegaOneCenterMap

/-!
# The elementary normal module in C.1.17

The omega center of the marked Sylow subgroup centralizes O₂(H). Since
F*(H)=O₂(H), self-centralization puts that omega center inside O₂(H),
and hence inside Ω₁(Z(O₂(H))). The latter is characteristic in the normal
two-core, so it contains the entire normal closure V. Thus V really is an
elementary abelian normal subgroup, without an extra module hypothesis.

Source: the construction in Aschbacher–Smith C.1.17, combined manuscript
(1 March 2004), p.126, and the generalized-Fitting centralizer theorem.
-/

public section

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles

open Theory.GroupTheory Stellmacher

variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

/-- The source characteristic-two condition in its centralizer form. -/
theorem InLocalClass.core_selfCentralizing (h : InLocalClass e) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  rw [← h.fitting]
  exact centralizer_generalizedFitting_le H

/-- The literal normal closure lies in the elementary center of the two-core. -/
theorem InLocalClass.localV_le_coreOmegaCenter (h : InLocalClass e) :
    localV e ≤ omegaOneCenterAmbient (pCore 2 H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : (omega₁ (Subgroup.center (pCore 2 H)) (p := 2)).Characteristic :=
    omega₁_characteristic _
  let : (omegaCenter (pCore 2 H)).Characteristic := inferInstanceAs
    ((omega₁ (Subgroup.center (pCore 2 H)) (p := 2)).map
      (Subgroup.center (pCore 2 H)).subtype).Characteristic
  let : (omegaOneCenterAmbient (pCore 2 H)).Normal :=
    inferInstanceAs ((omegaCenter (pCore 2 H)).map (pCore 2 H).subtype).Normal
  obtain ⟨T, he, _⟩ := h.sylow
  have hQ : pCore 2 H ≤ e.range := by
    rw [he]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hcentral : (omegaCenter B).map e ≤ Subgroup.centralizer (pCore 2 H : Set H) := by
    rintro _ ⟨b, hb, rfl⟩ q hq
    obtain ⟨c, rfl⟩ := hQ hq
    obtain ⟨z, _, rfl⟩ := hb
    simpa only [map_mul, Subgroup.subtype_apply] using congrArg e ((Subgroup.mem_center_iff.mp z.property) c)
  apply Subgroup.normalClosure_le_normal
  intro b hb
  refine (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨h.core_selfCentralizing (hcentral hb), ?_, hcentral hb⟩
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨z, hz, rfl⟩ := ha
  let : IsElementaryAbelian 2 (omega₁ (Subgroup.center B) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (Subgroup.center B)
  simpa only [map_pow, map_one, MonoidHom.comp_apply] using congrArg (e.comp (Subgroup.center B).subtype)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)

/-- The normal closure in C.1.17 is elementary abelian. -/
theorem InLocalClass.localV_elementary (h : InLocalClass e) :
    IsElementaryAbelian 2 (localV e) := by
  have hmem (x : localV e) := (mem_omegaOneCenterAmbient_iff (pCore 2 H) (x : H)).mp
    (h.localV_le_coreOmegaCenter x.property)
  refine {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      ((hmem x).2.2 y (hmem y).1).symm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (hmem x).2.1)
  }

/-- Thus V is killed by the quotient map defining H*. -/
theorem InLocalClass.localV_le_localKernel (h : InLocalClass e) :
    localV e ≤ localKernel e :=
  Subgroup.le_centralizer_iff_isMulCommutative.mpr h.localV_elementary.toIsMulCommutative

/-- In particular the moved subgroup used in the natural-module identification
is contained in the elementary center of the two-core. -/
theorem InLocalClass.moved_le_coreOmegaCenter (h : InLocalClass e) :
    moved e ≤ omegaOneCenterAmbient (pCore 2 H) :=
  (moved_le_localV e).trans h.localV_le_coreOmegaCenter

end CFSG.Quasithin.ChapterC.GlaubermanNiles
