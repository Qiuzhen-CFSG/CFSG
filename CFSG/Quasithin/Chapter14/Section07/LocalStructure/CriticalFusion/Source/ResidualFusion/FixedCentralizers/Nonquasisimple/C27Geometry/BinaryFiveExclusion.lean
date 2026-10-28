module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.LinearExclusion
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics

/-!
# Excluding the binary five-space row at the original fixed centralizer

The actual star stabilizer is the entire radical-intersection normalizer.
The intrinsic radical theorem constructs its proper partial flag in SL₅(2).
Transport through the natural matrix action keeps the whole stabilizer.
Its factor five forces the flag to one line or hyperplane, whose two-core
quotient has order 20160. Its factor seven contradicts the original A₅
residual. No C.2.7 parabolic predicate or geometric transport is assumed.

Source: Aschbacher--Smith C.2.7(3)(h), pp.145--147, and 14.7.68(2),
pp.1071--1072.
-/

public section
open Subgroup Theory.GroupTheory

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_binaryFive_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* SL(5,ZMod 2)) : False := by
  have hcard : Nat.card SL(5,ZMod 2) = 9999360 := by
    rw [Nat.card_congr (slEquivLinear 5).toEquiv,
      ← Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
    decide
  have hlarge : 40320 < Nat.card (starImage Lu (d.fixedCore u) Lu) := by
    rw [Nat.card_congr e.toEquiv,hcard]
    decide
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  have hi := (ChapterC.C27Source.star_intersection_placement_of_large_order
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) hlarge).1
  let R := (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  let P := (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  have hP : P.map e.toMonoidHom = normalizer (R.map e.toMonoidHom : Set SL(5,ZMod 2)) := by
    rw [show P = normalizer (R : Set (starImage Lu (d.fixedCore u) Lu)) from
      d.fixedStarM_eq_radicalNormalizer_of_large_order u h hlarge,
      map_equiv_normalizer_eq]
  obtain ⟨m,B,hm,_,hinc,hproper,hflag⟩ := Matrix.HigherLinear.binary_five_radical_normalizer
    (R.map e.toMonoidHom) (hi.map_equiv e)
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hmap : (P.map e.toMonoidHom).map (slEquivLinear 5).toMonoidHom =
      ⨅ i, parabolic (B i) := by
    rw [hP,hflag,Subgroup.map_iInf _ (slEquivLinear 5).injective]
    apply congrArg iInf
    funext i
    ext x
    obtain ⟨g,rfl⟩ := (slEquivLinear 5).surjective x
    rw [← LinearParabolics.linearStabilizer_eq_parabolicSL]
    constructor
    · rintro ⟨y,hy,he⟩
      have hy' : y = g := (slEquivLinear 5).injective he
      subst y
      exact (LinearParabolics.binary_mem_linearStabilizer (B i) g).mp hy
    · intro hg
      exact ⟨g,(LinearParabolics.binary_mem_linearStabilizer (B i) g).mpr hg,rfl⟩
  let t := ((subgroupOfEquivOfLe
    (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm.trans
      (e.subgroupMap P)).trans ((slEquivLinear 5).subgroupMap (P.map e.toMonoidHom))
  let v := t.trans (MulEquiv.subgroupCongr hmap)
  have hres := d.fixedStarM_hasA5TwoResidual_of_source u h
  have h5 : 5 ∣ Nat.card (⨅ i, parabolic (B i) : Subgroup (LinearGroup 5)) := by
    rw [← Nat.card_congr v.toEquiv]
    exact hres.five_dvd_card
  obtain ⟨b,i,_,he⟩ := GeometricFlags.exists_endpoint_coordinates hm B hinc.monotone
    (fun i => (hproper i).1) (fun i => (hproper i).2) h5
  have hne : flagStabilizer b {i} ≠ ⊤ := by
    rw [flagStabilizer_singleton]
    exact FourParabolicAction.parabolic_ne_top (flagSpace_ne_bot b i) (flagSpace_ne_top b i)
  exact LinearParabolics.binaryFive_false_of_coordinates hres b {i} hne
    (v.trans (MulEquiv.subgroupCongr he))
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
