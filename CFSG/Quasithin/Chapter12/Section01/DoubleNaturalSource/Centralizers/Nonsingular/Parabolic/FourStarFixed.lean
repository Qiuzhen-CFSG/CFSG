module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarModule
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.FixedGeometry

/-!
# Fixed-space control for the original degree-four middle parabolic

A full binary flag fixes exactly its first natural line and last dual line.
Every line-hyperplane parabolic containing that Sylow fixes these two lines.
Apply this calculation to the actual natural-plus-dual moved section and its
fixed supplement, using the marking supplied by the module equivalence.

Relative normality in C_G(w) identifies the component Sylow with the original
intersection C_T(w) intersect K. Its image in the star quotient is a full
component Sylow. Vectors fixed by the original C_T(w) are therefore fixed by
the residual's image in the middle parabolic. Transport through the full
quotient action proves centralization in G, retaining the central kernel.
`FourStarFixedSource` applies this to the original nonsingular consumer.
Source: Aschbacher--Smith 12.1.1, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.InvariantNodeActions BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer

private theorem middle_flag_pair (b : FiveBasis) :
    flagStabilizer b {0,3} ≤ pairStabilizer (b 0) (b.coord 4) := by
  intro g hg
  have h0 := (mem_flagStabilizer_iff _ _ _).mp hg 0 (by simp)
  have h3 := (mem_flagStabilizer_iff _ _ _).mp hg 3 (by simp)
  rw [flagSpace_zero] at h0
  rw [flagSpace_last] at h3
  constructor
  · have hv := (h0 (b 0)).mpr (Submodule.subset_span (Set.mem_singleton _))
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
    have hc0 : c ≠ 0 := by
      intro hz
      exact b.ne_zero 0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
    simpa [hc1] using hc.symm
  · intro v
    exact (by decide : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y) _ _ (h3 v)

/-- The line-hyperplane parabolic fixes the full fixed space of any Sylow
it contains, on the literal natural-plus-dual module. -/
private theorem middle_flag_fixes_sylow_fixed (b : FiveBasis)
    (P : Sylow 2 (LinearGroup 5)) (hP : (P : Subgroup _) ≤ flagStabilizer b {0,3})
    (g : LinearGroup 5) (hg : g ∈ flagStabilizer b {0,3})
    (v : CoordinateSpace 5) (hv : v ∈ fixedSpace naturalDualRepresentation P) :
    naturalDualRepresentation g v = v := by
  obtain ⟨c,hc⟩ := sylow_eq_cutStabilizer P
  have he : flagStabilizer b {0,3} = flagStabilizer c {0,3} :=
    cutStabilizer_eq_of_fullFlag_le c b {0,3} (hc ▸ hP)
  rw [hc,fixedSpace_fullFlag (by decide : 0 < 4)] at hv
  have hgg := middle_flag_pair c (he ▸ hg)
  have hk := kernel_prod_lines (c 0) (c.coord 4)
  rw [←hk] at hgg
  exact hgg.2 v hv
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The original middle parabolic centralizes the star module fixed by
C_T(w), with the full quotient map and fixed supplement retained. -/
theorem doubleNatural_four_adapted_C27_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi
  let J := offenderSubgroup (starRepresentation K Q)
  let C := (starImage K Q K).subgroupOf J
  let ρ := (starRepresentation K Q).comp J.subtype
  let : (K.subgroupOf (B.pointCentralizer w)).Normal := hKn
  have hCJ := (star_offender_fitting hi).1
  let j := subgroupOfEquivOfLe hCJ
  obtain ⟨s,hs,⟨e⟩⟩ := D.doubleNatural_four_adapted_C27_naturalDual h B S w hw K hKn hRK hi
  let a := (j.symm.trans e.groupEquiv).trans (slEquivLinear 5)
  obtain ⟨b,hb⟩ := D.doubleNatural_four_adapted_C27_middle h B S w hw K hKn hRK hi a
  let H := B.pointCentralizer w
  let K₀ := K.subgroupOf H
  let : K₀.Normal := hKn
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  obtain ⟨P₁,hP₁⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let eK := subgroupOfEquivOfLe hi.component.1
  let P₂ := P₁.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP₂ : (P₂ : Subgroup K).map K.subtype = B.pointSylow w ⊓ K := by
    change ((P₁ : Subgroup K₀).map eK.toMonoidHom).map K.subtype = _
    rw [map_map]
    have he : K.subtype.comp eK.toMonoidHom = H.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hP₁,map_inf _ _ _ H.subtype_injective,hP₀,
      map_subgroupOf_eq_of_le hi.component.1]
  let q := a.toMonoidHom.comp (toStarImage K Q)
  let P := P₂.mapSurjective (f := q) (a.surjective.comp (toStarImage_surjective K Q))
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hqM (k : K) (hk : (k : G) ∈ B.localPointCentralizer w) :
      q k ∈ BinaryLinear.FiveFlagGeometry.flagStabilizer b {0,3} := by
    rw [←hb]
    apply mem_map_of_mem a.toMonoidHom
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel K Q)) ⟨hk,k.property⟩
  have hP : (P : Subgroup (LinearGroup 5)) ≤ BinaryLinear.FiveFlagGeometry.flagStabilizer b {0,3} := by
    rintro _ ⟨k,hk,rfl⟩
    exact hqM k (hPM (hP₂ ▸ mem_map_of_mem K.subtype hk).1)
  have heAction (k : K) (u : s.space.toSubmodule) :
      e.linearEquiv (s.space.toRepresentation (j.symm (toStarImage K Q k)) u) =
        BinaryNaturalDual.naturalDualRepresentation (q k) (e.linearEquiv u) :=
    (e.intertwines (j.symm (toStarImage K Q k)) u).trans
      (ChapterB.QuasisimpleSource.NaturalDualCentralizer.action_apply 5 _ _)
  intro r hr
  rintro x ⟨⟨z,hz,rfl⟩,hfix⟩
  let v : Additive (starV K Q) := Additive.ofMul ⟨z,hz⟩
  obtain ⟨u,hu,c,hc,he⟩ := Submodule.mem_sup.mp
    (show v ∈ s.space.toSubmodule ⊔ Representation.invariants ρ by rw [hs]; trivial)
  let u₀ : s.space.toSubmodule := ⟨u,hu⟩
  have hfixK (k : K) (hk : k ∈ P₂) : ρ (j.symm (toStarImage K Q k)) v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have hkP : (k : G) ∈ B.pointSylow w := (hP₂ ▸ mem_map_of_mem K.subtype hk).1
    have hh := hfix k hkP
    change (((starRepresentation K Q (QuotientGroup.mk' (starKernel K Q)
      (⟨k,mem_sup_left k.property⟩ : (K ⊔ Q : Subgroup G))) v).toMul :
        (K ⊔ Q : Subgroup G)) : G) = (z : G)
    rw [starRepresentation_apply]
    change (k : G) * (z : G) * (k : G)⁻¹ = (z : G)
    change (k : G) * (z : G) = (z : G) * (k : G) at hh
    rw [hh,mul_inv_cancel_right]
  have huP : e.linearEquiv u₀ ∈ fixedSpace
      (BinaryNaturalDual.naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space 5))
      (P : Subgroup (LinearGroup 5)) := by
    rintro ⟨g,⟨k,hk,rfl⟩⟩
    have huFix : s.space.toRepresentation (j.symm (toStarImage K Q k)) u₀ = u₀ := by
      apply Subtype.ext
      have hh := hfixK k hk
      rw [←he,map_add,hc] at hh
      exact add_right_cancel hh
    exact (heAction k u₀).symm.trans (congrArg e.linearEquiv huFix)
  let k : K := ⟨r,hRK hr⟩
  have hrM : r ∈ B.localPointCentralizer w :=
    ⟨B.pointResidual_le_normalizer w hr,(B.pointResidual_le w hr).2⟩
  have hum := Nonsingular.middle_flag_fixes_sylow_fixed b P hP (q k) (hqM k hrM) _ huP
  have huFix : s.space.toRepresentation (j.symm (toStarImage K Q k)) u₀ = u₀ := by
    apply e.linearEquiv.injective
    exact (heAction k u₀).trans hum
  have hvFix : ρ (j.symm (toStarImage K Q k)) v = v := by
    rw [←he,map_add,hc]
    exact congrArg (fun x => x+c) (congrArg Subtype.val huFix)
  have hh := congrArg (fun y : Additive (starV K Q) => ((y.toMul : (K ⊔ Q : Subgroup G)) : G)) hvFix
  change (((starRepresentation K Q (QuotientGroup.mk' (starKernel K Q)
    (⟨k,mem_sup_left k.property⟩ : (K ⊔ Q : Subgroup G))) v).toMul :
      (K ⊔ Q : Subgroup G)) : G) = (z : G) at hh
  rw [starRepresentation_apply] at hh
  change r * (z : G) * r⁻¹ = (z : G) at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
