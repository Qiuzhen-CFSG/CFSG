module
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizer
public import Theory.SpecificGroups.BinaryLinear.FivePointExtension

/-!
# Automorphisms of quintic two-local normalizers in binary five-space

A nontrivial two-subgroup whose normalizer has a factor five has an endpoint
parabolic as its full normalizer. An automorphism preserving that subgroup
therefore preserves an endpoint parabolic and is inner. Inverse transpose
reduces the hyperplane case to the existing point-radical rigidity theorem.

Consequently, in any overgroup with a self-centralizing normal GL₅(2), the
normalizer of that two-subgroup lies in the normal GL₅(2). The subgroup's
normalizer also contains an actual Sylow two-subgroup of GL₅(2).
Source application: Aschbacher--Smith 12.6.17, printed p.827, combined
manuscript of 1 March 2004, on the original R_v normalizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.QuinticNormalizer
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem map_congr_stable {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (A : Subgroup X)
    (ha : A.map a.toMonoidHom = A) :
    (A.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = A.map e.toMonoidHom := by
  rw [map_map]
  have hh : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg e (congrArg a (e.symm_apply_apply x))
  rw [hh,←map_map,ha]

theorem inner_of_preserves_endParabolic (P : Subgroup (LinearGroup 5))
    (hP : FiveParabolicStabilizer.IsEndParabolic P) (a : MulAut (LinearGroup 5))
    (ha : P.map a.toMonoidHom = P) : a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  rcases hP with ⟨v,hv,rfl⟩ | ⟨f,hf,rfl⟩
  · exact BinaryLinear.inner_of_preserves_pointParabolic v hv a ha
  · obtain ⟨v,hv,he⟩ := FiveParabolicStabilizer.hyperplane_map_graph hf
    have hc := map_congr_stable (graphLinear 5) a (parabolic f.ker) ha
    rw [he] at hc
    obtain ⟨g,hg⟩ := BinaryLinear.inner_of_preserves_pointParabolic v hv
      (MulAut.congr (graphLinear 5) a) hc
    obtain ⟨x,hx⟩ := (MulAut.congr_inner_iff (graphLinear 5) a).mp ⟨g,hg.symm⟩
    exact ⟨x,hx.symm⟩

theorem inner_of_preserves_twoSubgroup (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5))))
    (a : MulAut (LinearGroup 5)) (ha : U.map a.toMonoidHom = U) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  apply inner_of_preserves_endParabolic _ (normalizer_isEndParabolic U hU hne hfive) a
  rw [map_equiv_normalizer_eq,ha]

theorem exists_sylow_le_normalizer (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) :
    ∃ S : Sylow 2 (LinearGroup 5), (S : Subgroup _) ≤ normalizer (U : Set (LinearGroup 5)) := by
  open FiveFlagGeometry FiveFlagGeometry.MaximalOvergroups in
    rcases normalizer_isEndParabolic U hU hne hfive with ⟨v,hv,he⟩ | ⟨f,hf,he⟩
    · obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace
        (Submodule.span (ZMod 2) {v}) 0 (by simpa using finrank_span_singleton hv)
      refine ⟨flagSylow b,?_⟩
      rw [he,flagSylow_coe,←hb,←flagStabilizer_singleton]
      exact (flag_le_iff b _ _).mpr (Set.subset_univ _)
    · have hd : Module.finrank (ZMod 2) f.ker = 4 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        norm_num [Space] at hh
        omega
      obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace f.ker 3 (by simpa using hd)
      refine ⟨flagSylow b,?_⟩
      rw [he,flagSylow_coe,←hb,←flagStabilizer_singleton]
      exact (flag_le_iff b _ _).mpr (Set.subset_univ _)
end BinaryLinear.QuinticNormalizer
namespace BinaryLinear.QuinticNormalizer
open OuterCyclic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_binaryFive_normal
    (B : Subgroup G) [B.Normal] (e : B ≃* LinearGroup 5)
    (hc : centralizer (B : Set G) = ⊥)
    (U : Subgroup B) (hp : IsPGroup 2 U) (hu : U ≠ ⊥)
    (hf : 5 ∣ Nat.card (normalizer (U : Set B))) :
    normalizer (U.map B.subtype : Set G) ≤ B := by
  intro g hg
  let a : MulAut B := MulAut.conjNormal g
  have ha : U.map a.toMonoidHom = U := by
    apply map_injective B.subtype_injective
    rw [map_map]
    have hh : B.subtype.comp a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp B.subtype := rfl
    rw [hh,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hg
  let b := MulAut.congr e a
  have hb : (U.map e.toMonoidHom).map b.toMonoidHom = U.map e.toMonoidHom :=
    map_congr_stable e a U ha
  have hf' : 5 ∣ Nat.card (normalizer (U.map e.toMonoidHom : Set (LinearGroup 5))) := by
    rw [←map_equiv_normalizer_eq U e,card_map_of_injective e.injective]
    exact hf
  obtain ⟨x,hx⟩ := inner_of_preserves_twoSubgroup (U.map e.toMonoidHom) (hp.map _)
    (fun he => hu ((U.map_eq_bot_iff_of_injective e.injective).mp he)) hf' b hb
  obtain ⟨y,hy⟩ := (MulAut.congr_inner_iff e a).mp ⟨x,hx.symm⟩
  have hgx : g = (y : B) := by
    apply MulAut.conjNormal_injective_of_centralizer_eq_bot B hc
    change a = _
    simpa only [MulAut.conjNormal_val] using hy
  rw [hgx]
  exact y.property
end BinaryLinear.QuinticNormalizer
