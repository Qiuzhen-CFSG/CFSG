module
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction

/-!
# Invariant cubic generation of the actual G₂(2)′ model

The two restricted parabolics have relative Sylow index three and generate
the binary derived group. Their intrinsic root descriptions make each
invariant under every automorphism preserving the Sylow subgroup. Sylow
conjugacy transports this exact property to any prescribed Sylow.

Source: Aschbacher--Smith 14.3.6(2) and its application in14.3.15,
printed pp.991 and994. This retains the actual derived G₂ carrier.
-/

public section
open Subgroup
namespace Atlas.G2.BinaryParabolicPair.InvariantCubicGeneration

theorem fixed_invariant_cubic_generation (H : Subgroup DerivedModel)
    (_hs : (derivedSylow : Subgroup DerivedModel) ≤ H)
    (hl : ∀ J : Subgroup DerivedModel, (derivedSylow : Subgroup DerivedModel) ≤ J →
      (derivedSylow : Subgroup DerivedModel).relIndex J = 3 →
      (∀ a : MulAut DerivedModel,
        (derivedSylow : Subgroup DerivedModel).map a.toMonoidHom = derivedSylow →
        J.map a.toMonoidHom = J) → J ≤ H) : H = ⊤ := by
  have hinv (a : MulAut DerivedModel)
      (ha : (derivedSylow : Subgroup DerivedModel).map a.toMonoidHom = derivedSylow) :
      derivedFirst.map a.toMonoidHom = derivedFirst ∧
      derivedSecond.map a.toMonoidHom = derivedSecond := by
    rw [derivedSylow_eq] at ha
    have hh := SylowParabolicInvariance.restricted_parabolics_invariant a ha
    rw [LieParabolicSetup.parabolic₁_binary] at hh
    exact hh
  have hfirst := hl derivedFirst derivedSylow_le_first derivedSylow_index_in_first
    (fun a ha => (hinv a ha).1)
  have hsecond := hl derivedSecond derivedSylow_le_second derivedSylow_index_in_second
    (fun a ha => (hinv a ha).2)
  have hgen : derivedFirst ⊔ derivedSecond = ⊤ := by
    apply map_injective (f := DerivedModel.subtype) DerivedModel.subtype_injective
    rw [Subgroup.map_sup, derivedFirst_map_subtype, derivedSecond_map_subtype,
      ← MonoidHom.range_eq_map, DerivedModel.range_subtype]
    have h := DerivedParabolicGeneration.binary_restricted_pair_generate
    rw [LieParabolicSetup.parabolic₁_binary] at h
    exact h
  exact top_unique (hgen ▸ sup_le hfirst hsecond)

/-- Every Sylow subgroup admits generating cubic overgroups invariant under
all automorphisms preserving that Sylow subgroup. -/
theorem sylow_invariant_cubic_generation (P : Sylow 2 DerivedModel) (H : Subgroup DerivedModel)
    (hs : (P : Subgroup DerivedModel) ≤ H)
    (hl : ∀ J : Subgroup DerivedModel, (P : Subgroup DerivedModel) ≤ J →
      (P : Subgroup DerivedModel).relIndex J = 3 →
      (∀ a : MulAut DerivedModel, (P : Subgroup DerivedModel).map a.toMonoidHom = P →
        J.map a.toMonoidHom = J) → J ≤ H) : H = ⊤ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq DerivedModel P derivedSylow
  let a := MulAut.conj g
  have hmap : (P : Subgroup DerivedModel).map a.toMonoidHom = (derivedSylow : Subgroup DerivedModel) :=
    congrArg Sylow.toSubgroup hg
  have he : H.map a.toMonoidHom = ⊤ := by
    apply fixed_invariant_cubic_generation
    · exact hmap ▸ map_mono hs
    · intro J hPJ hi hinv
      have hPpre : (P : Subgroup DerivedModel) ≤ J.comap a.toMonoidHom :=
        (map_le_iff_le_comap).mp (hmap ▸ hPJ)
      have hindex : (P : Subgroup DerivedModel).relIndex (J.comap a.toMonoidHom) = 3 := by
        have hh := relIndex_map_map_of_injective (f := a.toMonoidHom)
          (P : Subgroup DerivedModel) (J.comap a.toMonoidHom) a.injective
        rw [hmap,map_comap_eq_self_of_surjective a.surjective] at hh
        exact hh.symm.trans hi
      have hpreinv (b : MulAut DerivedModel) (hb : (P : Subgroup DerivedModel).map b.toMonoidHom = P) :
          (J.comap a.toMonoidHom).map b.toMonoidHom = J.comap a.toMonoidHom := by
        let d : MulAut DerivedModel := a.symm.trans (b.trans a)
        have hd : d.toMonoidHom.comp a.toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := by
          apply MonoidHom.ext
          intro x
          exact congrArg a (congrArg b (a.symm_apply_apply x))
        have hdP : (derivedSylow : Subgroup DerivedModel).map d.toMonoidHom = derivedSylow := by
          rw [←hmap,map_map,hd,←map_map,hb]
        have heq := hinv d hdP
        apply map_injective (f := a.toMonoidHom) a.injective
        rw [map_map,←hd,←map_map,map_comap_eq_self_of_surjective a.surjective,heq]
      have hh := map_mono (f := a.toMonoidHom) (hl _ hPpre hindex hpreinv)
      rwa [map_comap_eq_self_of_surjective a.surjective] at hh
  apply map_injective (f := a.toMonoidHom) a.injective
  rw [he,map_top_of_surjective _ a.surjective]

end Atlas.G2.BinaryParabolicPair.InvariantCubicGeneration
