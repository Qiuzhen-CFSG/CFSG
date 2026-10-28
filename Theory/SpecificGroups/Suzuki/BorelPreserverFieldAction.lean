module
public import Theory.SpecificGroups.Suzuki.BorelFieldQuotient
public import Theory.SpecificGroups.Suzuki.BorelInvolutionCore
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# The coefficient action of every Suzuki Borel preserver

The standard root group is the Borel's two-core, so a Borel preserver
preserves it. The proved inner--field decomposition therefore has its
inner factor in the same Borel. The literal root quotient kills that
factor and retains the ordinary action on defining-field units.

The Chapter 10 central Hall consumer compares this action with its
original tensor exchanger, without assuming that exchanger is involutory.
Source: Aschbacher--Smith 9.2.7, pp.731--732, refs/quasithin.pdf, and
Huppert--Blackburn III, XI.3.1 and XI.3.3.
-/

public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient

theorem borel_preserver_field_action (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hB : ∀ x ∈ SuzukiBorelSubgroup m, α x ∈ SuzukiBorelSubgroup m) :
    ∃ σ : BinaryGaloisField (2*m+1) ≃+* BinaryGaloisField (2*m+1),
      ∀ x : SuzukiBorelSubgroup m,
        projection m hm ⟨α x,hB x x.property⟩ =
          Units.map σ.toMonoidHom (projection m hm x) := by
  have hmap : (SuzukiBorelSubgroup m).map α.toMonoidHom = SuzukiBorelSubgroup m := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      exact hB x hx
    · rw [card_map_of_injective α.injective]
  let a : MulAut (SuzukiBorelSubgroup m) :=
    (α.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  have hroot : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hxB : x ∈ SuzukiBorelSubgroup m := by
        rw [suzukiBorelSubgroup_eq_sup]
        exact mem_sup_left hx
      have hc : (⟨x,hxB⟩ : SuzukiBorelSubgroup m) ∈ pCore 2 (SuzukiBorelSubgroup m) := by
        rw [suzukiBorel_pCore m hm]
        exact hx
      have hh := mem_map_of_mem a.toMonoidHom hc
      rw [pCore_map_iso,suzukiBorel_pCore m hm] at hh
      exact hh
    · rw [card_map_of_injective α.injective]
  obtain ⟨g,σ,he⟩ := suzukiAut_eq_inner_mul_field m hm α
  have hg : g ∈ SuzukiBorelSubgroup m := by
    rw [←suzukiRootSubgroup_normalizer m hm]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh : α.toMonoidHom = (MulAut.conj g).toMonoidHom.comp
        (suzukiFieldAut m σ).toMonoidHom := congrArg MulEquiv.toMonoidHom he
    rwa [hh,←map_map,field_map_root] at hroot
  refine ⟨σ.toRingEquiv,fun x => ?_⟩
  have hh : (⟨α x,hB x x.property⟩ : SuzukiBorelSubgroup m) =
      borelActor m ⟨g,hg⟩ σ x := by
    apply Subtype.ext
    change α x = _
    rw [borelActor_apply,he]
  rw [hh]
  exact projection_borelActor m hm ⟨g,hg⟩ σ x

end BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
