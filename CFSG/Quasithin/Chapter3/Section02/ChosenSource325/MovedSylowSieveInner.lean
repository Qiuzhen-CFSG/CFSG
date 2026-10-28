module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveStability
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderFaithful
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTransport
import all CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTransport

/-!
# Recovering the common actor in the original component

A restricted action lying in the component image differs from a component
representative by the literal pointwise kernel. That kernel centralizes the
quasisimple component and lies in it when the component is F*. Nested action
images retain the original subgroup marking. The actual chosen-seed application
is `SeedAlternativesMovedSylowInner`.

Source: Aschbacher--Smith D.3.5(5), printed pp.195--196.
The internal import unfolds the existing nested equivalence only to verify
its subgroup map; no public boundary of that equivalence is changed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

theorem le_of_restrictedSubgroup_le
    (K : Subgroup H) (I : Submodule (ZMod 2) W)
    (_hKI : K ≤ subspaceStabilizer ρ I)
    (hk : subspaceKernel ρ I ⊤ ≤ K)
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I)
    (hi : restrictedSubgroup ρ I A ≤ restrictedSubgroup ρ I K) : A ≤ K := by
  intro a ha
  obtain ⟨k,hkK,he⟩ := hi (show subspaceActionHom ρ I ⟨a,hAI ha⟩ ∈
      restrictedSubgroup ρ I A from ⟨⟨a,hAI ha⟩,ha,rfl⟩)
  have hka : k.val⁻¹ * a ∈ subspaceKernel ρ I ⊤ := by
    refine ⟨mem_top _,fun v hv => ?_⟩
    have hev : ρ k.val v = ρ a v :=
      congrArg (fun q : subspaceActionImage ρ I => (q.val.val ⟨v,hv⟩ : W)) he
    rw [map_mul,Module.End.mul_apply,←hev,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel,map_one,Module.End.one_apply]
  have hm := K.mul_mem hkK (hk hka)
  change k.val * (k.val⁻¹ * a) ∈ K at hm
  simpa only [mul_inv_cancel_left] using hm

theorem le_component_of_restrictedSubgroup_le [Finite H]
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hF : generalizedFitting H = K)
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I)
    (hn : ¬ I ≤ fixedSpace ρ K)
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I)
    (hi : restrictedSubgroup ρ I A ≤ restrictedSubgroup ρ I K) : A ≤ K := by
  apply le_of_restrictedSubgroup_le ρ K I hKI _ A hAI hi
  exact (subspaceKernel_le_component_centralizer ρ K I hKI hn ⊤).trans
    (by simpa only [hF] using centralizer_generalizedFitting_le H)

/-- A marked faithful-image containment lifts to containment in F*, retaining
both the given actor and the image equivalence. -/
theorem le_component_of_marked_image [Finite H]
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hF : generalizedFitting H = K)
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I)
    (hn : ¬ I ≤ fixedSpace ρ K)
    {Q : Type*} [Group Q] (e : subspaceActionImage ρ I ≃* Q)
    (R : Subgroup Q) (hR : (restrictedSubgroup ρ I K).map e.toMonoidHom = R)
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I)
    (hi : (restrictedSubgroup ρ I A).map e.toMonoidHom ≤ R) : A ≤ K := by
  apply le_component_of_restrictedSubgroup_le ρ K hF I hKI hn A hAI
  apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rwa [hR]

/-- Restricting through an invariant containing module preserves the literal
component image under the existing nested action equivalence. -/
theorem nestedImageActionEquiv_restricted
    (U I : Submodule (ZMod 2) W)
    (hU : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ U) (hIU : I ≤ U)
    (K : Subgroup H) (hKI : K ≤ subspaceStabilizer ρ I) :
    (restrictedSubgroup (subspaceImageRepresentation ρ U) (I.comap U.subtype)
      (restrictedSubgroup ρ U K)).map
        (nestedImageActionEquiv ρ U I hU hIU).groupEquiv.toMonoidHom =
      restrictedSubgroup ρ I K := by
  let σ := subspaceImageRepresentation ρ U
  let J := I.comap U.subtype
  let e := nestedImageActionEquiv ρ U I hU hIU
  apply le_antisymm
  · rintro b ⟨c,⟨s,⟨g,hg,hgs⟩,rfl⟩,rfl⟩
    refine ⟨⟨g.val,hKI hg⟩,hg,?_⟩
    apply (subspaceImageRepresentation_injective ρ I)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ g.val v.val = (σ s.val ⟨v.val,hIU v.property⟩ : W)
    change subspaceActionHom ρ U g = s.val at hgs
    rw [←hgs]
    rfl
  · rintro b ⟨g,hg,rfl⟩
    let s : subspaceStabilizer σ J :=
      ⟨subgroupActionHom ρ U K (le_top.trans hU) ⟨g,hg⟩,
        Representation.BinaryOffender.Homogeneous.restrictedSubgroup_le_subspaceStabilizer_comap
          ρ U I hKI ⟨⟨g.val,(le_top.trans hU) hg⟩,hg,rfl⟩⟩
    refine ⟨subspaceActionHom σ J s,⟨s,⟨⟨g.val,(le_top.trans hU) hg⟩,hg,rfl⟩,rfl⟩,?_⟩
    apply (subspaceImageRepresentation_injective ρ I)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
