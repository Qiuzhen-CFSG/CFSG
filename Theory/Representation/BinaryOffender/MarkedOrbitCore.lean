module
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.PGroupCore
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms

/-!
# A Sylow-fixed generating subspace

For a faithful action, a Sylow-fixed subspace whose conjugates span the module
forces the normal two-core to be trivial. Under a surjective change of actors,
the very same marker and orbit span descend. Coprime normalizer lifting retains
the literal image of the prescribed two-subgroup.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Faithfulness and an orbit-generating Sylow-fixed marker exclude a normal
two-core. No offender-generation hypothesis is used. -/
theorem twoCore_eq_bot_of_sylow_fixed_span (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) (S : Sylow 2 G) (P : Submodule (ZMod 2) V)
    (hfix : P ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : G) (v : V), v ∈ P ∧ ρ g v = w} = ⊤) :
    pCore 2 G = ⊥ := by
  have hQS : pCore 2 G ≤ S := pCore_isPGroup.le_sylow_of_normal S
  have hPQ : P ≤ fixedSpace ρ (pCore 2 G) := fun v hv a => hfix hv ⟨a, hQS a.property⟩
  have htotal : (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ (pCore 2 G) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, v, hv, rfl⟩
    exact (fixedSpace_stable_of_normal ρ (pCore 2 G) (mem_top g) v).mpr (hPQ hv)
  apply bot_unique
  intro g hg
  apply hfaith
  ext v
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_mk, map_one, Module.End.one_apply] using
    (htotal (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V))) ⟨g, hg⟩

/-- The same vectors generate the same orbit span after a surjection of actors. -/
theorem orbit_span_comp_surjective (σ : Representation (ZMod 2) D V)
    (f : G →* D) (hf : Function.Surjective f) (P : Submodule (ZMod 2) V) :
    Submodule.span (ZMod 2) {w | ∃ (g : G) (v : V), v ∈ P ∧ σ (f g) v = w} =
      Submodule.span (ZMod 2) {w | ∃ (d : D) (v : V), v ∈ P ∧ σ d v = w} := by
  congr 1
  ext w
  constructor
  · rintro ⟨g, v, hv, he⟩
    exact ⟨f g, v, hv, he⟩
  · rintro ⟨d, v, hv, he⟩
    obtain ⟨g, rfl⟩ := hf d
    exact ⟨g, v, hv, he⟩

/-- The faithful action image has trivial two-core using the image of the
same compatible Sylow and the same orbit-generating marker. -/
theorem actionImage_twoCore_eq_bot_of_sylow_fixed_span [Finite G]
    (ρ : Representation (ZMod 2) G V) (S : Sylow 2 G) (P : Submodule (ZMod 2) V)
    (hfix : P ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : G) (v : V), v ∈ P ∧ ρ g v = w} = ⊤) :
    pCore 2 (actionImage ρ) = ⊥ := by
  let S' := S.mapSurjective (f := actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  apply twoCore_eq_bot_of_sylow_fixed_span (imageRepresentation ρ)
    (imageRepresentation_injective ρ) S' P
  · change P ≤ fixedSpace (imageRepresentation ρ) (actionSubgroup ρ (S : Subgroup G))
    rw [fixedSpace_actionSubgroup]
    exact hfix
  · rw [← orbit_span_comp_surjective (imageRepresentation ρ) (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective P]
    simpa only [imageRepresentation_actionHom] using hspan

/-- Coprime kernel correction descends a normalizer condition for the literal
image `J.map f`, with no identification with an intrinsic Thompson subgroup. -/
theorem normalizer_fixes_map_of_coprime_kernel [Finite G]
    (σ : Representation (ZMod 2) D V) (f : G →* D) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) (J : Subgroup G) (hJ : IsPGroup 2 J)
    (P : Submodule (ZMod 2) V)
    (hfix : ∀ g ∈ normalizer (J : Set G), ∀ v ∈ P, σ (f g) v = v) :
    ∀ d ∈ normalizer (J.map f : Set D), ∀ v ∈ P, σ d v = v := by
  let : Fact (IsPGroup 2 J) := ⟨hJ⟩
  rw [normalizer_map_eq_of_coprime_kernel 2 J f hf hker.coprime_two_left]
  rintro _ ⟨g, hg, rfl⟩ v hv
  exact hfix g hg v hv

end Representation.BinaryOffender
