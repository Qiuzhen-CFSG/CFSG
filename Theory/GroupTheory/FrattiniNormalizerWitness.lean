module

public import Theory.GroupTheory.CentricRadicalCertificates

/-!
# Normalizer witnesses acting trivially on the Frattini quotient

A normalizer element outside a subgroup whose action on its Frattini quotient
is trivial rules out that subgroup in a Frattini survivor census. Such witnesses
transport through every ambient group isomorphism: displacements transport
through the induced subgroup isomorphism, which preserves the Frattini subgroup.

Source: functoriality of the Frattini subgroup under surjective homomorphisms.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Trivial quotient action is equivalent to displacement into the kernel. -/
public theorem quotientAut_eq_one_iff_displacements (C : Subgroup G) [C.Characteristic]
    (a : MulAut G) : quotientAut C a = 1 ↔ ∀ x, x⁻¹ * a x ∈ C := by
  constructor
  · intro h x
    have he := DFunLike.congr_fun h (QuotientGroup.mk' C x)
    rw [quotientAut_apply_mk] at he
    exact QuotientGroup.eq.mp he.symm
  · exact quotientAut_eq_one_of_displacements C a

/-- An outside normalizer element acting trivially on the Frattini quotient. -/
@[expose] public def HasFrattiniNormalizerWitness (U : Subgroup G) : Prop :=
  ∃ g : normalizer (U : Set G), (g : G) ∉ U ∧
    quotientAut (frattini U) (U.normalizerMonoidHom g) = 1

/-- Frattini normalizer witnesses transport through ambient isomorphisms. -/
public theorem HasFrattiniNormalizerWitness.map (U : Subgroup G) (e : G ≃* H)
    (hw : U.HasFrattiniNormalizerWitness) :
    (U.map e.toMonoidHom).HasFrattiniNormalizerWitness := by
  obtain ⟨g, hg, ha⟩ := hw
  let V := U.map e.toMonoidHom
  let f := e.subgroupMap U
  let g' : normalizer (V : Set H) :=
    ⟨e g, U.le_normalizer_map e.toMonoidHom (mem_map_of_mem _ g.property)⟩
  refine ⟨g', ?_, ?_⟩
  · rintro ⟨u, hu, he⟩
    exact hg (e.injective he ▸ hu)
  · apply quotientAut_eq_one_of_displacements
    intro x
    have hx := (quotientAut_eq_one_iff_displacements (frattini U) _).mp ha (f.symm x)
    have hm := frattini_le_comap_frattini_of_surjective (φ := f.toMonoidHom) f.surjective hx
    have he : f ((f.symm x)⁻¹ * U.normalizerMonoidHom g (f.symm x)) =
        x⁻¹ * V.normalizerMonoidHom g' x := by
      apply Subtype.ext
      change e ((e.symm (x : H))⁻¹ * ((g : G) * e.symm x * (g : G)⁻¹)) =
        (x : H)⁻¹ * (e g * x * (e g)⁻¹)
      simp
    exact he ▸ hm

/-- The survivor condition is exactly absence of an outside witness. -/
public theorem not_hasFrattiniNormalizerWitness_iff (U : Subgroup G) :
    ¬ U.HasFrattiniNormalizerWitness ↔
      ∀ g : normalizer (U : Set G),
        quotientAut (frattini U) (U.normalizerMonoidHom g) = 1 → (g : G) ∈ U := by
  classical
  simp only [HasFrattiniNormalizerWitness, not_exists, not_and]
  exact ⟨fun h g ha => Classical.byContradiction (fun hn => h g hn ha),
    fun h g hn ha => hn (h g ha)⟩

/-- Existence of a Frattini normalizer witness is invariant under isomorphisms. -/
public theorem hasFrattiniNormalizerWitness_map_iff (U : Subgroup G) (e : G ≃* H) :
    (U.map e.toMonoidHom).HasFrattiniNormalizerWitness ↔ U.HasFrattiniNormalizerWitness := by
  constructor
  · intro h
    have hm := h.map _ e.symm
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    simpa only [Subgroup.map_map, he, Subgroup.map_id] using hm
  · exact HasFrattiniNormalizerWitness.map U e

end Subgroup
