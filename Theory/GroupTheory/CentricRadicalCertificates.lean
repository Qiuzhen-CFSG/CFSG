module

public import Theory.GroupTheory.CentricRadicalObstructions
public import Theory.GroupTheory.PGroup.Omega

/-!
# Transport and pointwise tests for centric radical certificates

The intrinsic radical condition is invariant under ambient group isomorphism:
normalizer actions, inner automorphisms and the p-core all transport through
the induced subgroup isomorphism. Thus local exclusions may be checked on
conjugacy representatives.

The quotient-action tests express triviality through element displacements.
For the Frattini quotient of `G/C`, containment in `C Φ(G)` suffices, using
surjectivity of `G → G/C`. This avoids constructing quotient automorphisms
explicitly in finite witness calculations.

Source: elementary isomorphism transport and the functoriality of the
Frattini subgroup under surjective homomorphisms; the radical obstruction
itself is proved in `CentricRadicalObstructions`.
-/

namespace Subgroup
variable {G G' : Type*} [Group G] [Group G']

/-- Transport the intrinsic radical condition through an ambient isomorphism. -/
public theorem intrinsic_radical_map (U : Subgroup G) (e : G ≃* G') (p : ℕ)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) :
    (U.map e.toMonoidHom).normalizerMonoidHom.range ⊓
      pCore p (MulAut (U.map e.toMonoidHom)) ≤
      (MulAut.conj : U.map e.toMonoidHom →* MulAut (U.map e.toMonoidHom)).range := by
  let V := U.map e.toMonoidHom
  let f : U ≃* V := e.subgroupMap U
  let E := MulAut.congr f
  intro a ha
  obtain ⟨g, hg⟩ := ha.1
  have hnorm : (normalizer (V : Set G')).comap e.toMonoidHom =
      normalizer (U : Set G) := by
    rw [comap_normalizer_eq_of_surjective V e.surjective]
    exact congrArg (fun H : Subgroup G => normalizer (H : Set G))
      (comap_map_eq_self_of_injective e.injective U)
  have hn : e.symm (g : G') ∈ normalizer (U : Set G) := by
    rw [← hnorm]
    change e (e.symm (g : G')) ∈ normalizer (V : Set G')
    simpa only [e.apply_symm_apply] using g.property
  let g₀ : normalizer (U : Set G) := ⟨e.symm g, hn⟩
  have hact : E (U.normalizerMonoidHom g₀) = V.normalizerMonoidHom g := by
    ext x
    change e (e.symm (g : G') * e.symm (x : G') * (e.symm (g : G'))⁻¹) =
      (g : G') * (x : G') * (g : G')⁻¹
    simp
  have hpc : U.normalizerMonoidHom g₀ ∈ pCore p (MulAut U) := by
    have hm : E (U.normalizerMonoidHom g₀) ∈
        (pCore p (MulAut U)).map E.toMonoidHom := by
      rw [pCore_map_iso p E, hact, hg]
      exact ha.2
    obtain ⟨b, hb, hbe⟩ := hm
    exact E.injective hbe ▸ hb
  obtain ⟨u, hu⟩ := hrad ⟨⟨g₀, rfl⟩, hpc⟩
  refine ⟨f u, ?_⟩
  rw [← hg, ← hact, ← hu]
  apply MulEquiv.ext
  intro x
  change f u * x * (f u)⁻¹ = f (u * f.symm x * u⁻¹)
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
end Subgroup


namespace Subgroup
variable {G : Type*} [Group G]

/-- A pointwise displacement test for trivial action on a characteristic quotient. -/
public theorem quotientAut_eq_one_of_displacements (C : Subgroup G) [C.Characteristic] (a : MulAut G)
    (h : ∀ x, x⁻¹ * a x ∈ C) : quotientAut C a = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' C (a y) = QuotientGroup.mk' C y
  exact (QuotientGroup.eq.mpr (h y)).symm

/-- Displacements into `C Φ(G)` imply trivial action on the Frattini quotient of `G/C`. -/
public theorem quotientAut_frattini_eq_one_of_displacements (C : Subgroup G) [C.Characteristic] (a : MulAut G)
    (h : ∀ x, x⁻¹ * a x ∈ C ⊔ frattini G) :
    quotientAut (frattini (G ⧸ C)) (quotientAut C a) = 1 := by
  have hle : C ⊔ frattini G ≤ (frattini (G ⧸ C)).comap (QuotientGroup.mk' C) := by
    refine sup_le ?_ (frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective C))
    intro x hx
    change QuotientGroup.mk' C x ∈ frattini (G ⧸ C)
    have hxq : QuotientGroup.mk' C x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact (frattini (G ⧸ C)).one_mem
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini (G ⧸ C)) x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective C y
  rw [quotientAut_apply_mk, quotientAut_apply_mk]
  change QuotientGroup.mk' (frattini (G ⧸ C)) (QuotientGroup.mk' C (a z)) =
    QuotientGroup.mk' (frattini (G ⧸ C)) (QuotientGroup.mk' C z)
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  simpa only [mem_comap, map_mul, map_inv] using hle (h z)
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- Displacements in the embedded Frattini subgroup test the restricted action. -/
public theorem quotientAut_frattini_characteristic_eq_one_of_displacements
    (C : Subgroup G) [C.Characteristic] (a : MulAut G)
    (h : ∀ x : C, (x : G)⁻¹ * a x ∈ (frattini C).map C.subtype) :
    quotientAut (frattini C) (MulAut.characteristic C a) = 1 := by
  apply quotientAut_eq_one_of_displacements
  intro x
  obtain ⟨y, hy, he⟩ := h x
  have he' : y = x⁻¹ * MulAut.characteristic C a x := Subtype.ext he
  exact he' ▸ hy

/-- Pointwise tests for the paired characteristic Frattini obstruction. -/
public theorem mem_of_intrinsic_radical_of_characteristic_frattini_displacements
    [Finite G] {p : ℕ} (U : Subgroup G) (hU : IsPGroup p U)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (C : Subgroup U) [C.Characteristic] (g : normalizer (U : Set G))
    (hc : ∀ x : C, (x : U)⁻¹ * U.normalizerMonoidHom g x ∈
      (frattini C).map C.subtype)
    (hq : ∀ x : U, x⁻¹ * U.normalizerMonoidHom g x ∈ C ⊔ frattini U) :
    (g : G) ∈ U :=
  mem_of_intrinsic_radical_of_characteristic_frattini_actions U hU hcent hrad C g
    (quotientAut_frattini_characteristic_eq_one_of_displacements C _ hc)
    (quotientAut_frattini_eq_one_of_displacements C _ hq)

/-- An outside normalizer element with trivial Frattini actions on omega and
its quotient. This is expressed by displacements in the original group. -/
@[expose] public def HasOmegaFrattiniWitness (p : ℕ) (U : Subgroup G) : Prop :=
  ∃ g : normalizer (U : Set G), (g : G) ∉ U ∧
    (∀ x : omega₁ U (p := p), (x : U)⁻¹ * U.normalizerMonoidHom g x ∈
      (frattini (omega₁ U (p := p))).map (omega₁ U (p := p)).subtype) ∧
    ∀ x : U, x⁻¹ * U.normalizerMonoidHom g x ∈ omega₁ U (p := p) ⊔ frattini U

/-- A centric intrinsic radical p-subgroup has no such outside witness. -/
public theorem not_hasOmegaFrattiniWitness_of_intrinsic_radical
    [Finite G] {p : ℕ} (U : Subgroup G) (hU : IsPGroup p U)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) : ¬ HasOmegaFrattiniWitness p U := by
  rintro ⟨g, hg, hc, hq⟩
  let : (omega₁ U (p := p)).Characteristic := omega₁_characteristic U
  exact hg (mem_of_intrinsic_radical_of_characteristic_frattini_displacements
    U hU hcent hrad (omega₁ U (p := p)) g hc hq)

end Subgroup
