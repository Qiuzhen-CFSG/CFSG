module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Transport
public import Theory.Representation.QuadraticFourGroup.Recognition.Overgroup

/-!
# Source hypotheses in a surviving component image

For a component with nontrivial homomorphic image, the component commutator
dichotomy reflects centralization. Thus the full preimage of the image
centralizer is the original centralizer. The source four-group remains
injective and has trivial component centralizer in the image. Distinct
components have distinct nontrivial images, so the involution still moves
the component. The displacement identity passes to actual subquotients.

We also transport the hypotheses when an automorphism fixing the four-group
pointwise moves the chosen component. This handles the component marking
in an arbitrary two-factor model. Source: GLS, volume 2, Theorem 25.14,
Step 2, using the genuine component calculus of Chapter 3.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup.SectionReduction
variable {G Q : Type*} [Group G] [Group Q]

theorem component_commutator_reflects (L A : Subgroup G) (hL : IsComponent G L)
    (f : G →* Q) (hne : L.map f ≠ ⊥) (hc : ⁅L.map f, A.map f⁆ = ⊥) :
    ⁅L, A⁆ = ⊥ := by
  rcases hL.commutator_dichotomy A with h | h
  · exact h
  · have hle : L ≤ ⁅L, A⁆ := h ▸ le_iSup_conjugates L A
    have hm : L.map f ≤ ⊥ := by
      simpa only [map_commutator, hc] using (map_mono (f := f) hle)
    exact (hne (le_bot_iff.mp hm)).elim

theorem component_centralizer_comap (L : Subgroup G) (hL : IsComponent G L)
    (f : G →* Q) (hne : L.map f ≠ ⊥) :
    (centralizer (L.map f : Set Q)).comap f = centralizer (L : Set G) := by
  apply le_antisymm
  · let A := (centralizer (L.map f : Set Q)).comap f
    have hc : ⁅L.map f, A.map f⁆ = ⊥ := by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
      exact map_comap_le _ _
    have hc' := component_commutator_reflects L A hL f hne hc
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hc'
    exact hc'
  · intro x hx
    rw [mem_comap, mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx l hl)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

theorem fourGroup_map_injective (h : Hypotheses ρ L B a)
    (f : G →* Q) (hne : L.map f ≠ ⊥) : Function.Injective (f.comp B.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro b hb
  have hbcent : (b : G) ∈ centralizer (L : Set G) := by
    rw [← component_centralizer_comap L h.component f hne]
    change f b ∈ centralizer (L.map f : Set Q)
    rw [show f b = 1 from hb]
    exact one_mem _
  have hb' : (b : G) ∈ B ⊓ centralizer (L : Set G) := ⟨b.property, hbcent⟩
  rw [h.centralizer, mem_bot] at hb'
  exact mem_bot.mpr (Subtype.ext hb')

theorem fourGroup_image_centralizer (h : Hypotheses ρ L B a)
    (f : G →* Q) (hne : L.map f ≠ ⊥) :
    B.map f ⊓ centralizer (L.map f : Set Q) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨⟨b, hb, rfl⟩, hc⟩
  have hbcent : b ∈ centralizer (L : Set G) := by
    rw [← component_centralizer_comap L h.component f hne]
    exact hc
  have hb' : b ∈ B ⊓ centralizer (L : Set G) := ⟨hb, hbcent⟩
  rw [h.centralizer, mem_bot] at hb'
  simp only [hb', map_one, mem_bot]

end Representation.QuadraticFourGroup.SectionReduction

namespace Representation.QuadraticFourGroup
open scoped IsMulCommutative
variable {G Q V U : Type*} [Group G] [Group Q]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

theorem Hypotheses.map_component (h : Hypotheses ρ L B a)
    (e : MulAut G) (he : ∀ b ∈ B, e b = b) :
    Hypotheses ρ (L.map e.toMonoidHom) B a := by
  have hea : e a = a := he a h.mem
  have hc : (MulAut.conj a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, hea]
  refine { h with
    component := h.component.map_equiv e
    moves := ?_
    centralizer := ?_
  }
  · intro hm
    apply h.moves
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [map_map, hc] using hm
  · apply le_bot_iff.mp
    rintro b ⟨hb, hbcent⟩
    have hbc : b ∈ Subgroup.centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      apply e.injective
      simpa only [map_mul, he b hb] using
        (mem_centralizer_iff.mp hbcent (e l) (mem_map_of_mem e.toMonoidHom hl))
    have hm : b ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hbc⟩
    rwa [h.centralizer] at hm

theorem Hypotheses.conjugate_component (h : Hypotheses ρ L B a) (b : B) :
    Hypotheses ρ (L.map (MulAut.conj (b : G)).toMonoidHom) B a := by
  let := h.elementary
  apply h.map_component
  intro c hc
  have hcomm : (b : G) * c = c * (b : G) :=
    congrArg Subtype.val (mul_comm b (⟨c, hc⟩ : B))
  simp only [MulAut.conj_apply, hcomm, mul_inv_cancel_right]

theorem Hypotheses.faithful_section_image (h : Hypotheses ρ L B a)
    (f : G →* Q) (hf : Function.Surjective f)
    (τ : Representation (ZMod 2) Q U) (hτ : Function.Injective τ)
    (hs : IsIrreducibleSection ρ (τ.comp f)) (hne : L.map f ≠ ⊥) :
    Hypotheses τ (L.map f) (B.map f) (f a) := by
  have hB := SectionReduction.fourGroup_map_injective h f hne
  refine {
    faithful := hτ
    component := (h.component.map_surjective f hf).resolve_left hne
    elementary := ?_
    card_four := ?_
    mem := mem_map_of_mem f h.mem
    involution := ?_
    moves := ?_
    quadratic := ?_
    centralizer := SectionReduction.fourGroup_image_centralizer h f hne
  }
  · let := h.elementary
    exact IsElementaryAbelian.map f
  · let e : B ≃ B.map f := Equiv.ofBijective (f.subgroupMap B)
      ⟨fun x y hxy => hB (congrArg Subtype.val hxy), f.subgroupMap_surjective B⟩
    exact (Nat.card_congr e).symm.trans h.card_four
  · have he := orderOf_injective (f.comp B.subtype) hB ⟨a, h.mem⟩
    exact he.trans ((Subgroup.orderOf_coe (⟨a, h.mem⟩ : B)).symm.trans h.involution)
  · intro he
    apply h.moves
    apply (h.component.map_conj a).eq_of_map_eq h.component f
    · have hc : f.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (f a)).toMonoidHom.comp f := by
        ext x
        simp [MulAut.conj_apply]
      simpa only [map_map, hc] using he
    · have hc : f.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (f a)).toMonoidHom.comp f := by
        ext x
        simp [MulAut.conj_apply]
      rw [map_map, hc, ← map_map, he]
      exact hne
  · exact (h.quadratic.irreducibleSection hs).image f

end Representation.QuadraticFourGroup

end
