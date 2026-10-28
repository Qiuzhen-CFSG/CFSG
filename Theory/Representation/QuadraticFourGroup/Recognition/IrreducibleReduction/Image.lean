module

public import Theory.Representation.QuadraticFourGroup.Recognition.Overgroup
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.Quotient
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Surviving components in faithful action images

A component with nontrivial homomorphic image centralizes the kernel. Its
perfectness then lifts centralizers exactly, by the three-subgroup lemma.
Consequently the four-group embeds, the component remains moved, and all the
quadratic four-group hypotheses pass to the faithful image of any irreducible
section on which the component survives.

A normal two-subgroup has a nonzero fixed vector on a nonzero binary module.
Irreducibility makes this fixed space the whole module, so faithfulness kills
the two-core. This also supplies the core input for the odd-transposition step.

Source: GLS, volume 2, Theorem 25.14, Step 2 (and Lemmas 3.8 and 9.8).
Existence of the section and lifting its orbit quotient are separate results.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Centralizers lift exactly when a component survives a homomorphism. -/
theorem IsComponent.centralizer_comap_of_map_ne_bot {L : Subgroup G}
    (hL : IsComponent G L) (f : G →* H) (hne : L.map f ≠ ⊥) :
    (centralizer (L.map f : Set H)).comap f = centralizer (L : Set G) := by
  let := hL.2
  have hker : ⁅f.ker, L⁆ = ⊥ := by
    rw [commutator_comm]
    exact (hL.normal_dichotomy f.ker).resolve_left
      (fun h => hne ((Subgroup.map_eq_bot_iff _).mpr h))
  apply le_antisymm
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    apply le_bot_iff.mp
    apply (commutator_mono (show
      ⁅(centralizer (L.map f : Set H)).comap f, L⁆ ≤ f.ker from ?_) le_rfl).trans
      hker.le
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact map_comap_le _ _
  · intro x hx
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx y hy)

end Theory.GroupTheory

namespace Representation.QuadraticFourGroup
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- A surviving component preserves every source hypothesis in a faithful image. -/
theorem Hypotheses.map_of_component_survives (h : Hypotheses ρ L B a)
    (f : G →* H) (hf : Function.Surjective f) (hne : L.map f ≠ ⊥)
    (σ : Representation (ZMod 2) H W) (hfaith : Function.Injective σ)
    (hq : FixesDisplacements (σ.comp f) a B) :
    Hypotheses σ (L.map f) (B.map f) (f a) := by
  have hcent := h.component.centralizer_comap_of_map_ne_bot f hne
  have hB : Function.Injective (f.comp B.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro b hb
    apply mem_bot.mpr
    apply Subtype.ext
    have hc : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hcent]
      change f b ∈ Subgroup.centralizer (L.map f : Set H)
      rw [show f b = 1 from hb]
      exact one_mem _
    have hb' : (b : G) ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨b.property, hc⟩
    change (b : G) = 1
    simpa only [h.centralizer, mem_bot] using hb'
  let eB : B ≃* B.map f := MulEquiv.ofBijective (f.subgroupMap B)
    ⟨fun x y he => hB (congrArg Subtype.val he), f.subgroupMap_surjective B⟩
  refine {
    faithful := hfaith
    component := (h.component.map_surjective f hf).resolve_left hne
    elementary := ?_
    card_four := (Nat.card_congr eB.toEquiv).symm.trans h.card_four
    mem := mem_map_of_mem f h.mem
    involution := ?_
    moves := ?_
    quadratic := ?_
    centralizer := ?_
  }
  · let := h.elementary
    exact IsElementaryAbelian.map f
  · exact (orderOf_injective (f.comp B.subtype) hB ⟨a, h.mem⟩).trans
      ((Subgroup.orderOf_coe ⟨a, h.mem⟩).symm.trans h.involution)
  · intro he
    apply h.moves
    have hcomp : f.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (f a)).toMonoidHom.comp f := by
      ext x
      simp [MulAut.conj_apply]
    have hm : (L.map (MulAut.conj a).toMonoidHom).map f = L.map f := by
      rw [map_map, hcomp, ← map_map]
      exact he
    exact (h.component.map_conj a).eq_of_map_eq h.component f hm (by rwa [hm])
  · rintro _ ⟨b, hb, rfl⟩ v
    exact hq b hb v
  · apply le_bot_iff.mp
    rintro b ⟨⟨c, hc, rfl⟩, hb⟩
    have hc' : c ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hcent]
      exact hb
    have he : c = 1 := by
      have : c ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hc, hc'⟩
      simpa only [h.centralizer, mem_bot] using this
    simp [he]

/-- A faithful irreducible finite-dimensional binary action has trivial two-core. -/
theorem twoCore_eq_bot_of_faithful_irreducible
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hfaith : Function.Injective ρ) : pCore 2 G = ⊥ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hp : IsPGroup (ringChar (ZMod 2)) (pCore 2 G) := by
    simpa only [ZMod.ringChar_zmod_n] using (pCore_isPGroup (p := 2) (G := G))
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (by simp only [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 2) ≠ 0) hp (ρ.comp (pCore 2 G).subtype)
  have hker : pCore 2 G ≤ ρ.ker := by
    apply le_ker_of_normal_invariants_ne_bot
    intro he
    have hv' : v ∈ invariants (ρ.comp (pCore 2 G).subtype) := hfix
    rw [he, Submodule.mem_bot] at hv'
    exact hv hv'
  exact le_bot_iff.mp (hker.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hfaith).le)

open BinaryOffender

/-- An actual irreducible section with surviving component has the required faithful image. -/
theorem Hypotheses.irreducibleSection_actionImage (h : Hypotheses ρ L B a)
    (σ : Representation (ZMod 2) G W) (hs : IsIrreducibleSection ρ σ)
    (hne : L.map (actionHom σ) ≠ ⊥) :
    Hypotheses (imageRepresentation σ) (actionSubgroup σ L) (actionSubgroup σ B)
      (actionHom σ a) ∧ (imageRepresentation σ).IsIrreducible := by
  refine ⟨h.map_of_component_survives (actionHom σ) σ.asGroupHom.rangeRestrict_surjective
    hne (imageRepresentation σ) (imageRepresentation_injective σ)
    (h.quadratic.irreducibleSection hs), ?_⟩
  exact (irreducible_comp_surjective_iff (actionHom σ)
    σ.asGroupHom.rangeRestrict_surjective (imageRepresentation σ)).mp hs.1

end Representation.QuadraticFourGroup

end
