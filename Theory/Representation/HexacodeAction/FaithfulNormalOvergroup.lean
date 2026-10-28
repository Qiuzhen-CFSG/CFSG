module

public import Theory.Representation.HexacodeAction.NormalOvergroup

/-!
# The faithful actor above a prescribed normal even hexacode subgroup

Faithfulness of the whole original action suffices to extend an actual
normal even marking; no quotient-generation condition is needed. If a
literal Sylow has order sixteen, its image cannot lie in the even subgroup,
so this extension is an isomorphism with the full hexacode actor. The same
linear coordinates are retained on every vector and every original actor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.Codes
namespace Representation.Hexacode
open SixDimensional
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_embedding_of_normal_even_marking
    (ρ : Representation (ZMod 2) D V) (hfaith : Function.Injective ρ)
    (C : Subgroup D) [C.Normal]
    (c : C≃*HexEvenAutomorphisms) (e : V≃ₗ[ZMod 2]hexacode)
    (he : ∀ (g : C) (v : V), e (ρ g v)=evenAction (c g) (e v)) :
    ∃ f : D→*HexAutomorphisms, Function.Injective f ∧
      (∀ g : C, f g=(c g).val) ∧
      (∀ (g : D) (v : V), e (ρ g v)=action (f g) (e v)) := by
  let a := coordinateAction ρ e
  have ha (g : C) : a g = hexAction (c g).val := by
    apply LinearEquiv.ext
    intro w
    change e (ρ g (e.symm w)) = _
    rw [he, e.apply_symm_apply]
    rfl
  have himage : C.map a = evenBinaryImage := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨c ⟨g,hg⟩, (ha ⟨g,hg⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨b, rfl⟩ := c.surjective g
      exact ⟨b, b.property, ha b⟩
  have hmem (g : D) : a g ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    exact le_normalizer_map a ⟨g, by rw [C.normalizer_eq_top]; trivial, rfl⟩
  let j := a.codRestrict hexAction.range hmem
  let f := (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have hf (g : D) : hexAction (f g) = a g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro g h hgh
    apply coordinateAction_injective ρ e hfaith
    rw [← hf, ← hf, hgh]
  · intro g
    apply hexAction_injective
    rw [hf, ha]
  · intro g w
    have h := LinearEquiv.congr_fun (hf g) (e w)
    change action (f g) (e w) = e (ρ g (e.symm (e w))) at h
    simpa only [e.symm_apply_apply] using h.symm

/-- The original Sylow order distinguishes the full actor from its even subgroup. -/
theorem full_equivariant_of_sylow_sixteen [Finite D]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (C : Subgroup D) [C.Normal]
    (c : C≃*HexEvenAutomorphisms) (e : V≃ₗ[ZMod 2]hexacode)
    (he : ∀ (g : C) (v : V), e (ρ g v)=evenAction (c g) (e v))
    (S : Sylow 2 D) (hS : Nat.card S=16) :
    ∃ f : D≃*HexAutomorphisms, C.map f.toMonoidHom=hexSign.ker ∧
      ∀ (g : D) (v : V), e (ρ g v)=action (f g) (e v) := by
  obtain ⟨f,hfi,hfc,hact⟩ := exists_embedding_of_normal_even_marking
    ρ hf C c e he
  have hmap : C.map f=hexSign.ker := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      rw [hfc ⟨g,hg⟩]
      exact (c ⟨g,hg⟩).property
    · intro x hx
      obtain ⟨c,hc⟩ := c.surjective ⟨x,hx⟩
      exact ⟨c,c.property,(hfc c).trans (congrArg Subtype.val hc)⟩
  have hcontains : hexSign.ker≤f.range := hmap ▸ map_le_range f C
  have htwo : hexSign.ker.index=2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
    simp [Nat.card_eq_fintype_card]
  have hfull : f.range=⊤ := by
    have hh : f.range.index∣2 := htwo ▸ index_dvd_of_le hcontains
    rcases (Nat.dvd_prime Nat.prime_two).mp hh with h1 | h2
    · exact index_eq_one.mp h1
    · have hr := relIndex_mul_index hcontains
      rw [htwo,h2] at hr
      have hr1 : hexSign.ker.relIndex f.range=1 := by omega
      have heq : f.range=hexSign.ker := le_antisymm (relIndex_eq_one.mp hr1) hcontains
      have hc : Nat.card D=1080 := by
        rw [Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,heq]
        exact hexEven_card
      have hdiv := S.card_subgroup_dvd_card
      rw [hS,hc] at hdiv
      norm_num at hdiv
  let b := MulEquiv.ofBijective f ⟨hfi,MonoidHom.range_eq_top.mp hfull⟩
  exact ⟨b,hmap,hact⟩

end Representation.Hexacode
