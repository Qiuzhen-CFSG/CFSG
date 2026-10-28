module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.SectionDichotomy
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# The actual exchanged rank-one actor

The input retains the two component embeddings, their marked product, the
moving Sylow element, the normal component orbit, and the genuine SQTK
hypothesis. It asserts no representation-theoretic conclusion.

The product is centerless. Its centralizer embeds in the two-group quotient
supplied by the Sylow supplement, and hence lies in the trivial two-core.
This makes the orbit self-centralizing, the key to faithful section actions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.16(1),
printed p.952 (PDF p.969), and the component-kernel argument of F.9.18(6).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
universe u w

/-- Only the intrinsic group hypotheses of the exchanged PSL₂ branch.
The marked coordinate subgroups identify the original component embeddings. -/
structure ExchangedActor (𝒦 : GroupClass.{u}) (D : Type u) [Group D] [Finite D]
    (F : Type w) [Field F] [Finite F] [CharP F 2] (n : ℕ) where
  degree_ge : 2 ≤ n
  field_card : Nat.card F = 2 ^ n
  component : Subgroup D
  second : Subgroup D
  orbit : Subgroup D
  sylow : Sylow 2 D
  component_isComponent : Theory.GroupTheory.IsComponent D component
  second_isComponent : Theory.GroupTheory.IsComponent D second
  component_le : component ≤ orbit
  second_le : second ≤ orbit
  orbit_eq : orbit = conjugateSpanBy component (sylow : Subgroup D)
  orbit_normal : orbit.Normal
  generated : orbit ⊔ (sylow : Subgroup D) = ⊤
  twoCore : pCore 2 D = ⊥
  sqtk : IsSQTK 𝒦 D
  mover : sylow
  moved : component.map (MulAut.conj (mover : D)).toMonoidHom = second
  distinct : second ≠ component
  productEquiv : orbit ≃* (PSL(2,F) × PSL(2,F))
  first_mark : (component.subgroupOf orbit).map productEquiv.toMonoidHom =
    (⊤ : Subgroup PSL(2,F)).prod ⊥
  second_mark : (second.subgroupOf orbit).map productEquiv.toMonoidHom =
    (⊥ : Subgroup PSL(2,F)).prod ⊤

/-- A centerless normal subgroup supplemented by a two-group is
self-centralizing when the whole group has trivial two-core. -/
theorem centralizer_eq_bot_of_centerless_supplement {D : Type*} [Group D] (L : Subgroup D) [L.Normal]
    (T : Sylow 2 D) (hg : L ⊔ (T : Subgroup D) = ⊤)
    (hz : center L = ⊥) (hcore : pCore 2 D = ⊥) :
    centralizer (L : Set D) = ⊥ := by
  let C := centralizer (L : Set D)
  let f := (QuotientGroup.mk' L).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro c hc
    have hcL : (c : D) ∈ L := (QuotientGroup.eq_one_iff (N := L) (x := (c : D))).mp hc
    have hcZ : (⟨c, hcL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      apply Subtype.ext
      exact c.property l l.property
    have hc1 : (c : D) = 1 := congrArg Subtype.val (show (⟨c, hcL⟩ : L) = 1 from by simpa [hz] using hcZ)
    exact mem_bot.mpr (Subtype.ext hc1)
  have hp : IsPGroup 2 C :=
    (quotient_isPGroup_of_sup_eq_top (T : Subgroup D) L T.isPGroup' (by rwa [sup_comm])).of_injective f hf
  have hle : C ≤ pCore 2 D := le_sSup ⟨inferInstance, hp⟩
  exact bot_unique (hcore ▸ hle)


/-- The actual characteristic-two projective product has trivial center. -/
theorem center_eq_bot_of_product_equiv {D F : Type*} [Group D] [Field F] [CharP F 2]
    (L : Subgroup D) (e : L ≃* (PSL(2,F) × PSL(2,F))) : center L = ⊥ := by
  have hz : center (PSL(2,F) × PSL(2,F)) = ⊥ := by
    rw [Subgroup.center_prod, Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]
    ext x
    simp
  apply eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x, hx⟩).property
  change e x ∈ center (PSL(2,F) × PSL(2,F)) at he
  rw [hz, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

/-- The literal component orbit in the source actor is self-centralizing. -/
theorem ExchangedActor.centralizer_eq_bot
    {𝒦 : GroupClass.{u}} {D : Type u} [Group D] [Finite D]
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (d : ExchangedActor 𝒦 D F n) : centralizer (d.orbit : Set D) = ⊥ := by
  let : d.orbit.Normal := d.orbit_normal
  exact centralizer_eq_bot_of_centerless_supplement d.orbit d.sylow d.generated
    (center_eq_bot_of_product_equiv d.orbit d.productEquiv) d.twoCore

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
