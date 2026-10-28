module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.Kernel
public import Theory.GroupAction.ModelConjugation

/-!
# Coordinates for the actual component omega action

Sylow conjugacy aligns the matrix root group with the prescribed component
Sylow, and elementary abelianness identifies that Sylow with its omega group.
The resulting equivalence intertwines the original conjugation action with
model automorphisms. In particular it embeds the relative centralizer of an
acting subgroup into the root fixed points of each of its elements.

Source: Aschbacher–Smith 16.5.1, printed p.1194, the linear outer-offender step.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G} {n : ℕ}

noncomputable def modelAction {F : Type*} [Field F]
    (h : StandardSetup T z L) (e : L ≃* PSL(2,F)) : T →* MulAut PSL(2,F) :=
  Theory.GroupAction.ModelConjugation.action T L h.sylow_normalizes e

theorem exists_root_coordinates {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentSylow T L)] (e₀ : L ≃* PSL(2,F)) :
    ∃ (e : L ≃* PSL(2,F))
      (b : componentOmegaInSylow T L ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F),
      ∀ u : componentOmegaInSylow T L, (e.symm (b u) : G) = ((u : T) : G) := by
  let U := Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F
  obtain ⟨S, hS⟩ := h.toCentralComponentSetup.exists_component_sylow
  let P := (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F).mapSurjective
    (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P S
  let e : PSL(2,F) ≃* L := e₀.symm.trans (MulAut.conj g)
  have he : U.map e.toMonoidHom = (S : Subgroup L) := by
    change U.map ((MulAut.conj g).toMonoidHom.comp e₀.symm.toMonoidHom) = _
    rw [← map_map, show U =
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F : Subgroup PSL(2,F))
      from (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F).symm]
    exact congrArg Sylow.toSubgroup hg
  let f := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  have hroot : U.map f = omegaOneAmbient (componentSylow T L) := by
    rw [omegaOneAmbient_eq_self]
    rw [show f = L.subtype.comp e.toMonoidHom from rfl, ← map_map, he, hS]
    rw [subgroupOf_map_subtype]
    rfl
  let b₀ : U ≃* omegaOneAmbient (componentSylow T L) :=
    (U.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hroot)
  let b : U ≃* componentOmegaInSylow T L :=
    b₀.trans (subgroupOfEquivOfLe ((omegaOneAmbient_le _).trans inf_le_left)).symm
  refine ⟨e.symm, b.symm, fun u => ?_⟩
  exact congrArg (fun v : componentOmegaInSylow T L => ((v : T) : G))
    (b.apply_symm_apply u)

theorem root_coordinates_action {F : Type*} [Field F]
    (h : StandardSetup T z L) (e : L ≃* PSL(2,F))
    (b : componentOmegaInSylow T L ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F)
    (hb : ∀ u : componentOmegaInSylow T L, (e.symm (b u) : G) = ((u : T) : G))
    (t : T) (u : componentOmegaInSylow T L) :
    modelAction h e t (b u) = b (omegaAction h t u) := by
  apply e.symm.injective
  apply Subtype.ext
  have hc := hb (omegaAction h t u)
  rw [omegaAction_apply] at hc
  change (e.symm (e (L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩
    (e.symm (b u)))) : G) = _
  rw [e.symm_apply_apply]
  change (t : G) * (e.symm (b u) : G) * (t : G)⁻¹ = _
  rw [hb]
  exact hc.symm

theorem modelAction_normalizes_root {F : Type*} [Field F]
    (h : StandardSetup T z L) (e : L ≃* PSL(2,F))
    (b : componentOmegaInSylow T L ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F)
    (hb : ∀ u : componentOmegaInSylow T L, (e.symm (b u) : G) = ((u : T) : G))
    (t : T) :
    (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F).map
      (modelAction h e t).toMonoidHom = Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F := by
  let : Finite (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F) :=
    Finite.of_equiv (componentOmegaInSylow T L) b.toEquiv
  apply eq_of_le_of_card_ge ?_ (card_map_of_injective (modelAction h e t).injective).ge
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨v, hv⟩ := b.surjective ⟨u, hu⟩
  have he : (b v : PSL(2,F)) = u := congrArg Subtype.val hv
  change modelAction h e t u ∈ _
  rw [← he, root_coordinates_action h e b hb]
  exact (b (omegaAction h t v)).property

theorem centralizer_card_le_root_fixed {F : Type*} [Field F] [Finite F]
    (h : StandardSetup T z L) (e : L ≃* PSL(2,F))
    (b : componentOmegaInSylow T L ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F)
    (hb : ∀ u : componentOmegaInSylow T L, (e.symm (b u) : G) = ((u : T) : G))
    (A : Subgroup T) (t : T) (ht : t ∈ A) :
    Nat.card (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) ≤
      Nat.card {u : Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F //
        modelAction h e t u = u} := by
  let f : (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) →
      {u : Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F // modelAction h e t u = u} :=
    fun x => ⟨b ⟨x, x.property.1⟩, by
      rw [root_coordinates_action h e b hb]
      congr 2
      apply Subtype.ext
      change t * (x : T) * t⁻¹ = x
      have hc := x.property.2 t ht
      rw [hc, mul_inv_cancel_right]⟩
  apply Nat.card_le_card_of_injective f
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun u : componentOmegaInSylow T L => (u : T))
    (b.injective (congrArg Subtype.val hxy))
end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
