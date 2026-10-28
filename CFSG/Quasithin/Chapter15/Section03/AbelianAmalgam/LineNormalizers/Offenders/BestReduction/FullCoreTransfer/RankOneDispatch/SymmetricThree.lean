module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Models
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The actual binary natural action in the symmetric-three branch

A faithful action that splits into a fixed space and a two-dimensional moved
space remains faithful on that plane. Coordinates embed the actor in GL₂(2),
and the order six makes this embedding an isomorphism. The binary GL–SL
comparison constructs the action intertwiner used by the model section.

Source: Aschbacher–Smith, B.5.6(2), printed p.105, and the proof of 15.3.67,
printed p.1154 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {W : Type v}
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem natural_of_faithful_binary_plane
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 2) (hc : Nat.card D = 6) :
    Nonempty (ActionEquiv ρ (linearNatural BinaryField.two 2)) := by
  let X := Fin 2 → ZMod 2
  let e : W ≃ₗ[ZMod 2] X := LinearEquiv.ofFinrankEq W X (by
    simpa only [X, Module.finrank_pi, Fintype.card_fin] using hd)
  let c := LinearMap.GeneralLinearGroup.congrLinearEquiv e
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X
  let s := BinaryLinear.OuterCyclic.slEquivLinear 2
  let f := s.symm.toMonoidHom.comp (l.toMonoidHom.comp (c.toMonoidHom.comp ρ.asGroupHom))
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    exact congrArg Units.val (c.injective (l.injective (s.symm.injective he)))
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi, by rw [hc, Atlas.card_sl_two]; norm_num⟩
  let a := MulEquiv.ofBijective f hbij
  refine ⟨⟨a, e, ?_⟩⟩
  intro g v
  have he : s (a g) = l (c (ρ.asGroupHom g)) := s.apply_symm_apply _
  have he' := congrArg (fun t : X ≃ₗ[ZMod 2] X => t (e v)) he
  change e (ρ g v) = Matrix.mulVec (a g).val (e v)
  change Matrix.mulVec (a g).val (e v) = e (ρ g (e.symm (e v))) at he'
  simpa only [e.symm_apply_apply] using he'.symm

/-- B.5.6(2) supplies the degree-one SL₂ model, with its actual moved space. -/
theorem symmetricThree_model
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (h : SymmetricThreeCase ρ) : RankOneModel ρ := by
  let s := MovedSection.ofNormal ρ (⊤ : Subgroup D)
  have hfs : Function.Injective s.space.toRepresentation := by
    intro g k he
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ moved ρ ⊤ ⊔ ρ.invariants := by rw [h.decomposition.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    change ρ g (x + y) = ρ k (x + y)
    rw [map_add, map_add, hy g, hy k]
    exact congrArg (fun z : W => z + y)
      (congrArg Subtype.val (LinearMap.congr_fun he ⟨x, hx⟩))
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule = 2 := h.dimension
  have hc : Nat.card D = 6 := by
    rw [Nat.card_congr h.equiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨e⟩ := natural_of_faithful_binary_plane s.space.toRepresentation hfs hd hc
  let U : Subrepresentation (ρ.comp e.groupEquiv.symm.toMonoidHom) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule _ hv⟩
  refine RankOneModel.linearTwo BinaryField.two e.groupEquiv
    ⟨U, e.linearEquiv.toLinearMap, e.linearEquiv.surjective, ?_, ?_, ?_⟩
  · intro g v
    change e.linearEquiv (s.space.toRepresentation (e.groupEquiv.symm g) v) =
      linearNatural BinaryField.two 2 g (e.linearEquiv v)
    rw [e.intertwines, e.groupEquiv.apply_symm_apply]
  · intro g v hv
    have hv0 : v = 0 := e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    rw [hv0, map_zero]
  · intro g v
    exact Submodule.subset_span ⟨e.groupEquiv.symm g, Subgroup.mem_top _, v,
      Submodule.mem_top, rfl⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
