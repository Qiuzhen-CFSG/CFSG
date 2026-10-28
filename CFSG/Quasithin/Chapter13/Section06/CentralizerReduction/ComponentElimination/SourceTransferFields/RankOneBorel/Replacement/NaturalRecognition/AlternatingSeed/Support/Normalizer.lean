module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Moved

/-!
# The ambient permutation action on the original alternating-five constituent

Normality of C puts the ambient action on [W,C] in the linear normalizer
of its A₅ action. The genuine single-copy normalizer calculation identifies
that normalizer with S₅. The resulting homomorphism extends the originally
specified C-to-A₅ marking and uses its original linear coordinates.
Source: Aschbacher–Smith B.4.2(5) and13.6.15, printed pp.86 and930.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
open ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

private def transportedHom (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5)) :
    D →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))) where
  toFun g :=
    (e.linearEquiv.symm.trans
      ((LinearEquiv.ofBijective (U.toRepresentation g)
        (U.toRepresentation.apply_bijective g)).trans e.linearEquiv)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro w
    change Multiplicative.ofAdd (e.linearEquiv
      (U.toRepresentation 1 (e.linearEquiv.symm w.toAdd))) = w
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro w
    change Multiplicative.ofAdd (e.linearEquiv
      (U.toRepresentation (g*h) (e.linearEquiv.symm w.toAdd))) =
      Multiplicative.ofAdd (e.linearEquiv (U.toRepresentation g
        (e.linearEquiv.symm (e.linearEquiv
          (U.toRepresentation h (e.linearEquiv.symm w.toAdd))))))
    rw [e.linearEquiv.symm_apply_apply, map_mul, Module.End.mul_apply]

private theorem transportedHom_on_component (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5)) (c : C) :
    transportedHom U e c =
      BinaryPermutation.naturalMulAction (Fin 5) (e.groupEquiv c) := by
  apply MulEquiv.ext
  intro w
  change Multiplicative.ofAdd (e.linearEquiv
    (U.toRepresentation c (e.linearEquiv.symm w.toAdd))) =
    Multiplicative.ofAdd (alternatingNatural 5 (e.groupEquiv c) w.toAdd)
  have he := e.intertwines c (e.linearEquiv.symm w.toAdd)
  rw [e.linearEquiv.apply_symm_apply] at he
  exact congrArg Multiplicative.ofAdd he

private theorem transportedHom_component (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5)) :
    C.map (transportedHom U e) = (alternatingGroup (Fin 5)).map
      (BinaryPermutation.naturalMulAction (Fin 5)) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨e.groupEquiv ⟨c, hc⟩, (e.groupEquiv ⟨c, hc⟩).property,
      (transportedHom_on_component U e ⟨c, hc⟩).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := e.groupEquiv.surjective ⟨a, ha⟩
    refine ⟨c, c.property, ?_⟩
    rw [transportedHom_on_component, hc]

/-- A full invariant copy has an ambient S₅ action extending its original
A₅ marking, using precisely the supplied linear equivalence. -/
theorem exists_permutation_action [C.Normal] (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5)) :
    ∃ r : D →* Equiv.Perm (Fin 5),
      (∀ c : C, r c = (e.groupEquiv c : Equiv.Perm (Fin 5))) ∧
      ∀ g w, e.linearEquiv (U.toRepresentation g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w) := by
  let n := BinaryPermutation.naturalMulAction (Fin 5)
  have hn : Function.Injective n :=
    BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
  let f := transportedHom U e
  have hf (g : D) : f g ∈ n.range := by
    have hnorm : f g ∈ normalizer (C.map f : Set _) := by
      apply Subgroup.le_normalizer_map f
      exact ⟨g, by rw [Subgroup.normalizer_eq_top]; exact mem_top _, rfl⟩
    rw [transportedHom_component] at hnorm
    exact BinaryPermutation.normalizer_alternatingFive_naturalMulAction_le_range hnorm
  let r := (MonoidHom.ofInjective hn).symm.toMonoidHom.comp (f.codRestrict n.range hf)
  have hr (g : D) : n (r g) = f g :=
    congrArg Subtype.val ((MonoidHom.ofInjective hn).apply_symm_apply ⟨f g, hf g⟩)
  refine ⟨r, ?_, ?_⟩
  · intro c
    apply hn
    exact (hr c).trans (transportedHom_on_component U e c)
  · intro g w
    have he := congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (hr g) (Multiplicative.ofAdd (e.linearEquiv w)))
    change BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w) =
      e.linearEquiv (U.toRepresentation g (e.linearEquiv.symm (e.linearEquiv w))) at he
    rw [e.linearEquiv.symm_apply_apply] at he
    exact he.symm

/-- The map acts on the original constituent, whose ambient invariance comes
from its equality with the canonical moved space. -/
theorem exists_permutation_action_of_eq_moved [C.Normal]
    (I : Subrepresentation (ρ.comp C.subtype))
    (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
    (hm : I.toSubmodule = moved ρ C) :
    ∃ r : D →* Equiv.Perm (Fin 5),
      (∀ c : C, r c = (e.groupEquiv c : Equiv.Perm (Fin 5))) ∧
      ∀ g (w : I.toSubmodule), ρ g (w : V) =
        (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5)
          (r g) (e.linearEquiv w)) : V) := by
  let s := MovedSection.ofNormal ρ C
  have hs : s.space.toSubmodule = I.toSubmodule := s.space_eq.trans hm.symm
  let f := LinearEquiv.ofEq s.space.toSubmodule I.toSubmodule hs
  let a : ActionEquiv (s.space.toRepresentation.comp C.subtype) (alternatingNatural 5) :=
    { groupEquiv := e.groupEquiv
      linearEquiv := f.trans e.linearEquiv
      intertwines g w := e.intertwines g (f w) }
  obtain ⟨r, hr, ha⟩ := exists_permutation_action s.space a
  refine ⟨r, hr, ?_⟩
  intro g w
  have he := congrArg e.linearEquiv.symm (ha g (f.symm w))
  change e.linearEquiv.symm (e.linearEquiv (f (s.space.toRepresentation g (f.symm w)))) =
    e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5) (r g)
      (e.linearEquiv (f (f.symm w)))) at he
  rw [e.linearEquiv.symm_apply_apply, f.apply_symm_apply] at he
  exact congrArg (fun x : I.toSubmodule => (x : V)) he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
