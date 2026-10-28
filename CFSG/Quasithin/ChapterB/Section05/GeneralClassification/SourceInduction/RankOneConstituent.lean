module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# An alternating-five constituent excludes a natural SL₂ section

The alternating natural module has no invariants and is irreducible. Its
image in any module therefore lies in the moved space. Projection onto
the quotient of that space by its central part remains injective. The
known cubic fixed-vector obstruction then excludes a natural SL₂ section
over every field of characteristic two, preserving both actor markings.

This comparison supplies the last B.5 row exclusion in the original
residual Thompson argument, using the actual earlier13.3.2 constituent.
Source: Aschbacher–Smith14.7.67(4), p.1070; B.5.1, pp.99–103.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace RankOneConstituent

private theorem natural_faithful : Function.Injective (alternatingNatural 5) :=
  (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)).comp
    (alternatingGroup (Fin 5)).subtype_injective

private theorem natural_fixed_zero (v : BinaryPermutation.natural (Fin 5))
    (h : ∀ a : alternatingGroup (Fin 5), alternatingNatural 5 a v = v) : v = 0 := by
  have hz := invariants_eq_bot_of_faithful_irreducible (alternatingNatural 5)
    natural_faithful (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
  exact (show v ∈ (⊥ : Submodule (ZMod 2) _) from hz ▸ h)

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- A genuine alternating-five constituent in the moved space cannot have
an SL₂ natural central section, irrespective of the field or central extension. -/
theorem not_linearTwo_of_alternating_submodule (s : MovedSection ρ L)
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2))
    (f : alternatingGroup (Fin 5) →* L) (hf : Function.Injective f)
    (i : BinaryPermutation.natural (Fin 5) →+ s.space.toSubmodule)
    (hi : Function.Injective i)
    (hact : ∀ a v, i (alternatingNatural 5 a v) = s.space.toRepresentation (f a) (i v)) :
    False := by
  let j : BinaryPermutation.natural (Fin 5) →+ (Fin 2 → F.Carrier) :=
    e.linearEquiv.toAddMonoidHom.comp (s.central.toSubmodule.mkQ.toAddMonoidHom.comp i)
  have hj : Function.Injective j := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hvq : s.central.toSubmodule.mkQ (i v) = 0 :=
      e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hvq
    rw [s.central_eq] at hm
    apply natural_fixed_zero
    intro a
    apply hi
    exact (hact a v).trans (hm (f a))
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection
    (e.groupEquiv.toMonoidHom.comp f) (e.groupEquiv.injective.comp hf) j hj
  intro a v
  change e.linearEquiv (s.central.toSubmodule.mkQ (i (alternatingNatural 5 a v))) = _
  rw [hact]
  exact e.intertwines (f a) (s.central.toSubmodule.mkQ (i v))

/-- Any alternating-five submodule is already inside the literal moved
space. No reducedness assertion for the whole moved space is used. -/
theorem alternating_image_le_moved (s : MovedSection ρ L)
    (f : alternatingGroup (Fin 5) →* L)
    (i : BinaryPermutation.natural (Fin 5) →+ V)
    (hact : ∀ a v, i (alternatingNatural 5 a v) = ρ (f a) (i v)) :
    ∀ v, i v ∈ s.space := by
  let j := i.toZModLinearMap 2
  let P : Subrepresentation (alternatingNatural 5) := {
    toSubmodule := s.space.toSubmodule.comap j
    apply_mem_toSubmodule := by
      intro a v hv
      change i (alternatingNatural 5 a v) ∈ s.space.toSubmodule
      rw [hact]
      exact s.space.apply_mem_toSubmodule (f a) hv }
  let hi : Representation.IsIrreducible (alternatingNatural 5) :=
    BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)
  rcases hi.eq_bot_or_eq_top P with hP | hP
  · have htriv (a : alternatingGroup (Fin 5)) (v : BinaryPermutation.natural (Fin 5)) :
        alternatingNatural 5 a v = v := by
      have hm : alternatingNatural 5 a v - v ∈ P := by
        change i (alternatingNatural 5 a v - v) ∈ s.space.toSubmodule
        rw [map_sub,hact,s.space_eq]
        exact Submodule.subset_span ⟨f a,(f a).property,i v,Submodule.mem_top,rfl⟩
      rw [hP] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    have he : alternatingNatural 5 a = alternatingNatural 5 1 := by
      apply LinearMap.ext
      intro v
      simpa only [map_one, Module.End.one_apply] using htriv a v
    exact (ha (natural_faithful he)).elim
  · intro v
    have hv : v ∈ P := hP ▸ (show v ∈ (⊤ : Subrepresentation (alternatingNatural 5)) from trivial)
    exact hv

/-- The constituent need only be embedded in the full original module. -/
theorem not_linearTwo_of_alternating_injection (s : MovedSection ρ L)
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2))
    (f : alternatingGroup (Fin 5) →* L) (hf : Function.Injective f)
    (i : BinaryPermutation.natural (Fin 5) →+ V) (hi : Function.Injective i)
    (hact : ∀ a v, i (alternatingNatural 5 a v) = ρ (f a) (i v)) : False := by
  let j : BinaryPermutation.natural (Fin 5) →+ s.space.toSubmodule := {
    toFun := fun v => ⟨i v,alternating_image_le_moved s f i hact v⟩
    map_zero' := Subtype.ext i.map_zero
    map_add' _ _ := Subtype.ext (map_add i _ _) }
  exact not_linearTwo_of_alternating_submodule s F e f hf j
    (fun _ _ h => hi (congrArg Subtype.val h))
    (fun a v => Subtype.ext (hact a v))

end RankOneConstituent
end CFSG.Quasithin.ChapterB.QuasisimpleSource
