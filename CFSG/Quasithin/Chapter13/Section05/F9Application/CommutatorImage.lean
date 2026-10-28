module

public import CFSG.Quasithin.Chapter13.Section05.F9Application.SourceAction
public import Theory.Representation.BinaryOffender.ConjugationImage
/-!
# Literal source commutators in the natural coordinates

The actual conjugation map on the original V identifies the image of
[P,X] with the span of action differences on P. The same selected natural
coordinates and relative-normalizer permutation map occur on both sides.
For P=V this is the moved space used in 13.5.7; no commutator-space
identification is an input.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem image_commutator (P X:Subgroup G) (hP:P≤V)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V)) :
    image d ⁅P,X⁆=subspaceCommutator (naturalRepresentation (Fin 6)) (image d P)
      ((permutation d).comp (inclusion hX)).range := by
  let : Module (ZMod 2) (Additive (Multiplicative (natural (Fin 6)))) :=
    inferInstanceAs (Module (ZMod 2) (natural (Fin 6)))
  apply quotientImage_commutator (naturalRepresentation (Fin 6)) V P X
    (hX.trans inf_le_right) hP ((permutation d).comp (inclusion hX))
    d.coordinate.toMonoidHom d.coordinate.surjective
  intro x v
  exact (conjugation d (inclusion hX x) v).symm

theorem image_self : image d V=⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,hv⟩:=d.coordinate.surjective (Multiplicative.ofAdd w)
  exact (mem_image d V w).mpr ⟨v,v.property,congrArg Multiplicative.toAdd hv⟩

theorem image_commutator_self (X:Subgroup G)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V)) :
    image d ⁅V,X⁆=subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
      ((permutation d).comp (inclusion hX)).range := by
  rw [image_commutator d V X le_rfl hX,image_self d]
end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
