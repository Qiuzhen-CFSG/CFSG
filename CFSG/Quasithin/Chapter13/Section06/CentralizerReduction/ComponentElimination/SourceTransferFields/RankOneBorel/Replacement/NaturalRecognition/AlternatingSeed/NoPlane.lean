module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.SourcePlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Normalizer
/-!
# The terminal A₄ contradiction on the original source plane

Once the whole residual image agrees with its constructed A₄ projection,
the natural constituent and component-fixed complement give the concrete
moved three-space. The original order-four plane constructed in SourcePlane
is invariant inside that space, contradicting its submodule classification.
Source: Aschbacher–Smith, 13.6.15, printed p.930.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection SourceContainment SourceContainment.LinearThree ChapterB.QuasisimpleSource
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
theorem false_of_borel_projection (s : A5Module.Marking L V) (K T : Subgroup G)
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    [IsElementaryAbelian 2 (WK K L T (A5Module.markedZ s) (A5Module.markedV s))]
    (I : Subrepresentation (componentRepresentation K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz))
    (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
    (hs : IsCompl I.toSubmodule (fixedSpace (wkRepresentation K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz)
      (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K)))
    (f : Lv L (A5Module.markedV s) →* plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K)
    (hf : ∀ l, (f l : Gplus K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz) =
      residualPlusMap K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz l)
    (hB : f.range.map e.groupEquiv.toMonoidHom = BinaryPermutation.AlternatingFiveBorel.B) : False := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let ρ := (wkRepresentation K L T z v hL hz).comp (residualPlusMap K L T z v hL hz)
  let J := fixedSpace (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K)
  let b : Lv L v →* alternatingGroup (Fin 5) := e.groupEquiv.toMonoidHom.comp f
  have hb : ∀ l, b l ∈ BinaryPermutation.AlternatingFiveBorel.B := by
    intro l
    rw [←hB]
    exact ⟨f l,⟨l,rfl⟩,rfl⟩
  let q := b.codRestrict BinaryPermutation.AlternatingFiveBorel.B hb
  have hq : Function.Surjective q := by
    intro x
    have hx : x.val ∈ f.range.map e.groupEquiv.toMonoidHom := hB.symm ▸ x.property
    obtain ⟨k,⟨l,rfl⟩,he⟩ := hx
    exact ⟨l,Subtype.ext he⟩
  have hJ : ∀ l (w : J), ρ l w=w := by
    intro l w
    change wkRepresentation K L T z v hL hz (residualPlusMap K L T z v hL hz l) w=w
    rw [←hf]
    exact w.property (f l)
  have hact : ∀ l (w : I.toSubmodule), ρ l w=
      (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5) (q l).val.val (e.linearEquiv w)) : Additive (WK K L T z v)) := by
    intro l w
    have he := congrArg e.linearEquiv.symm (e.intertwines (f l) w)
    rw [e.linearEquiv.symm_apply_apply] at he
    have ha := congrArg (fun x : I.toSubmodule => (x : Additive (WK K L T z v))) he
    change wkRepresentation K L T z v hL hz (f l) w = _ at ha
    rw [hf] at ha
    exact ha
  obtain ⟨P,hPdim,hPinv,hPcomm⟩ := source_plane s K T hL hz
  exact BinaryPermutation.AlternatingFiveBorel.no_invariant_plane_of_natural_split
    ρ I.toSubmodule J hs.sup_eq_top hJ e.linearEquiv q hq hact P hPinv hPcomm hPdim
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
