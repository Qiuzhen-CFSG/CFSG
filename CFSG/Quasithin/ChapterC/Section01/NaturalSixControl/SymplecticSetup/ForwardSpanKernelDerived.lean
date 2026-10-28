module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanFaithful
public import Theory.GroupTheory.ClassTwoIndexTwoDerived
/-!
# The second-kernel intersection retains the forward derived line

The faithful symmetric-six action on the forward span's central quotient
forces that quotient to have more than four elements. In a class-two group
with derived subgroup of order two, an index-two subgroup with trivial
derived subgroup would force the central quotient to have order at most
four. Thus intersection with the second vertex kernel preserves the entire
forward derived line. This is the derived-transfer input in the terminal
MS93 (5.12) configuration, using the central-extension argument of (3.10)(i).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
private theorem large_of_six_action {A : Type*} [Group A] [Finite A]
    (ρ : Equiv.Perm (Fin 6) →* MulAut A) (hρ : Function.Injective ρ) : 4<Nat.card A := by
  have hi := Nat.card_le_card_of_injective (f:=fun x => (ρ x).toEquiv)
    (MulEquiv.toEquiv_injective.comp hρ)
  change Nat.card (Equiv.Perm (Fin 6))≤Nat.card (Equiv.Perm A) at hi
  rw [Nat.card_perm,Nat.card_fin,Nat.card_perm] at hi
  have hs : Nat.factorial 6=720 := rfl
  rw [hs] at hi
  by_contra hn
  have hl : Nat.card A≤4 := by omega
  have hh := Nat.factorial_le hl
  have hf : Nat.factorial 4=24 := rfl
  omega

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The actual faithful symmetric action excludes central quotient order at most four. -/
theorem forward_span_center_index_gt_four
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    4<(center (localZSpan R (p.walk.getVert 2) (alpha R))).index := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  have hPQ : P≤Q R (alpha R) := (s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (hPQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  obtain ⟨ρ,hρ,_⟩ := s.exists_forward_span_faithful_symmetric_central_action h u hfull hb p
  change 4<(center P).index
  rw [index_eq_card]
  exact large_of_six_action ρ hρ
/-- Intersecting the forward span with the second kernel preserves its derived line. -/
theorem forward_span_kernel_derived_eq
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    ⁅P⊓Q R (p.walk.getVert 2),P⊓Q R (p.walk.getVert 2)⁆=⁅P,P⁆ := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let D := (Q R (p.walk.getVert 2)).subgroupOf P
  have hPQ : P≤Q R (alpha R) := (s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (hPQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hc := s.forward_span_central_quotient h u hfull hb p
  have hh := ClassTwo.commutator_eq_of_index_le_two_of_center_index_gt_four
    hc.2.2.1 hc.2.1 (s.forward_span_center_index_gt_four h u hfull hb p)
    D (s.forward_span_second_vertex_index_le_two h u hfull hb p)
  have hm := congrArg (fun N : Subgroup P => N.map P.subtype) hh
  have hDm : D.map P.subtype=P⊓Q R (p.walk.getVert 2) := by
    dsimp only [D,subgroupOf]
    rw [map_comap_eq,range_subtype]
  rw [map_commutator,hDm,map_subtype_commutator] at hm
  simpa only [P,inf_comm] using hm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The literal characteristic replacement supplies the terminal derived transfer. -/
theorem reducedSource_block_or_forward_span_kernel_derived_eq
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      let P := localZSpan r.radical (p.walk.getVert 2) (alpha r.radical)
      ⁅P⊓Q r.radical (p.walk.getVert 2),P⊓Q r.radical (p.walk.getVert 2)⁆=⁅P,P⁆ := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_span_kernel_derived_eq (reduced_nativeCentralLayer d hm r) _ hf hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
