module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup
public import Theory.GroupAction.RankTwoCosetGeometry.Reorientation
public import Theory.GroupAction.CubicTree.ArcEquiv

/-!
# Both orientations of the original cubic source action

Reverse the endpoint maps and use the equivariant coset graph isomorphism.
This preserves the entire primitive cubic action and its two-perfectness,
without choosing a different completion. Short-arc regularity transports,
and a first singular arc starting in the second vertex class becomes one
starting in the first. The actual track normalizer argument can therefore
use its source orientation, while final recognition retains both possible
endpoint orders.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(2.12) and Sections 5--6, printed pp.383--384 and 393--395.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup Theory.GroupTheory RankTwoAmalgam Subgroup.CosetGeometry
open Theory.GroupAction.CubicTree SimpleGraph SimpleGraph.BasedWalk
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private def reverseAmalgam {L D R : Type*} [Group L] [Group D] [Group R]
    (α : RankTwoAmalgam L D R) : RankTwoAmalgam R D L := ⟨α.right,α.left⟩

private theorem reverse_primitive {L D R : Type*} [Group L] [Group D] [Group R]
    {α : RankTwoAmalgam L D R} (h : PrimitiveCubic α) :
    PrimitiveCubic (reverseAmalgam α) := by
  refine ⟨⟨h.sylow.right_injective,h.sylow.left_injective,
    h.sylow.right_sylow,h.sylow.left_sylow⟩,?_,h.right_index,h.left_index⟩
  intro N hL hR
  exact h.faithful N hR hL

private def reverseInclusionIso (A B : Subgroup G) :
    Iso (reverseAmalgam (inclusionAmalgam A B)) (inclusionAmalgam B A) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (inf_comm A B)
  right := MulEquiv.refl _
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Reversing the two local groups retains the actual cubic tree action. -/
theorem CubicTreeAction.swap (h : CubicTreeAction F) :
    CubicTreeAction (RankTwo.swapFamily F) := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  refine ⟨fun i => h.finite (!i),?_,?_,?_⟩
  · change F true ⊔ F false = ⊤
    simpa only [sup_comm] using h.generated
  · exact (reverse_primitive h.primitive).of_iso (reverseInclusionIso _ _)
  · exact (RankTwo.swapGraphIso F).isTree_iff.mp h.tree

/-- Reorientation preserves two-perfectness of the very same acting group. -/
theorem TwoPerfectTreeAction.swap (h : TwoPerfectTreeAction F) :
    TwoPerfectTreeAction (RankTwo.swapFamily F) :=
  ⟨h.toCubicTreeAction.swap,h.twoPerfect⟩

/-- Short-arc regularity transports without changing the acting group. -/
theorem shortRegular_swap {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p) :
    ∀ (k : ℕ) (v : RankTwo.Vertex (RankTwo.swapFamily F))
      (p : BasedWalk (RankTwo.graph (RankTwo.swapFamily F)) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p := by
  let e := RankTwo.swapGraphIso F
  have hn : ∀ v, Function.Bijective (e.toHom.mapNeighborSet v) := by
    intro v
    exact (e.mapNeighborSet v).bijective
  intro k v p hk hp
  obtain ⟨v,rfl⟩ := e.surjective v
  obtain ⟨q,rfl⟩ := (BasedWalk.map_bijective e.toHom hn k v).surjective p
  exact (rightRegular_graphIso_iff e (RankTwo.swapVertex_smul F) q).2
    (hshort k v q hk ((BasedWalk.nonbacktracking_map_iff e.toHom
      (fun v => (hn v).1) q).1 hp))

/-- A first singular arc in the second vertex class becomes a first singular
arc in the first class after reversing the source orientation. -/
theorem singular_swap {s : ℕ} {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hv : v.type = true)
    (hp : p.Nonbacktracking) (hs : ¬ RightRegular (A := G) p) :
    ∃ (w : RankTwo.Vertex (RankTwo.swapFamily F))
      (q : BasedWalk (RankTwo.graph (RankTwo.swapFamily F)) s w),
      w.type = false ∧ q.Nonbacktracking ∧ ¬ RightRegular (A := G) q := by
  let e := RankTwo.swapGraphIso F
  refine ⟨e v,p.map e.toHom,?_,?_,?_⟩
  · change (RankTwo.swapVertex F v).type = false
    rw [RankTwo.swapVertex_type,hv]
    rfl
  · exact (BasedWalk.nonbacktracking_map_iff e.toHom
      (fun v => (e.mapNeighborSet v).injective) p).2 hp
  · exact fun h => hs ((rightRegular_graphIso_iff e (RankTwo.swapVertex_smul F) p).1 h)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
