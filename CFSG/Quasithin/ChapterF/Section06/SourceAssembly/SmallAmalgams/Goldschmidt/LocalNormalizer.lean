module

public import Theory.GroupTheory.Amalgam.LocalCover
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup

/-!
# The normalizer argument for the actual cubic source action

The common Sylow overlap has index three in both finite local groups. Thus
a selected order-three subgroup at each endpoint covers the local cosets.
If both normalize a subgroup of the overlap, local coverage forces that
subgroup into the common normal core, which is trivial by primitivity.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.3),
printed p.380, as applied throughout Sections 4--6.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The local order-three subgroups give an edge-transitive normalizer;
faithfulness then kills the normalized subgroup of the literal overlap. -/
theorem CubicTreeAction.normalized_overlap_eq_bot_of_three_subgroups
    (h : CubicTreeAction F) (K : Subgroup G) (hKT : K ≤ F false ⊓ F true)
    (X : Subgroup (F false)) (Y : Subgroup (F true))
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3)
    (hXK : X.map (F false).subtype ≤ normalizer (K : Set G))
    (hYK : Y.map (F true).subtype ≤ normalizer (K : Set G)) : K = ⊥ := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  obtain ⟨P, hP⟩ := h.primitive.sylow.left_sylow
  obtain ⟨Q, hQ⟩ := h.primitive.sylow.right_sylow
  have hcompA := Subgroup.three_complement_of_two_group_index_three
    (inclusionAmalgam (F false) (F true)).left.range X
    (hP ▸ P.isPGroup') h.primitive.left_index hX
  have hcompB := Subgroup.three_complement_of_two_group_index_three
    (inclusionAmalgam (F false) (F true)).right.range Y
    (hQ ▸ Q.isPGroup') h.primitive.right_index hY
  apply Subgroup.local_pair_normalized_eq_bot (F false) (F true) K
    (normalizer (K : Set G)) h.generated h.common_core_eq_bot hKT le_rfl
  · intro a ha
    obtain ⟨⟨x,t⟩, he, _⟩ := hcompA.existsUnique (⟨a,ha⟩ : F false)
    obtain ⟨d, hd⟩ := t.property
    refine ⟨x.1.1, hXK ⟨x.1,x.2,rfl⟩, d.1, d.2, ?_⟩
    have he' := congrArg (fun z : F false => (z : G)) he
    have hd' := congrArg (fun z : F false => (z : G)) hd
    exact he'.symm.trans (congrArg (fun z : G => x.1.1 * z) hd'.symm)
  · intro b hb
    obtain ⟨⟨y,t⟩, he, _⟩ := hcompB.existsUnique (⟨b,hb⟩ : F true)
    obtain ⟨d, hd⟩ := t.property
    refine ⟨y.1.1, hYK ⟨y.1,y.2,rfl⟩, d.1, d.2, ?_⟩
    have he' := congrArg (fun z : F true => (z : G)) he
    have hd' := congrArg (fun z : F true => (z : G)) hd
    exact he'.symm.trans (congrArg (fun z : G => y.1.1 * z) hd'.symm)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
