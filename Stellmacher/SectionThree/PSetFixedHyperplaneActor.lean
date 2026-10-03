module

public import Stellmacher.SectionThree.PSetResidualConstituent
public import Stellmacher.SectionThree.PSetIrreducibleHyperplaneActor
public import Stellmacher.SectionThree.PSetResidualKernel

/-!
# Elementary actors fixing a hyperplane of a residual-active module

For a solvable member of PSet, a normal elementary abelian two-subgroup
with nontrivial residual action controls every elementary actor fixing a
hyperplane: the actor has index at most two over its two-core intersection.

Extract an actual irreducible subquotient on which the residual remains
nontrivial. The common fixed-index bound passes to this quotient. Its actual
actor image has order at most two by the irreducible form of the Section One
fixed-hyperplane argument. Local residual-kernel control transfers that bound
to the original actor modulo its intersection with the two-core.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40 / PDF p.30,
the application of (1.2) in (8.4). Residual nontriviality is retained explicitly;
neither faithfulness of the original module nor its irreducibility is assumed.
-/

namespace Stellmacher.SectionThree

public theorem pSet_fixed_hyperplane_actor_bound
    {H : Type*} [Group H] [Finite H]
    (S P C A : Subgroup H) (h : Hypotheses H S)
    (hP : P ∈ PSet (⊤ : Subgroup H) S) (hsolv : Group.IsSolvable P)
    (hCP : C ≤ P) (hCN : (C.subgroupOf P).Normal)
    (hC : IsElementaryAbelian 2 C) (hA : IsElementaryAbelian 2 A) (hAP : A ≤ P)
    (hres : ⁅twoResidualAmbient P, C⁆ ≠ ⊥)
    (hfixed : Nat.card C =
      2 * Nat.card (C ⊓ Subgroup.centralizer (A : Set H) : Subgroup H)) :
    (A ⊓ twoCoreAmbient P).relIndex A ≤ 2 := by
  obtain ⟨E, D, _hEC, _hDE, _hEN, _hDN, _hPE, _hPD, hN,
      action, _haction, hW, hirr, hescape, hbound⟩ :=
    exists_residual_nontrivial_irreducible_constituent P C A hCP hCN hC hAP hA hres hfixed
  let _ := hN
  let _ := hW
  let _ := hA
  have hcard := pSet_irreducible_fixed_hyperplane_actor_card_le_two
    S P A h hP hsolv hA hAP action hirr hescape hbound
  exact (pSet_actor_core_index_le_image_card S h P A hP hsolv hAP
    (IsElementaryAbelian.isPGroup 2 A) action hescape).trans hcard

end Stellmacher.SectionThree
