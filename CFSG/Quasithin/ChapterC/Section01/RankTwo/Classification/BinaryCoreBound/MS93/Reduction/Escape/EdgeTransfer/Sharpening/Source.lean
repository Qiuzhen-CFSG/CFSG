module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Sharpening
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The two edge-action branches in the binary source transfer

The source edge displacement is a nontrivial proper subgroup of the natural
subgroup of order eight. Its order is therefore two or four. In the first
case, its normality inside the actual edge kernel makes it central there,
and the source transfer conclusion follows immediately. In the second case,
the existing invariant-subgroup argument sharpens every neighboring natural
bound to the edge displacement times the fixed core.

This exhausts the edge-action cases needed for (4.2)(i), without assuming an
unconditional order-four equality or using escape or distance-four facts.
The final conditional assembly needs only `NeighborNaturalBound`; the owner
of the source theorem must still construct that extension bound. We do not
assert the stronger standalone `NeighborSharpening` in the order-two case,
where the source transfer conclusion has already been proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.2)(i), printed p.882. The cardinal-four argument on that page
suffices after the binary cardinal-two case is disposed of by centrality.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)

include hb modules

/-- An order-two displacement is central in the edge kernel, hence belongs
to its actual omega-center. Normality is relative to that kernel. -/
theorem edge_transfer_of_card_two (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅Z R a, Q R b⁆ ≤ Z R b := by
  let A := ⁅Z R a, Q R b⁆
  have hAZ : A ≤ Z R a :=
    (edge_commutator_le_natural hb modules a b ha hab).trans (U_le_Z a)
  have hAT : A ≤ Q R b := hAZ.trans (edge_Z_le_Q hb a b ha hab)
  let : (A.subgroupOf (Q R b)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    change g ∈ normalizer ((⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized R a (hg.2 a (adjacent_symm R hab))),
      mem_normalizer_iff_map_conj_eq.mp ((Q R b).le_normalizer hg)]
  have hc := central_of_normal_card_two (A.subgroupOf (Q R b))
    ((Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hcard)
  rw [edge_Z_eq_fixed hb modules a b ha hab]
  refine le_inf hAZ ?_
  intro x hx t ht
  exact congrArg Subtype.val ((mem_center_iff.mp
    (hc (show (⟨x, hAT hx⟩ : Q R b) ∈ A.subgroupOf (Q R b) from hx))) ⟨t, ht⟩)

/-- The complete list of possible binary edge displacement orders follows
from the actual natural embedding and the proper-commutator bound. -/
theorem edge_displacement_card_two_or_four (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2 ∨
      Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at a ha]; decide)
  have hU := edge_commutator_le_natural hb modules a b ha hab
  let : Finite (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  have hdvd := card_dvd_of_le hU
  rw [modules.natural.card_at a ha] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsmall := edge_displacement_card_le_four hb modules a b ha hab
  have hlarge := (one_lt_card_iff_ne_bot _).mpr (edge_commutator_ne_bot modules a b ha hab)
  omega

/-- Either the source transfer is already true, or all neighboring natural
bounds sharpen. No extension bound is required to prove this alternative. -/
theorem edge_transfer_or_neighbor_sharpening (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≤ Z R b ∨
      ∀ d : Vertex R, Adjacent R d b → Q R a ≠ Q R d →
        ⁅Z R d, Q R b⁆ ≤ U R a ⊔ fixedCore R a →
        ⁅Z R d, Q R b⁆ ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a := by
  rcases edge_displacement_card_two_or_four hb modules a b ha hab with htwo | hfour
  · exact Or.inl (edge_transfer_of_card_two hb modules a b ha hab htwo)
  · exact Or.inr (fun d hdb hne hnatural =>
      neighbor_sharpening_of_card_four hb modules a b d ha hab hdb hne hfour hnatural)

/-- Source (4.2)(i) conditional only on the neighboring natural bound.
The edge-action case split here discharges the former sharpening dependency;
the remaining natural bound must be supplied by the extension owner. -/
theorem edgeTransfer_of_neighbor_naturalBound (hext : NeighborNaturalBound geometry) :
    Escape.EdgeTransfer geometry := by
  intro a b ha hab hB
  rcases edge_transfer_or_neighbor_sharpening hb modules a b ha hab with hdone | hsharp
  · exact hdone
  · apply edge_transfer_of_span R hb modules a b ha hab
    apply edgeSpan_le_of_neighbor_steps modules a b ha hab hB
    · exact fun d hdb hne hBd => hext a b d ha hab hdb hne hBd
    · exact hsharp
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening
