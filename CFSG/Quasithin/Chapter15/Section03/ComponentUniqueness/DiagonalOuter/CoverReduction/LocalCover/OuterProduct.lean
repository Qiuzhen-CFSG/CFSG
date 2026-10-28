module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Action
public import Theory.GroupTheory.SylowCubicSupplement
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport

/-!
# The literal local product from the outer-order bound

Once C_I(L) lies in L, the actual marked outer action has kernel L. Its image
has order dividing twelve, and the opposite residual supplies an outer cubic.
Together with the image of the actual Sylow two-subgroup, this generates the
whole image. Pullback gives I=L∨D∨S; normalization gives the literal product.
This argument needs only the order bound, not realization of every projective
automorphism by the ambient group, and leaves the original marking unchanged.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

/-- The actual outer action, a cubic actor and the local Sylow give the literal product. -/
theorem product_of_marked_outer_order {L I D S : Subgroup G} {q : ℕ}
    (c : ProjectiveMarking L q) [Group.IsPerfect L]
    (hcore : pCore 2 L ≤ center L)
    (hLI : L ≤ I) (hDI : D ≤ I) (hSI : S ≤ I)
    (hIL : I ≤ normalizer (L : Set G))
    (hC : I ⊓ centralizer (L : Set G) ≤ L)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hSD : S ≤ normalizer (D : Set G))
    (hout : Nat.card (MulAut.Outer PSL(3,c.F)) ∣ 12)
    (hz : ∃ z ∈ D, c.Diagonal z) :
    (I : Set G) = (L : Set G) * (D : Set G) * (S : Set G) := by
  let f : I →* MulAut.Outer PSL(3,c.F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,c.F))).comp
      ((markedAction c).comp (inclusion hIL))
  have hker : f.ker = L.subgroupOf I := by
    ext i
    change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,c.F))
      (markedAction c ⟨i, hIL i.property⟩) = 1 ↔ (i : G) ∈ L
    exact (QuotientGroup.eq_one_iff _).trans
      (markedAction_inner_iff_mem c hcore hLI hIL hC i.property)
  let K := (L ⊔ D) ⊔ S
  have hKI : K ≤ I := sup_le (sup_le hLI hDI) hSI
  have hLK : L ≤ K := le_sup_left.trans le_sup_left
  have hDK : D ≤ K := le_sup_right.trans le_sup_left
  have hPK : (P : Subgroup I) ≤ K.subgroupOf I := by
    intro p hp
    exact (show S ≤ K from le_sup_right) (hP ▸ mem_map_of_mem I.subtype hp)
  obtain ⟨z, hzD, hzdiag⟩ := hz
  let zI : I := ⟨z, hDI hzD⟩
  have hz3 : zI ^ 3 = 1 := Subtype.ext (orderOf_eq_prime_iff.mp hzdiag.1).1
  have hzout : f zI ≠ 1 := by
    intro he
    obtain ⟨_, a, ha, hr⟩ := hzdiag
    apply ha
    rw [← markedAction_eq_of_realizes c ⟨z, hIL (hDI hzD)⟩ hr]
    exact (QuotientGroup.eq_one_iff _).mp he
  have hfz3 : orderOf (f zI) = 3 := orderOf_eq_prime
    (by rw [← map_pow, hz3, map_one]) hzout
  have he : K.subgroupOf I = ⊤ :=
    Theory.GroupTheory.eq_top_of_range_card_dvd_twelve f
      (f.range.card_subgroup_dvd_card.trans hout) P (K.subgroupOf I)
      (by rw [hker]; exact fun _ hx => hLK hx) hPK zI (hDK hzD) hfz3
  have hKIeq : K = I := by
    have hh := congrArg (Subgroup.map I.subtype) he
    rwa [map_subgroupOf_eq_of_le hKI, ← MonoidHom.range_eq_map, range_subtype] at hh
  have hSN : S ≤ normalizer (L ⊔ D : Subgroup G) :=
    (le_inf (hSI.trans hIL) hSD).trans (normalizer_inf_normalizer_le_normalizer_sup L D)
  rw [← hKIeq, coe_mul_of_right_le_normalizer_left (L ⊔ D) S hSN,
    coe_mul_of_right_le_normalizer_left L D (hDI.trans hIL)]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
