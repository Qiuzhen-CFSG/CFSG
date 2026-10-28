module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupAction.FixedLineIrreducibility

/-!
# The fixed-line argument on the actual `U/Z`

The image of `Z_S` in `U/Z` has order two, and its `H`-conjugates
necessarily generate the quotient because `U = ⟨Z_S^H⟩`. The commutator
inclusion `[Z_S,T] ≤ Z` from 15.3.48 makes this line fixed by `T`.
If the paired actors from 15.3.56(7) have exactly this fixed line,
the full Sylow group has the same fixed subgroup. The fixed-line theorem
then proves irreducibility.

Thus the final lemma discharges the generation and line-size inputs of
15.3.57(1). Its paired-actor fixed-point input still belongs to 15.3.56;
no recognition or extraspecial-group assertion is assumed implicitly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1148.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G] (Z ZS : Subgroup G)
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The generating orbit in the literal quotient is forced by the definition of `U`. -/
theorem distinguishedLine_generates :
    let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    closure {w : VectorQuotient Z ZS |
      ∃ h : centralizerH Z, ∃ z ∈ distinguishedLine Z ZS, h • z = w} = ⊤ := by
  let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  let q := QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))
  let C := closure {w : VectorQuotient Z ZS |
    ∃ h : centralizerH Z, ∃ z ∈ distinguishedLine Z ZS, h • z = w}
  let D := (C.comap q).map (closureU Z ZS).subtype
  have hUD : closureU Z ZS ≤ D := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, z, hz, rfl⟩
    let zU : closureU Z ZS := ⟨z, ZS_le_closureU Z ZS hz⟩
    let hH : centralizerH Z := ⟨h, hh⟩
    let u : closureU Z ZS := ⟨h * z * h⁻¹,
      (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS hh) z).mp zU.property⟩
    refine mem_map.mpr ⟨u, ?_, rfl⟩
    change q u ∈ C
    apply Subgroup.subset_closure
    refine ⟨hH, q zU, mem_map.mpr ⟨zU, hz, rfl⟩, ?_⟩
    exact quotientAction_mk Z ZS hH zU
  apply top_unique
  intro w _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w
  obtain ⟨u', hu', heq⟩ := hUD u.property
  have heq' : u' = u := Subtype.ext heq
  exact heq' ▸ hu'

/-- The image of the source four-group has order two, using the actual kernel `Z`. -/
theorem card_distinguishedLine [Finite G] (hZZS : Z ≤ ZS)
    (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4) :
    Nat.card (distinguishedLine Z ZS) = 2 := by
  let U := closureU Z ZS
  let A := ZS.subgroupOf U
  let N := Z.subgroupOf U
  have hNA : N ≤ A := fun _ h => hZZS h
  have hcA : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (ZS_le_closureU Z ZS)).toEquiv).trans hZS
  have hcN : Nat.card (N.subgroupOf A) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv]
    exact (Nat.card_congr
      (subgroupOfEquivOfLe (hZZS.trans (ZS_le_closureU Z ZS))).toEquiv).trans hZ
  have hi : N.relIndex A = Nat.card (distinguishedLine Z ZS) := by
    simpa only [QuotientGroup.ker_mk', distinguishedLine, A, N, U] using
      (Subgroup.relIndex_ker (K := A) (QuotientGroup.mk' N))
  have hc := (N.subgroupOf A).card_mul_index
  change Nat.card (N.subgroupOf A) * N.relIndex A = Nat.card A at hc
  rw [hcN, hi, hcA] at hc
  omega

/-- The earlier centrality modulo `Z` fixes the distinguished line pointwise. -/
theorem distinguishedLine_le_fixedPoints (T : Subgroup G) (hcomm : ⁅ZS, T⁆ ≤ Z) :
    let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    distinguishedLine Z ZS ≤ FixedPoints.subgroup (T.subgroupOf (centralizerH Z))
      (VectorQuotient Z ZS) := by
  let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  change distinguishedLine Z ZS ≤ FixedPoints.subgroup (T.subgroupOf (centralizerH Z))
    (VectorQuotient Z ZS)
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
  intro t
  change quotientAction Z ZS t.val (QuotientGroup.mk' _ u) = QuotientGroup.mk' _ u
  rw [quotientAction_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (t.val : G) * (u : G) * (t.val : G)⁻¹ / (u : G) ∈ Z
  have hc : ⁅(t.val : G), (u : G)⁆ ∈ Z := by
    rw [Subgroup.commutator_comm] at hcomm
    exact hcomm (Subgroup.commutator_mem_commutator t.property hu)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hc

/-- A subgroup of the Sylow actors with this fixed line determines the full fixed subgroup. -/
theorem fixedPoints_eq_distinguishedLine (T : Subgroup G) (hcomm : ⁅ZS, T⁆ ≤ Z)
    (J : Subgroup (centralizerH Z)) (hJT : J ≤ T.subgroupOf (centralizerH Z))
    (hJ : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS) :
    let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    FixedPoints.subgroup (T.subgroupOf (centralizerH Z)) (VectorQuotient Z ZS) =
      distinguishedLine Z ZS := by
  let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  refine le_antisymm ?_ (distinguishedLine_le_fixedPoints Z ZS T hcomm)
  rw [← hJ]
  intro w hw j
  exact hw ⟨j.val, hJT j.property⟩

/-- The irreducibility assertion of 15.3.57(1), conditional on the paired-actor calculation 15.3.56(7). -/
theorem lemma_15_3_57_one_of_pair_fixed_line [Finite G]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (hcomm : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (J : Subgroup (centralizerH Z))
    (hJT : J ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hJ : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS) :
    let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    ∀ D : Subgroup (VectorQuotient Z ZS),
      (∀ h : centralizerH Z, ∀ w ∈ D, h • w ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  let R := (T : Subgroup G).subgroupOf (centralizerH Z)
  have hRp : IsPGroup 2 R :=
    T.isPGroup'.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hfix := fixedPoints_eq_distinguishedLine Z ZS T hcomm J hJT hJ
  have hc : Nat.card (FixedPoints.subgroup R (VectorQuotient Z ZS)) = 2 := by
    rw [hfix]
    exact card_distinguishedLine Z ZS hZZS hZ hZS
  have hgen : closure {w : VectorQuotient Z ZS |
      ∃ h : centralizerH Z, ∃ z ∈ FixedPoints.subgroup R (VectorQuotient Z ZS),
        h • z = w} = ⊤ := by
    rw [hfix]
    exact distinguishedLine_generates Z ZS
  exact irreducible_of_fixed_line_generates R hRp hc hgen

end CFSG.Quasithin.Chapter15.Section03.Nonabelian
