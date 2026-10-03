module

public import Theory.Character.ModularBlock.RelativeTransferBasic
public import Theory.Character.ModularBlock.SubgroupBrauerHom

/-!
# Fixed-coset recovery of subgroup Brauer restriction

For a p-subgroup Q contained in H, over characteristic p coefficients,
Brauer restriction of the relative transfer of a central H-algebra element
is its identity-coset contribution whenever every other Q-fixed coset term
has zero restriction. Conjugating on the left by Q does not change any
coefficient indexed by C_G(Q). The resulting Q-invariant coefficient sum
therefore reduces to its fixed points by p-group orbit cancellation.
Representative independence identifies the identity contribution with the
original subgroup embedding. This coefficient calculation is the transfer
input to the maximal-support form of Brauer's third main theorem.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BrauerThirdMain

open Subgroup

universe u v

attribute [local instance] Fintype.ofFinite

/-- Multiplying a conjugating representative on the left by an element of the
subgroup leaves the `Q`-Brauer restriction unchanged. -/
theorem subgroupRestriction_conjugationMap_q_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (q : Q) (H : Subgroup G) (g : G)
    (b : MonoidAlgebra R H) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H ((q : G) * g) b) =
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H g b) := by
  ext h
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    DefectSupport.subgroupCentralizerRestriction_apply]
  have hconj :
      RelativeTransferBrauer.conjugationMap R H ((q : G) * g) b =
        MonoidAlgebra.of R G (q : G) *
          RelativeTransferBrauer.conjugationMap R H g b *
            MonoidAlgebra.of R G (q : G)⁻¹ := by
    rw [RelativeTransferBrauer.conjugationMap_apply,
      RelativeTransferBrauer.conjugationMap_apply]
    simp only [map_mul, mul_inv_rev, mul_assoc]
  rw [hconj]
  let a : MonoidAlgebra R G :=
    RelativeTransferBrauer.conjugationMap R H g b
  have hcomm : (q : G) * (h : G) = (h : G) * (q : G) := by
    exact Subgroup.mem_centralizer_iff.mp h.property (q : G) q.property
  change
    (MonoidAlgebra.of R G (q : G) * a *
      MonoidAlgebra.of R G (q : G)⁻¹).coeff (h : G) = a.coeff (h : G)
  rw [show MonoidAlgebra.of R G (q : G)⁻¹ =
      MonoidAlgebra.single (q : G)⁻¹ 1 by rfl,
    MonoidAlgebra.coeff_mul_single_apply,
    show MonoidAlgebra.of R G (q : G) =
      MonoidAlgebra.single (q : G) 1 by rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp only [one_mul, mul_one]
  congr 1
  calc
    (q : G)⁻¹ * ((h : G) * ((q : G)⁻¹)⁻¹) =
        (q : G)⁻¹ * ((h : G) * (q : G)) := by simp
    _ = (q : G)⁻¹ * ((q : G) * (h : G)) := by rw [hcomm]
    _ = (h : G) := by simp

/-! ## A fixed-coset transfer calculation -/

/-- Brauer restriction of a relative transfer is the identity term when all
nonidentity fixed cosets have zero restriction.  The hypothesis is stated at
the coefficient level so that the theorem is independent of block theory. -/
theorem subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
    {p : ℕ} [Fact p.Prime]
    {R : Type u} {G : Type v} [CommRing R] [CharP R p]
    [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (H : Subgroup G) (hQH : Q ≤ H) (b : MonoidAlgebra R H)
    (hbCenter : b ∈ Set.center (MonoidAlgebra R H))
    (hterm : ∀ q : G ⧸ H,
      q ∈ MulAction.fixedPoints Q (G ⧸ H) →
      q ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H q.out b) = 0) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.relativeTransfer R H b) =
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.subgroupSubtypeMap R H b) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let : Fintype (MulAction.fixedPoints Q (G ⧸ H)) :=
    Fintype.ofFinite _
  ext x
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    DefectSupport.subgroupCentralizerRestriction_apply]
  let ev : MonoidAlgebra R G →+ R := (Finsupp.applyAddHom (x : G)).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  change ev (RelativeTransferBrauer.relativeTransfer R H b) =
    ev (RelativeTransferBrauer.subgroupSubtypeMap R H b)
  rw [RelativeTransferBrauer.relativeTransfer, map_sum]
  let F : (G ⧸ H) → R := fun q ↦
    (RelativeTransferBrauer.conjugationMap R H q.out b).coeff (x : G)
  have hFinv : ∀ q : Q, ∀ c : G ⧸ H, F (q • c) = F c := by
    intro q c
    change F ((q : G) • c) = F c
    have hout : RelativeTransferBrauer.conjugationMap R H
        ((q : G) • c).out b =
        RelativeTransferBrauer.conjugationMap R H ((q : G) * c.out) b := by
      apply RelativeTransferBrauer.conjugationMap_out_eq_of_mk_eq
        H ((q : G) • c) ((q : G) * c.out)
      · simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H (q : G) c)
      · exact hbCenter
    change (RelativeTransferBrauer.conjugationMap R H ((q : G) • c).out b).coeff (x : G) =
      (RelativeTransferBrauer.conjugationMap R H c.out b).coeff (x : G)
    rw [hout]
    exact congrArg (fun y : MonoidAlgebra R
        (Subgroup.centralizer (Q : Set G)) => y.coeff x)
      (subgroupRestriction_conjugationMap_q_mul Q q H c.out b)
  let q0 : G ⧸ H := (QuotientGroup.mk (1 : G) : G ⧸ H)
  have hq0fixed : q0 ∈ MulAction.fixedPoints Q (G ⧸ H) := by
    rw [MulAction.mem_fixedPoints]
    intro q
    change (QuotientGroup.mk ((q : G) * 1) : G ⧸ H) =
      (QuotientGroup.mk (1 : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.inv_mem (hQH q.property)
  calc
    (∑ q : G ⧸ H, F q) =
        ∑ q : MulAction.fixedPoints Q (G ⧸ H), F q :=
      SubgroupBrauerMap.sum_eq_sum_fixedPoints_of_smul_invariant hQ F hFinv
    _ = F q0 := by
      let e : MulAction.fixedPoints Q (G ⧸ H) := ⟨q0, hq0fixed⟩
      rw [Fintype.sum_eq_single e]
      intro y hy
      have hy0 : (y : G ⧸ H) ≠ q0 := by
        intro h
        apply hy
        exact Subtype.ext h
      have hz := hterm y.1 y.2 (by simpa [q0] using hy0)
      let evQ : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) →+ R :=
        (Finsupp.applyAddHom x).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom
      change evQ (DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H y.1.out b)) = 0
      rw [hz, map_zero]
    _ = (RelativeTransferBrauer.subgroupSubtypeMap R H b).coeff (x : G) := by
      have hout := RelativeTransferBrauer.conjugationMap_out_eq_of_mk_eq
        H q0 (1 : G) (by simp [q0]) b hbCenter
      dsimp only [F]
      rw [hout, RelativeTransferBrauer.conjugationMap_apply]
      simp

end ModularBlock.BrauerThirdMain

