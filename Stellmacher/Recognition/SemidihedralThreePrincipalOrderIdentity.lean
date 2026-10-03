module
public import Stellmacher.Recognition.SemidihedralThreePrincipalLocalPairing
public import ABG.ChapterIII.Section7.ThreePrincipalOrderReduction
public import Theory.SpecificGroups.GL2.ThreeFourCentralizerOddCore

/-!
# The characteristic-three principal-character order identity

Write N = C_G(x), let K be its odd core viewed in G, and put A = C_K(T).
The GL₂(3) quotient gives |N| = 48 |A| [K:A] and |C_G(T)| = 4 |A|.
For any supplied principal datum, the local involution-pair evaluation is
2 [K:A]/|A|. Involution fusion and the global character pairing then give
|G|(f₁ − 3)² = 4608 |A| [K:A]³ f₁(f₁ − 1).

The datum retains the actual block characters; this argument neither constructs
it nor requires the odd core to be trivial or to centralize T.

Source: Alperin–Brauer–Gorenstein, III.2 Proposition 6 equation (4), proved
in III.7, article pp.68 and 103–104.
-/

namespace Stellmacher.Recognition
open ABG Matrix
noncomputable section
attribute [local instance] Fintype.ofFinite

private theorem involution_fusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (u : G) (hu : orderOf u = 2) : IsConj u x := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hi⟩ := hcov u hu
  obtain ⟨j, hj⟩ := hcov x hx
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

/-- The involution centralizer order in the odd-core intersection parameters. -/
public theorem involutionCentralizer_card_coreParameters
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    Nat.card N = 48 * Nat.card A * A.index := by
  let N := Subgroup.centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  let K := O.map N.subtype
  let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
  have hK : Nat.card K = Nat.card O := Subgroup.card_map_of_injective N.subtype_injective
  change Nat.card N = 48 * Nat.card A * A.index
  rw [involutionCentralizer_card_of_simple_nTwo S hS hN x hx,
    ← hK, ← A.card_mul_index, mul_assoc]

/-- The four-group centralizer has order four times its odd-core intersection. -/
public theorem fourCentralizer_card_intersection_of_simple_nTwo
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    Nat.card (Subgroup.centralizer (T : Set G)) = 4 * Nat.card A := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  let eF : ABG.GL2 3 1 ≃* GL (Fin 2) (ZMod 3) :=
    Units.mapEquiv (GaloisField.equivZmodP 3).toRingEquiv.mapMatrix.toMulEquiv
  exact Subgroup.fourCentralizer_card_intersection_of_oddCoreQuotient x T hT hxT
    (e.trans eF)

/-- ABG III.2 Proposition 6 (4), for any supplied characteristic-three
principal datum, retaining the possibly nontrivial local odd core. -/
public theorem semidihedral_threePrincipal_order_identity
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (c : ThreePrincipalData G x) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    (Nat.card G : ℤ) * ((c.degree 0 : ℤ) - 3)^2 =
      4608 * (Nat.card A * A.index^3 : ℕ) *
        (c.degree 0 : ℤ) * ((c.degree 0 : ℤ) - 1) := by
  let N := Subgroup.centralizer ({x} : Set G)
  let K := (pPrimeCore 2 N).map N.subtype
  let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
  have hlocal : scalarProduct N c.localOrderFunction
      (fun u => (Theory.Character.involutionPairCount u : ℂ)) =
        2 * (A.index : ℂ) / Nat.card A := by
    convert threePrincipal_local_pairing S hS hN x hx T hT hxT c using 1
    congr 1
    exact Subsingleton.elim _ _
  exact c.order_identity_of_local_pairing hx (involution_fusion S hS x hx)
    (Nat.card A) A.index Nat.card_pos.ne' A.index_ne_zero_of_finite
    (involutionCentralizer_card_coreParameters S hS hN x hx T)
    hlocal

end
end Stellmacher.Recognition
