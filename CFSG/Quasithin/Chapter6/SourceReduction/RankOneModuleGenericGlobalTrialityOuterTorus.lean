module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# The triality torus has no unipotent normalizer at q > 2

The two base-field torus coordinates separate all twelve positive D4 roots.
The only weight needing care is the square character; it is nontrivial on
any nonidentity base-field unit in characteristic two. Uniqueness of the
ordered root coordinates therefore makes the torus centralizer in U trivial.
Since U and the torus are disjoint and the torus normalizes U, a unipotent
normalizer of the torus already centralizes it, and is consequently trivial.

The companion outer-involution construction pulls this fact through the
original whole-overlap map. It supplies the disjointness needed to split
T over the original S, without an odd-degree assumption.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, pp.289,293–294
(`refs/quasithin.pdf`). The genuine graph-field and root coordinates follow
GLS3 §§2.4–2.6 through the imported triality modules.
-/

public noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterTorus
private def rootWeight (P : Parameters) (a : TorusCoordinates.Coordinates P) (j : Fin 12) : ExtensionField P :=
  (a 0).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 0) *
    ((a 2).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 2) *
    ((a 3).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 3) *
     (a 1).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 1)))

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem product_curve (P : Parameters) (hp : P.prime=2) (a : TorusCoordinates.Coordinates P) (j : Fin 12)
    (u : ExtensionField P) :
    TorusCoordinates.product P a * curve P j u * (TorusCoordinates.product P a)⁻¹ =
      curve P j (rootWeight P a j * u) := by
  simp only [TorusCoordinates.product, conjugate_product, torusWord_curve_conjugate P hp]
  simp only [rootWeight, mul_assoc]

private theorem product_orderedProduct (P : Parameters) (hp : P.prime=2) (a : TorusCoordinates.Coordinates P) (v : Coordinates P) :
    TorusCoordinates.product P a * orderedProduct P v * (TorusCoordinates.product P a)⁻¹ =
      orderedProduct P (fun j => rootWeight P a j * v j) := by
  simp only [orderedProduct, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simp only [conjugate_mul, product_curve P hp]


private def pairing : Fin 12 → Fin 4 → ℤ := ![![2,-1,0,0], ![0,-1,2,0], ![0,-1,0,2], ![-1,2,-1,-1], ![1,1,-1,-1], ![-1,1,1,-1], ![-1,1,-1,1], ![1,0,1,-1], ![-1,0,1,1], ![1,0,-1,1], ![1,-1,1,1], ![0,1,0,0]]
private theorem root_pairing (j : Fin 12) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex j)
      (typeDSimpleRootIndex 2 i) = pairing j i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex j) k) = pairing j i := by
    revert j i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (pairing j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem separating_weights (P : Parameters) (hp : P.prime=2)
    (b : (fixedField P)ˣ) (hb : b≠1) (j : Fin 12) :
    rootWeight P (TorusCoordinates.expand P (1,b)) j ≠ 1 ∨
    rootWeight P (TorusCoordinates.expand P (TorusCoordinates.fixedUnit P b,1)) j ≠ 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hb' : ((b.val : fixedField P) : ExtensionField P) ≠ 1 :=
    fun hh => hb (Units.ext (Subtype.ext hh))
  have hb2 : ((b.val : fixedField P) : ExtensionField P)^2 ≠ 1 := by
    intro he
    exact hb' ((sq_eq_sq_iff_eq_or_eq_neg.mp (he.trans (one_pow 2).symm)).elim id
      (fun hh => hh.trans (CharTwo.neg_eq 1)))
  fin_cases j <;>
    simp only [rootWeight,root_pairing,pairing,TorusCoordinates.expand,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      TorusCoordinates.frobenius_fixedUnit,map_one] <;>
    simp [TorusCoordinates.fixedUnit,hb',hb2]


private theorem centralizer_trivial (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (u : Carrier (binaryParameters n hn)) (hu : u∈unipotent (binaryParameters n hn))
    (hc : u∈centralizer (torus (binaryParameters n hn) : Set _)) : u=1 := by
  let P := binaryParameters n hn
  have hp : P.prime=2 := rfl
  have hq : 2<P.q := Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn2
  have hn : 1<Nat.card (fixedField P)ˣ := by rw [Nat.card_units,card_fixedField]; omega
  let : Nontrivial (fixedField P)ˣ := Finite.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨b,hb⟩ := exists_ne (1:(fixedField P)ˣ)
  let v := (CentralCovers.TwoPrimary.positiveEquiv n ‹0<n›).symm ⟨u,hu⟩
  have hv : FixedDescent.carrierToSplit P hp u = orderedProduct P (expand P v) := by
    rw [←CentralCovers.TwoPrimary.baseProduct_toSplit]
    apply congrArg (FixedDescent.carrierToSplit P hp)
    exact (congrArg Subtype.val ((CentralCovers.TwoPrimary.positiveEquiv n ‹0<n›).apply_symm_apply
      ⟨u,hu⟩)).symm.trans (CentralCovers.TwoPrimary.positiveEquiv_val n ‹0<n› v)
  have hweights (a : TorusCoordinates.OrbitParameters P) (j : Fin 12) :
      rootWeight P (TorusCoordinates.expand P a) j * expand P v j = expand P v j := by
    let g := TorusCoordinates.torusMulEquiv P hp a
    have hcomm : (g : Carrier P)*u*(g : Carrier P)⁻¹=u := by
      rw [hc g g.property,mul_inv_cancel_right]
    have hg : FixedDescent.carrierToSplit P hp g = TorusCoordinates.product P
        (TorusCoordinates.expand P a) := by
      change FixedDescent.carrierToSplit P hp (TorusCoordinates.torusMulEquiv P hp a).val = _
      rw [TorusCoordinates.torusMulEquiv_val,FixedDescent.carrierToSplit_toCarrier]
      exact TorusCoordinates.inclusion_orbitElementary P hp a
    have hh := congrArg (FixedDescent.carrierToSplit P hp) hcomm
    simp only [map_mul,map_inv,hg,hv] at hh
    rw [product_orderedProduct P hp] at hh
    exact congrFun (orderedProduct_injective P hh) j
  have hz : expand P v=0 := by
    funext j
    rcases separating_weights P hp b hb j with hs|hs
    · exact eq_zero_of_mul_eq_self_left hs (hweights (1,b) j)
    · exact eq_zero_of_mul_eq_self_left hs (hweights (TorusCoordinates.fixedUnit P b,1) j)
  apply FixedDescent.carrierToSplit_injective P hp
  rw [hv,hz,map_one]
  simp [orderedProduct,curve_zero]

/-- The full triality torus has no nonidentity unipotent normalizer when q>2. -/
theorem unipotent_torus_normalizer_trivial (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (u : Carrier (binaryParameters n hn)) (hu : u∈unipotent (binaryParameters n hn))
    (hnorm : u∈normalizer (torus (binaryParameters n hn) : Set _)) : u=1 := by
  let P := binaryParameters n hn
  have hp : P.prime=2 := rfl
  apply centralizer_trivial n hn hn2 u hu
  apply mem_centralizer_iff.mpr
  intro t ht
  have hT : u*t*u⁻¹*t⁻¹∈torus P := (torus P).mul_mem
    ((mem_normalizer_iff.mp hnorm t).mp ht) ((torus P).inv_mem ht)
  have hU : u*t*u⁻¹*t⁻¹∈unipotent P := by
    have hh := (unipotent P).mul_mem hu
      ((mem_normalizer_iff.mp (borel_le_normalizer_unipotent P hp (torus_le_borel P ht)) u⁻¹).mp
        ((unipotent P).inv_mem hu))
    simpa only [mul_assoc] using hh
  have he := disjoint_def.mp (disjoint_unipotent_torus P hp) hU hT
  have hh : u*t=t*u := mul_inv_eq_one.mp (by simpa only [mul_inv_rev,mul_assoc] using he)
  exact hh.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterTorus
