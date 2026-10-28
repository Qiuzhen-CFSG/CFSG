module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionNatural
public import Theory.Representation.SL2.NaturalCoprimeCentralizer
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Full neighboring centers beside a natural field-four center

A full neighboring central involution lies in the common edge Sylow center,
hence in the natural starting center. An actual element of the starting
Sylow normalizer lifts a cubic in the quotient and fixes the neighbor.
Equivariance then kills the involution in the literal natural module.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
  {K : Type*} [Field K] [Finite K]

/-- The full neighboring stabilizer has no central involution when the
starting center is natural over a field of order four. -/
theorem natural_neighbor_central_involution_eq_one
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v))
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (eK : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SL(2,K))
    (hK : Nat.card K = 4)
    (x : G) (hx : x ∈ (center (stabilizer (family P) w)).map
      (stabilizer (family P) w).subtype) (hx2 : x^2=1) : x=1 := by
  let := finite_endpoints h
  let F := family P
  let A := d.localGroup v
  let W := stabilizer F w
  let : Finite A := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨k,_,_,_,π,e,hπ,_,_,⟨δ⟩⟩ :=
    source_natural_center_coordinates_of_neighbor_central h d he hcentral hnat
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  have hk : Nat.card k = 4 := (Matrix.SL2.field_card_eq_of_equiv (e.symm.trans eK)).trans hK
  obtain ⟨z,hz,rfl⟩ := hx
  have hWC : W ≤ centralizer (zpowers (z : G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hzp : IsPGroup 2 (zpowers (z : G)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx2).isPGroup 2 _
  have hzQ : zpowers (z : G) ≤ W.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hzp (zpowers_le.mpr z.property)
      (hWC.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨T,U,hTU⟩ := d.common_sylow w v he.symm
  have hzT : (z : G) ∈ (T : Subgroup W).map W.subtype :=
    pCoreIn_le_sylow W T (hzQ (mem_zpowers _))
  have hzΩ : (z : G) ∈ omegaCenterIn ((T : Subgroup W).map W.subtype) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzT,?_,hx2⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,map_subtype_le _ hy⟩)
  rw [hTU] at hzΩ
  have hzZ : (z : G) ∈ Z F v :=
    (le_iSup (fun U : Sylow 2 (stabilizer F v) =>
      omegaCenterIn ((U : Subgroup (stabilizer F v)).map (stabilizer F v).subtype)) U) hzΩ
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d he
  let Rq := R.mapSurjective hπ
  let N := normalizer (Rq : Set SL(2,k))
  have hdiv : 3 ∣ Nat.card N := by
    change 3 ∣ Nat.card (normalizer ((Rq : Subgroup SL(2,k)) : Set SL(2,k)))
    rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even Rq,hk]
    decide
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hdiv
  have hao : orderOf (a : SL(2,k)) = 3 :=
    (orderOf_injective N.subtype N.subtype_injective a).trans ha
  have ha1 : (a : SL(2,k)) ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hao
    contradiction
  have hN : (normalizer (R : Set A)).map π = N := R.normalizer_map_surjective π hπ
  obtain ⟨g,hg,hga⟩ := hN.ge a.property
  have hgw : (g : G) ∈ W := by
    rw [←(source_edge_local_normalizer h d he M R hR).2] at hg
    exact hg
  let zZ : Z F v := ⟨z,hzZ⟩
  have hconj : (⟨(g : G) * zZ * (g : G)⁻¹,
      (mem_normalizer_iff.mp (δ.normalized g.property) zZ).mp zZ.property⟩ : Z F v) = zZ := by
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨g,hgw⟩))
  have hfixed : Matrix.mulVec (π g).val (δ.coordinates zZ).toAdd = (δ.coordinates zZ).toAdd := by
    have hh := (δ.equivariant g zZ).symm
    rw [hconj] at hh
    exact hh
  have hzero := Representation.SL2.natural_odd_fixed_eq_zero (π g)
    (by rw [hga,hao]; decide) (by rwa [hga]) _ hfixed
  exact mem_bot.mp ((δ.coordinates_eq_one_iff zZ).mp (Multiplicative.toAdd.injective hzero))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
