module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.LocalRestrictions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Power
/-!
# Transport of the literal singular subspaces

Conjugation on U/Z transports each subgroup image by the same ambient
conjugation. An element whose square normalizes a subgroup exchanges its
image with the image of its right conjugate. This keeps the partner's
natural and dual summands attached to the original quotient.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition LocalRestrictions Representation.BinaryOffender
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

theorem subspace_mk_mem (A : Subgroup G) (hZA : Z ≤ A) (u : closureU Z ZS) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) ∈
      vectorSubspace Z ZS A ↔ (u:G)∈A := by
  change u∈(vectorImage Z ZS A).comap (QuotientGroup.mk' _) ↔ _
  rw [vectorImage_preimage Z ZS A hZA]
  rfl

theorem point_le_conjugate (A : Subgroup G) (hZA : Z≤A) (t : centralizerH Z) :
    Z ≤ rightConjugate A (t:G) := by
  intro z hz
  apply mem_map_equiv.mpr
  simp only [MulAut.conj_symm_apply,inv_inv]
  have he : z*(t:G)=(t:G)*z := t.property z hz
  rw [← he,mul_inv_cancel_right]
  exact hZA hz

theorem actor_mem_conjugate_subspace
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (A : Subgroup G) (hZA : Z≤A) (t : centralizerH Z) (w : Space Z ZS) :
    actorRepresentation Z ZS hk (QuotientGroup.mk' _ t) w∈vectorSubspace Z ZS A ↔
      w∈vectorSubspace Z ZS (rightConjugate A (t:G)) := by
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w.toMul
  have hw : w=Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
  rw [hw,actorRepresentation_mk]
  change Additive.ofMul (quotientAction Z ZS t (QuotientGroup.mk' _ u))∈_ ↔ _
  rw [quotientAction_mk,subspace_mk_mem,subspace_mk_mem Z ZS _
    (point_le_conjugate Z A hZA t)]
  · change (t:G)*(u:G)*(t:G)⁻¹∈A ↔ (u:G)∈rightConjugate A (t:G)
    simp only [rightConjugate,mem_map_equiv,MulAut.conj_symm_apply,inv_inv]
  · exact hZA

omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
theorem conjugate_twice_of_square_normalizes (A : Subgroup G) (t : G)
    (ht : t^2∈normalizer (A:Set G)) :
    rightConjugate (rightConjugate A t) t=A := by
  have he : rightConjugate (rightConjugate A t) t=rightConjugate A (t^2) := by
    change (A.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom=_
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,MulAut.conj_apply,inv_inv]
    simp only [pow_two,mul_inv_rev,mul_assoc]
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (A:Set G)).inv_mem ht)

theorem actor_exchanges_subspaces
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (A : Subgroup G) (hZA : Z≤A) (t : centralizerH Z)
    (ht : (t:G)^2∈normalizer (A:Set G)) :
    (∀w∈vectorSubspace Z ZS A,actorRepresentation Z ZS hk (QuotientGroup.mk' _ t) w∈
      vectorSubspace Z ZS (rightConjugate A (t:G))) ∧
    (∀w∈vectorSubspace Z ZS (rightConjugate A (t:G)),
      actorRepresentation Z ZS hk (QuotientGroup.mk' _ t) w∈vectorSubspace Z ZS A) := by
  constructor
  · intro w hw
    rw [actor_mem_conjugate_subspace Z ZS hk _ (point_le_conjugate Z A hZA t),
      conjugate_twice_of_square_normalizes A (t:G) ht]
    exact hw
  · intro w hw
    exact (actor_mem_conjugate_subspace Z ZS hk A hZA t w).mpr hw

/-- An elementary subgroup is singular for the literal power form. -/
theorem elementary_subspace_singular (A : Subgroup G) [IsElementaryAbelian 2 A]
    (q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hp : ∀u:closureU Z ZS,q (Additive.ofMul (QuotientGroup.mk' _ u))=0 ↔ u^2=1) :
    ∀w∈vectorSubspace Z ZS A,q w=0 := by
  rintro w ⟨u,hu,he⟩
  change QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u=w.toMul at he
  have he' : Additive.ofMul (QuotientGroup.mk' _ u)=w := congrArg Additive.ofMul he
  rw [← he']
  apply (hp u).mpr
  apply Subtype.ext
  exact congrArg (fun a:A => (a:G)) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨u,hu⟩:A))

/-- The actual ambient normalizer stabilizes exactly the corresponding quotient subspace. -/
theorem actorImage_le_subspaceStabilizer
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (A X : Subgroup G) (hZA : Z≤A) (hAU : A≤closureU Z ZS)
    (hXN : X≤normalizer (A:Set G)) :
    actorImage Z X≤subspaceStabilizer (actorRepresentation Z ZS hk) (vectorSubspace Z ZS A) := by
  rw [stabilizer_eq_actorImage_normalizer Z ZS hk A hZA hAU]
  exact map_mono (fun _ hx => hXN hx)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
