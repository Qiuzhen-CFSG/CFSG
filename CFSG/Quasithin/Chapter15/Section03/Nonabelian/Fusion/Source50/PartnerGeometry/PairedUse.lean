module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedData
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedTransport
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MarkedCoordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Earlier

/-!
# Literal consumers of the selected polar coordinates

The paired coordinates give the source fixed line, extraspecial actor and,
in dimension three, the final marked partner action. All actor images use
the original quotient H/O₂(H) and its literal conjugation conventions.
Source: Aschbacher–Smith 15.3.56(4–7), printed p.1148.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open Core.ResidualGeneration BinaryPairedTransvections
variable {G : Type*} [Group G] {Z ZS : Subgroup G}

private theorem actor_conjugate (A : Subgroup G) (hA : A ≤ centralizerH Z)
    (t : centralizerH Z) :
    Recognition.actorImage Z (rightConjugate A (t:G)) =
      (Recognition.actorImage Z A).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 (centralizerH Z)) t)⁻¹).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨u,hu,he⟩ := hx
    let uH : centralizerH Z := ⟨u,hA hu⟩
    have heH : x=t⁻¹*uH*t := by
      apply Subtype.ext
      change (x:G)=(t:G)⁻¹*u*(t:G)
      change (t:G)⁻¹*u*((t:G)⁻¹)⁻¹=(x:G) at he
      simpa only [inv_inv] using he.symm
    refine ⟨q uH,⟨uH,hu,rfl⟩,?_⟩
    change (q t)⁻¹*q uH*((q t)⁻¹)⁻¹=q x
    rw [heH]
    simp only [map_mul,map_inv,inv_inv]
  · rintro ⟨a,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨t⁻¹*u*t,?_,?_⟩
    · refine ⟨(u:G),hu,?_⟩
      change (t:G)⁻¹*(u:G)*((t:G)⁻¹)⁻¹=(t:G)⁻¹*(u:G)*(t:G)
      rw [inv_inv]
    · change q (t⁻¹*u*t)=(q t)⁻¹*q u*((q t)⁻¹)⁻¹
      simp only [map_mul,map_inv,inv_inv]

private theorem subgroupOf_zpowers (t : centralizerH Z) :
    (zpowers (t:G)).subgroupOf (centralizerH Z)=zpowers t := by
  apply map_injective (centralizerH Z).subtype_injective
  rw [map_subgroupOf_eq_of_le (zpowers_le.mpr t.property),MonoidHom.map_zpowers]
  rfl

variable [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  {V₀ : Subgroup G} {y : G} {t : centralizerH Z}
  {hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z)}

namespace PairedCoordinates.Data

variable (b : PairedCoordinates.Data Z ZS V₀ y t hk)
include b

/-- The literal quotient fixed subgroup is the distinguished source line. -/
theorem fixed_line (T : Subgroup G) (hXT : partnerX Z ZS y ≤ T)
    (ht : (t:G)∈T) (hseed : ⁅ZS,T⁆≤Z)
    (hcard : Nat.card (distinguishedLine Z ZS)=2) :
    let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    FixedPoints.subgroup ((partnerX Z ZS y ⊔ zpowers (t:G)).subgroupOf (centralizerH Z))
      (VectorQuotient Z ZS)=distinguishedLine Z ZS := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  let ρ := PairedCoordinates.actor Z ZS hk b.coordinates
  let ρH := ρ.comp q
  let J := (partnerX Z ZS y ⊔ zpowers (t:G)).subgroupOf (centralizerH Z)
  have hequiv (h : centralizerH Z) (v : VectorQuotient Z ZS) :
      b.coordinates (Additive.ofMul (quotientAction Z ZS h v))=
        ρH h (b.coordinates (Additive.ofMul v)) := by
    change _=b.coordinates (actorRepresentation Z ZS hk (q h)
      (b.coordinates.symm (b.coordinates (Additive.ofMul v))))
    rw [b.coordinates.symm_apply_apply,actorRepresentation_mk]
    rfl
  have himage : J.map ρH=(centerGroup b.centerVector).map pairedAction ⊔ zpowers (ρ (q t)) := by
    dsimp only [J]
    rw [subgroupOf_sup b.X_le_H (zpowers_le.mpr t.property),Subgroup.map_sup,
      subgroupOf_zpowers,MonoidHom.map_zpowers]
    change ((partnerX Z ZS y).subgroupOf (centralizerH Z)).map (ρ.comp q) ⊔ _=_
    rw [← Subgroup.map_map]
    exact congrArg (fun K => K ⊔ zpowers (ρ (q t))) b.actor_image
  have hfix : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      distinguishedLine Z ZS ≤ FixedPoints.subgroup J (VectorQuotient Z ZS) := by
    let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    intro v hv j
    exact distinguishedLine_le_fixedPoints Z ZS T hseed hv
      ⟨j.val,(sup_le hXT (zpowers_le.mpr ht)) j.property⟩
  exact paired_model_fixed_line J b.coordinates ρH hequiv b.centerVector b.center_ne_zero
    b.axisForm b.axis_ne_zero b.incident (ρ (q t)) b.exchange_center b.exchange_axis
    (b.quadratic_invariant _) b.exchange_E b.exchange_D himage hcard hfix

/-- Faithful coordinate transport detects the actual paired actor center. -/
theorem extraspecial_product [Finite G]
    (V : Subgroup G) (hVH : V ≤ centralizerH Z)
    (htV : (t:G)∈normalizer (V:Set G))
    (hVX : Recognition.actorImage Z V ≤ Recognition.actorImage Z (partnerX Z ZS y))
    (hcard : Nat.card (Recognition.actorImage Z V)=2)
    (s : ℕ) (hdim : Module.finrank (ZMod 2) (PairedCoordinates.ESpace Z ZS y)=s+2) :
    0<s → ∃ P : Subgroup (ActorQuotient Z), IsExtraspecial 2 P ∧
      ∃ X : Subgroup P, IsElementaryAbelian 2 X ∧ Nat.card X=2^(s+1) ∧
        (center P).map P.subtype=Recognition.actorImage Z V := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  let ρ := PairedCoordinates.actor Z ZS hk b.coordinates
  have hρ := BinaryLagrangianDualPair.coordinateActor_injective
    (actorRepresentation Z ZS hk) b.coordinates (actorRepresentation_injective Z ZS hk)
  have hVconj : rightConjugate V (t:G)=V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V:Set G)).inv_mem htV)
  have hVXt : Recognition.actorImage Z V ≤
      (Recognition.actorImage Z (partnerX Z ZS y)).map (MulAut.conj (q t)⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj (q t)⁻¹).toMonoidHom) hVX
    rw [← actor_conjugate V hVH t,hVconj] at hh
    exact hh
  exact source_paired_extraspecial_product ρ hρ _ (q t) V b.centerVector b.center_ne_zero
    b.axisForm b.axis_ne_zero b.incident b.actor_image (b.quadratic_invariant _)
    b.exchange_E b.exchange_D b.exchange_axis hVX hVXt hcard s hdim

/-- The dimension-three specialization gives the literal order-eight actor. -/
theorem actor_pair_card [Finite G]
    (hdim : Module.finrank (ZMod 2) (PairedCoordinates.ESpace Z ZS y)=3) :
    Nat.card (Recognition.actorImage Z
      (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) (t:G)))=8 := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  let ρ := PairedCoordinates.actor Z ZS hk b.coordinates
  have hρ := BinaryLagrangianDualPair.coordinateActor_injective
    (actorRepresentation Z ZS hk) b.coordinates (actorRepresentation_injective Z ZS hk)
  have hXconj : rightConjugate (partnerX Z ZS y) (t:G)≤centralizerH Z := by
    rintro _ ⟨x,hx,rfl⟩
    exact (centralizerH Z).mul_mem ((centralizerH Z).mul_mem
      ((centralizerH Z).inv_mem t.property) (b.X_le_H hx))
      ((centralizerH Z).inv_mem ((centralizerH Z).inv_mem t.property))
  have hsup : Recognition.actorImage Z
      (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) (t:G))=
      Recognition.actorImage Z (partnerX Z ZS y) ⊔
      Recognition.actorImage Z (rightConjugate (partnerX Z ZS y) (t:G)) := by
    unfold Recognition.actorImage
    rw [subgroupOf_sup b.X_le_H hXconj,Subgroup.map_sup]
  rw [hsup,actor_conjugate _ b.X_le_H t]
  exact source_paired_actor_pair_card ρ hρ _ (q t) b.centerVector b.center_ne_zero
    b.axisForm b.axis_ne_zero b.incident b.actor_image (b.quadratic_invariant _)
    b.exchange_E b.exchange_D b.exchange_axis hdim

/-- The same coordinates give the full concrete marking used in fusion. -/
theorem marked [Finite G]
    (hdim : Module.finrank (ZMod 2) (PairedCoordinates.ESpace Z ZS y)=3) :
    Nonempty (Partner.MarkedAction Z ZS V₀ y (t:G) b.X_le_H) := by
  exact MarkedCoordinates.markedAction_of_paired Z ZS V₀ y (t:G) b.X_le_H
    hdim b.centerVector b.center_ne_zero b.coordinates
    (fun w => b.E_image (Additive.ofMul w)) (fun w => b.Et_image (Additive.ofMul w))
    (fun w => b.center_image (Additive.ofMul w)) b.parameter b.full b.equivariant

end PairedCoordinates.Data
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
