module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.PointQuotient
public import Theory.Representation.G2BinaryPointResidualMovement
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.FlagNormalization

/-!
# The original point residual moves the seed through its two-core

The point residual has cubic core quotient. If its two-core fixed the
marked three-space, the seed action would therefore be commutative.
Two actual cubics lifted from the derived second parabolic violate this.
The proof retains the original subtype, quotient and conjugation action;
it supplies the nontrivial star core in unitary reduction (c).

Source: Aschbacher--Smith 13.3.14(c), printed pp.891--892.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem conjugation_commutes_of_cubic_core (R U : Subgroup G)
    (hRU : R ≤ normalizer (U : Set G)) (hcard : Nat.card (R ⧸ pCore 2 R) = 3)
    (hc : R.pCoreIn 2 ≤ centralizer (U : Set G)) (r s : R) (v : U) :
    (r*s).val*v.val*(r*s).val⁻¹ = (s*r).val*v.val*(s*r).val⁻¹ := by
  let ψ : R →* MulAut U := U.normalizerMonoidHom.comp (inclusion hRU)
  have hker : pCore 2 R ≤ ψ.ker := by
    intro x hx
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change x.val*v.val*x.val⁻¹=v.val
    have hcv := mem_centralizer_iff.mp (hc (mem_map_of_mem R.subtype hx)) v.val v.prop
    change v.val*x.val=x.val*v.val at hcv
    rw [←hcv,mul_inv_cancel_right]
  let ψbar := QuotientGroup.lift (pCore 2 R) ψ hker
  let : IsCyclic (R ⧸ pCore 2 R) := isCyclic_of_prime_card hcard
  have hcomm : ψ (r*s) = ψ (s*r) :=
    congrArg ψbar (mul_comm (QuotientGroup.mk r : R ⧸ pCore 2 R) (QuotientGroup.mk s))
  exact congrArg (fun q : MulAut U => (q v).val) hcomm

/-- The point residual's two-core moves the actual seed: otherwise its
cubic quotient would make the seed action commutative, contrary to two
literal conjugate cubics in the native point parabolic. -/
theorem unitary_point_residual_core_moves_seed
    (L Z U : Subgroup G) (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz : pointCoordinateSubspace E Z = pointLine) (hs : pointCoordinateSubspace E U = seed)
    (hZV : Z ≤ V) (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hres : pResidual 2 L = ⊤)
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho) :
    let R := (pResidual 2 (L ⊓ centralizer (Z : Set G) : Subgroup G)).map
      (L ⊓ centralizer (Z : Set G)).subtype
    ¬ R.pCoreIn 2 ≤ centralizer (U : Set G) := by
  let K := L ⊓ centralizer (Z : Set G)
  let R := (pResidual 2 K).map K.subtype
  change ¬ R.pCoreIn 2 ≤ centralizer (U : Set G)
  intro hc
  obtain ⟨f,hf,_,hfe⟩ := unitary_point_centralizer_map L Z rho E he hz hZV hLN hfaith hres hd
  let a : derivedSecond := ⟨⟨movingActor,movingActor_mem_derived⟩,movingActor_mem_derivedSecond⟩
  let c : derivedSecond := ⟨⟨Atlas.G2.rootC 1 * Atlas.G2.rootD 1,point_actor_membership.2.2.2⟩,
    point_actor_membership.2.2.1⟩
  let b := c*a*c⁻¹
  have ha : a ∈ pResidual 2 derivedSecond := movingActor_derived_residual
  have hb : b ∈ pResidual 2 derivedSecond := (inferInstance : (pResidual 2 derivedSecond).Normal).conj_mem a ha c
  have hlift (x : derivedSecond) (hx : x ∈ pResidual 2 derivedSecond) :
      ∃ r : R, f ⟨r.val,((map_subtype_le _ : R ≤ K) r.prop)⟩ = x := by
    rw [←map_pResidual_of_surjective 2 f hf] at hx
    obtain ⟨k,hk,hkx⟩ := hx
    exact ⟨⟨k.val,⟨k,hk,rfl⟩⟩,hkx⟩
  obtain ⟨r,hr⟩ := hlift a ha
  obtain ⟨s,hs'⟩ := hlift b hb
  have hRU : R ≤ normalizer (U : Set G) :=
    point_centralizer_normalizes_marked_seed U Z R rho E he hs hz
      hUV
      ((map_subtype_le _).trans (inf_le_left.trans hLN)) ((map_subtype_le _).trans inf_le_right)
  have hcard : Nat.card (R ⧸ pCore 2 R) = 3 :=
    unitary_point_residual_quotient_card L Z rho E he hz hZV hLN hfaith hres hd
  let v : Additive V := E.symm (Pi.single 1 1)
  have hv : v.toMul.val ∈ U := (mem_pointCoordinateSubspace E U v).mp (by rw [hs]; simp [v])
  have hact := conjugation_commutes_of_cubic_core R U hRU hcard hc r s ⟨v.toMul.val,hv⟩
  let n (x : R) : normalizer (V : Set G) := ⟨x.val,hLN ((map_subtype_le _ x.prop).1)⟩
  have heq : E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict (n (r*s))) v) =
      E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict (n (s*r))) v) :=
    congrArg E (Additive.toMul.injective (Subtype.ext hact))
  rw [he,he] at heq
  have hnative (x : R) : rho (V.normalizerMonoidHom.rangeRestrict (n x)) =
      (f ⟨x.val,map_subtype_le _ x.prop⟩).val.val := (hfe ⟨x.val,map_subtype_le _ x.prop⟩).symm
  have hrs : rho (V.normalizerMonoidHom.rangeRestrict (n (r*s))) = (a*b).val.val := by
    refine (hnative _).trans (congrArg (fun x : derivedSecond => x.val.val) ?_)
    change f (⟨r.val,map_subtype_le _ r.prop⟩ * ⟨s.val,map_subtype_le _ s.prop⟩ : K) = a*b
    exact (map_mul f _ _).trans (congrArg₂ (fun x y : derivedSecond => x*y) hr hs')
  have hsr : rho (V.normalizerMonoidHom.rangeRestrict (n (s*r))) = (b*a).val.val := by
    refine (hnative _).trans (congrArg (fun x : derivedSecond => x.val.val) ?_)
    change f (⟨s.val,map_subtype_le _ s.prop⟩ * ⟨r.val,map_subtype_le _ r.prop⟩ : K) = b*a
    exact (map_mul f _ _).trans (congrArg₂ (fun x y : derivedSecond => x*y) hs' hr)
  rw [hrs,hsr] at heq
  exact Atlas.G2.Natural.BinaryPointFlag.point_residual_cubics_do_not_commute (by
    simpa only [v,LinearEquiv.apply_symm_apply,a,b,c,Subgroup.coe_mul,Subgroup.coe_inv] using heq)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
