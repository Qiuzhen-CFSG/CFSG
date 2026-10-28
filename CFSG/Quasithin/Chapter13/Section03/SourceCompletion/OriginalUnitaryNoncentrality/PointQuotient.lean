module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ComponentPerfect
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.PResidual.SylowIndexThree
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction

/-!
# The genuine unitary point-residual quotient

The literal point centralizer in L maps onto the derived second parabolic
of the split-octonion model, with two-group kernel and an explicit action
identity. Its Sylow two-subgroup has index three. Residual/core quotient
transport therefore gives order three for the original point residual
modulo its intrinsic two-core. No first-parabolic identification is used.

Source: Aschbacher--Smith 13.3.14(c)--(d), printed pp.891--892.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The actual point centralizer surjects onto the native derived point
parabolic, with a two-group kernel. -/
theorem unitary_point_centralizer_map
    (L Z : Subgroup G) (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz : pointCoordinateSubspace E Z = pointLine) (hZV : Z ≤ V)
    (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hres : pResidual 2 L = ⊤)
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho) :
    ∃ f : (L ⊓ centralizer (Z : Set G) : Subgroup G) →* derivedSecond,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      ∀ k, (f k).val.val = rho (V.normalizerMonoidHom.rangeRestrict
        ⟨k.val,hLN k.prop.1⟩) := by
  let K := L ⊓ centralizer (Z : Set G)
  let fL : L →* Atlas.G2.Model F := rho.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN))
  let f := fL.comp (inclusion (show K ≤ L from inf_le_left))
  let : Group.IsPerfect L := component_isPerfect_of_unitary_action L rho E he hLN hfaith hres hd
  have hder : fL.range ≤ DerivedModel := by
    calc
      fL.range = (commutator L).map fL := by rw [Group.IsPerfect.commutator_eq_top,←MonoidHom.range_eq_map]
      _ = ⁅fL.range,fL.range⁆ := map_commutator_eq (f:=fL)
      _ ≤ commutator (Atlas.G2.Model F) := commutator_mono le_top le_top
  have hpoint (k : K) : f k ∈ Atlas.G2.parabolic := by
    apply fixes_first_mem_parabolic
    let a := V.normalizerMonoidHom.rangeRestrict (inclusion hLN (inclusion inf_le_left k))
    obtain ⟨w,hw⟩ := E.surjective (Pi.single 0 1)
    have hwZ : w.toMul.val ∈ Z := (mem_pointCoordinateSubspace E Z w).mp (by
      rw [hz,hw,mem_pointLine]; intro i hi; simp [hi])
    change Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (Pi.single 0 1) = _
    rw [←hw,←he]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change k.val*w.toMul.val*k.val⁻¹=w.toMul.val
    rw [←mem_centralizer_iff.mp k.prop.2 _ hwZ,mul_inv_cancel_right]
  let q : K →* derivedSecond := {
    toFun := fun k => ⟨⟨f k,hder ⟨inclusion inf_le_left k,rfl⟩⟩,hpoint k⟩
    map_one' := Subtype.ext (Subtype.ext (map_one f))
    map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul f x y)) }
  refine ⟨q,?_,?_,fun _ => rfl⟩
  · intro g
    obtain ⟨i,⟨n,hnL,rfl⟩,hnative⟩ := hd g.val.prop
    have hnZ : n.val ∈ centralizer (Z : Set G) := by
      intro z hz'
      let v : Additive V := Additive.ofMul ⟨z,hZV hz'⟩
      have hv : E v ∈ pointLine := hz ▸ (mem_pointCoordinateSubspace E Z v).mpr hz'
      have hf := pointParabolic_fixes_pointLine g.val.val g.prop (E v) hv
      rw [←hnative,←he] at hf
      have hh : n.val*z*n.val⁻¹=z := congrArg (fun w:Additive V=>(w.toMul:G)) (E.injective hf)
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact ⟨⟨n.val,hnL,hnZ⟩,Subtype.ext (Subtype.ext hnative)⟩
  · have hk : IsPGroup 2 f.ker :=
      (component_action_kernel_isTwo L rho E he hLN hfaith).comap_of_injective
        (inclusion (show K ≤ L from inf_le_left)) (inclusion_injective _)
    have hker : q.ker = f.ker := by
      ext k
      exact ⟨fun h => congrArg (fun x : derivedSecond => x.val.val) h,
        fun h => Subtype.ext (Subtype.ext h)⟩
    exact hker.symm ▸ hk

/-- The literal point two-residual has intrinsic core quotient of order three. -/
theorem unitary_point_residual_quotient_card
    (L Z : Subgroup G) (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz : pointCoordinateSubspace E Z = pointLine) (hZV : Z ≤ V)
    (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hres : pResidual 2 L = ⊤)
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho) :
    let R := (pResidual 2 (L ⊓ centralizer (Z : Set G) : Subgroup G)).map
      (L ⊓ centralizer (Z : Set G)).subtype
    Nat.card (R ⧸ pCore 2 R) = 3 := by
  let K := L ⊓ centralizer (Z : Set G)
  let R := (pResidual 2 K).map K.subtype
  obtain ⟨f,hf,hk,_⟩ := unitary_point_centralizer_map L Z rho E he hz hZV hLN hfaith hres hd
  let er := (pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective
  have he := (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).symm.trans
    (f.pResidualCoreQuotientEquiv hf hk)
  change Nat.card (R ⧸ pCore 2 R) = 3
  rw [Nat.card_congr he.toEquiv]
  apply residual_core_quotient_card_of_sylow_index_three derivedSecondSylow
  exact derivedSylow_index_in_second
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
