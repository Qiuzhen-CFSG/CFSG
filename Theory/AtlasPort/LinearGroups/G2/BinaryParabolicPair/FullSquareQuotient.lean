module

public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.GroupTheory.NormalSymmetricThreeTwelve
public import Theory.GroupTheory.OddInvolutionEndpointModels

/-!
# The C₄² radical of the full binary G₂ second vertex

The second derived vertex is normal in the full vertex. Its characteristic
two-core, already identified through the actual root-word map as C₄², is
therefore normal in the full vertex. The quotient has order twelve and contains
the normal S₃ quotient of the derived vertex. It is consequently D₁₂. All
subgroups and quotient maps remain the original embedded root groups.

Source: Aschbacher–Smith F.1.12(I)(3), F.6.18(11), and 14.2.21.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryParabolicPair.FullSquare
open BinaryCore ExceptionalLocalQuotients
open Theory.GroupTheory.RankTwoAmalgam

/-- The original second vertex's intersection with the ambient derived group. -/
def inner : Subgroup secondParabolic :=
  (commutator (Model (ZMod 2))).comap secondParabolic.subtype

instance inner_normal : inner.Normal := inferInstanceAs
  ((commutator (Model (ZMod 2))).comap secondParabolic.subtype).Normal

/-- Reorder the two literal subgroup memberships. -/
def innerEquiv : derivedSecond ≃* inner where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The characteristic derived-vertex core inside the full second vertex. -/
def radical : Subgroup secondParabolic := (pCore 2 inner).map inner.subtype

instance radical_normal : radical.Normal := inferInstanceAs
  ((pCore 2 inner).map inner.subtype).Normal

/-- The original C₄² marking, through the already checked root words. -/
def radicalEquiv : radical ≃* C4Square :=
  ((pCore 2 inner).equivMapOfInjective inner.subtype inner.subtype_injective).symm.trans
    ((LocalCoreTransport.coreEquiv 2 innerEquiv.symm).trans derivedSecondCoreEquiv)

theorem radical_card : Nat.card radical = 16 := by
  rw [Nat.card_congr radicalEquiv.toEquiv]
  norm_num [C4Square,Nat.card_prod,Nat.card_eq_fintype_card]

abbrev Q := secondParabolic ⧸ radical
def project : secondParabolic →* Q := QuotientGroup.mk' radical
def innerImage : Subgroup Q := inner.map project

instance innerImage_normal : innerImage.Normal :=
  (inferInstance : inner.Normal).map project (QuotientGroup.mk'_surjective radical)

theorem inner_project_ker : (project.comp inner.subtype).ker = pCore 2 inner := by
  ext x
  change (QuotientGroup.mk (x : secondParabolic) : Q) = 1 ↔ x ∈ pCore 2 inner
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y,hy,he⟩
    exact inner.subtype_injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- The embedded normal S₃ quotient of the original derived vertex. -/
def innerImageEquiv : innerImage ≃* Equiv.Perm (Fin 3) := by
  let f := project.comp inner.subtype
  have hr : f.range = innerImage := by
    rw [MonoidHom.range_comp,range_subtype]
    rfl
  let a : (inner ⧸ pCore 2 inner) ≃* innerImage :=
    ((QuotientGroup.quotientMulEquivOfEq inner_project_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hr)
  exact a.symm.trans ((LocalCoreTransport.quotientEquiv 2 innerEquiv.symm).trans
    (derivedSecondQuotientEquiv.trans
      (dihedralEquivPSL.symm.trans nonempty_dihedralThreeEquivPerm.some)))

theorem quotient_card : Nat.card Q = 12 := by
  have hc := radical.card_mul_index
  rw [radical_card,secondParabolic_card] at hc
  change radical.index = 12
  omega

/-- The actual full second-vertex quotient is D₁₂. -/
def quotientEquiv : Q ≃* DihedralGroup 6 :=
  (dihedral_twelve_of_normal_symmetric_three quotient_card innerImage innerImageEquiv).some

end Atlas.G2.BinaryParabolicPair.FullSquare
