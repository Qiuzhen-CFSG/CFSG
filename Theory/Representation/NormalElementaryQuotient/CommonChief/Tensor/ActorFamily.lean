module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.ActorLift
public import Theory.Representation.PSL3Two.DoubledOffenders
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Uniqueness of the actor on a sharp natural tensor

Restricting the same external tensor to its first factor gives exactly three
copies of its constituent for every subgroup, not just the initially marked
actor. Thus displacement at most three bounds constituent displacement by
one. Within a two-subgroup of SL₃(2), rank-two actors with that bound are
unique: on two natural copies they are offenders, and the Sylow offender
calculation identifies each with the same common-axis four-group.

The quotient and coordinate maps are those of the original chief section.
Source: Aschbacher--Smith 13.1.9, printed p.871, the equality of the
Thompson image and the marked common-axis actor.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped TensorProduct
open QuadraticFourGroup.TensorClassification
namespace Representation.ProductIsotypic
variable {G H V : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) (G × H) V} {A : Subgroup G}

def SharpTensor.copyCoordinates (d : SharpTensor ρ A) :
    V ≃ₗ[ZMod 2] (Fin 3 → d.constituent.toSubmodule) :=
  d.coordinates.toLinearEquiv.trans
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2) d.constituent.toSubmodule (Fin 3))

theorem SharpTensor.copyCoordinates_action (d : SharpTensor ρ A) (g : G) (v : V) :
    d.copyCoordinates (ρ (g,1) v) = fun i => d.constituent.toRepresentation g (d.copyCoordinates v i) := by
  have he := LinearMap.congr_fun (d.coordinates.isIntertwining' (g,1)) v
  change d.coordinates (ρ (g,1) v) =
    externalTensor d.constituent.toRepresentation d.multiplicity (g,1) (d.coordinates v) at he
  change TensorProduct.piScalarRight _ _ _ _ (d.coordinates (ρ (g,1) v)) =
    fun i => d.constituent.toRepresentation g
      (TensorProduct.piScalarRight _ _ _ _ (d.coordinates v) i)
  rw [he]
  generalize d.coordinates v = w
  induction w using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul u v =>
    simp only [externalTensor_apply,TensorProduct.map_tmul,map_one,Module.End.one_apply,
      TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul,map_smul]
  | add u v hu hv =>
    simp only [map_add,hu,hv,Pi.add_apply]
    rfl

theorem SharpTensor.fixedCodim_left [FiniteDimensional (ZMod 2) V]
    (d : SharpTensor ρ A) (B : Subgroup G) :
    fixedCodim (left ρ) B = 3 * fixedCodim d.constituent.toRepresentation B := by
  have hh := fixedCodim_map_equivariant (left ρ)
    (BinaryParabolicNatural.copies (Fin 3) d.constituent.toRepresentation)
    (MonoidHom.id G) d.copyCoordinates d.copyCoordinates_action B
  simpa only [Subgroup.map_id,BinaryParabolicNatural.fixedCodim_copies,Fintype.card_fin] using hh
end Representation.ProductIsotypic

namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥}

theorem Data.NaturalTensor.constituent_fixedCodim_le
    (d : c.NaturalTensor hc) (B : Subgroup Q) (hBK : B ≤ K) :
    3 * fixedCodim d.tensor.constituent.toRepresentation (B.subgroupOf (K ⊔ A)) ≤
      fixedCodim ρ B := by
  let F := actorGroup S K A
  let σ := sectionRepresentation (ρ.comp F.subtype) c.lower c.upper
  let E := K ⊔ A
  have hBE : B ≤ E := hBK.trans le_sup_left
  have hBF : B ≤ F := hBE.trans le_sup_right
  have hf : fixedSpace (ProductIsotypic.left (c.productRepresentation hc)) (B.subgroupOf E) =
      fixedSpace σ (B.subgroupOf F) := by
    ext v
    constructor
    · intro h b
      have hb := h ⟨⟨b.val.val,hBE b.property⟩,b.property⟩
      change c.productRepresentation hc (⟨b.val.val,hBE b.property⟩,1) v = v at hb
      rw [c.productRepresentation_left] at hb
      exact hb
    · intro h b
      change c.productRepresentation hc (b.val,1) v = v
      rw [c.productRepresentation_left]
      exact h ⟨⟨b.val.val,hBF b.property⟩,b.property⟩
  have hd : fixedCodim (ProductIsotypic.left (c.productRepresentation hc)) (B.subgroupOf E) =
      fixedCodim σ (B.subgroupOf F) := by unfold fixedCodim; rw [hf]
  have hbound := fixedCodim_section_le (ρ.comp F.subtype) c.lower c.upper (B.subgroupOf F)
  have hrest : fixedCodim (ρ.comp F.subtype) (B.subgroupOf F) = fixedCodim ρ B := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hBF]
  rw [←hd,d.tensor.fixedCodim_left] at hbound
  exact hbound.trans_eq hrest
end Representation.CommonChief

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.DoubledOffenders

theorem eq_of_offenders_in_twoGroup (R A B : Subgroup Group)
    (hR : IsPGroup 2 R) (hA : A ≤ R) (hB : B ≤ R)
    (ha : IsOffender (W.prod W) A) (hb : IsOffender (W.prod W) B) : A = B := by
  obtain ⟨P,hP⟩ := hR.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Group Matrix.PSL3Two.SourceFlag.flagSylow P
  have he : (P : Subgroup Group) = Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [←hg,Sylow.coe_subgroup_smul]
    rfl
  exact ((offender_borel_conjugate_iff g A (he ▸ hA.trans hP)).mp ha).trans
    ((offender_borel_conjugate_iff g B (he ▸ hB.trans hP)).mp hb).symm
end BinaryLinearThree.DoubledOffenders

namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {d : c.NaturalTensor hc}

theorem Data.NaturalTensor.OtherNatural.matrixAction_injective
    (n : d.OtherNatural) (hAK : A ≤ K) : Function.Injective n.matrixAction := by
  intro x y hxy
  have hE : K ⊔ A ≤ K := sup_le le_rfl hAK
  let xK : K := ⟨x,hE x.property⟩
  let yK : K := ⟨y,hE y.property⟩
  have he : n.second xK = n.second yK := by
    rw [←n.matrixAction_second,←n.matrixAction_second]
    exact hxy
  exact Subtype.ext (congrArg (fun z : K => (z : Q)) (n.second.injective he))

theorem Data.NaturalTensor.OtherNatural.unique_actor
    (n : d.OtherNatural) (hAK : A ≤ K)
    (R B : Subgroup Q) (hR : IsPGroup 2 R) (hAR : A ≤ R) (hBR : B ≤ R) (hBK : B ≤ K)
    (hAe : IsElementaryTwo A) (hBe : IsElementaryTwo B)
    (hAr : rank A = 2) (hBr : rank B = 2)
    (hBd : fixedCodim d.tensor.constituent.toRepresentation (B.subgroupOf (K ⊔ A)) ≤ 1) :
    B = A := by
  let E := K ⊔ A
  let φ := n.matrixAction
  have hφ : Function.Injective φ := n.matrixAction_injective hAK
  have hAE : A ≤ E := le_sup_right
  have hBE : B ≤ E := hBK.trans le_sup_left
  have hoff (C : Subgroup Q) (hCE : C ≤ E) (he : IsElementaryTwo C) (hr : rank C = 2)
      (hd : fixedCodim d.tensor.constituent.toRepresentation (C.subgroupOf E) ≤ 1) :
      IsOffender (BinaryLinearThree.W.prod BinaryLinearThree.W) ((C.subgroupOf E).map φ) := by
    let := he.2
    have he₀ : IsElementaryTwo (C.subgroupOf E) :=
      ⟨fun hz => he.1 (by
        have hh := congrArg (Subgroup.map E.subtype) hz
        simpa only [map_subgroupOf_eq_of_le hCE,Subgroup.map_bot] using hh),
        IsElementaryAbelian.subgroupOf hCE⟩
    let := he₀.2
    have heM : IsElementaryTwo ((C.subgroupOf E).map φ) :=
      ⟨fun hz => he₀.1 (Subgroup.map_injective hφ (hz.trans (Subgroup.map_bot φ).symm)),
        IsElementaryAbelian.map φ⟩
    have hr₀ : rank (C.subgroupOf E) = 2 := by
      unfold rank
      rw [Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv]
      exact hr
    have hcod := fixedCodim_map_equivariant d.tensor.constituent.toRepresentation
      BinaryLinearThree.W φ n.coordinates
      (fun g v => by
        let k : K := ⟨g,(sup_le le_rfl hAK) g.property⟩
        have hh := n.second_action k v
        rw [←n.matrixAction_second] at hh
        exact hh) (C.subgroupOf E)
    refine ⟨heM,?_⟩
    rw [fixedCodim_prod,←hcod,rank_map_injective φ hφ,hr₀]
    omega
  have he := BinaryLinearThree.DoubledOffenders.eq_of_offenders_in_twoGroup
    ((R.subgroupOf E).map φ) ((B.subgroupOf E).map φ) ((A.subgroupOf E).map φ)
    (hR.comap_subtype.map φ) (map_mono (subgroupOf_mono E hBR))
    (map_mono (subgroupOf_mono E hAR)) (hoff B hBE hBe hBr hBd)
    (hoff A hAE hAe hAr d.tensor.displacement.le)
  have he₀ := Subgroup.map_injective hφ he
  have hh := congrArg (Subgroup.map E.subtype) he₀
  simpa only [map_subgroupOf_eq_of_le hBE,map_subgroupOf_eq_of_le hAE] using hh
end Representation.CommonChief
