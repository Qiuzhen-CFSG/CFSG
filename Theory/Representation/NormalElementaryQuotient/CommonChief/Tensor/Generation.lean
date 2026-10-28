module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.WholeMoved
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.ActorFamily
public import Theory.Representation.PSL3Two.SylowAxisGeneration

/-!
# Parabolic generation on the whole natural tensor

The original zero-denominator projection and tensor coordinates identify
the whole moved module with three copies of the same natural constituent.
Pointwise fixation of the constituent's Sylow fixed line consequently fixes
all Sylow-fixed vectors of the whole module. Transporting the natural
point-parabolic and common-axis generation retains the original second
factor, the original actor, and its full normalizer.

Source: Aschbacher--Smith 13.1.9, printed p.871, final generation argument.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {t : c.NaturalTensor hc}

@[expose] def Data.NaturalTensor.OtherNatural.wholeCopies (o : t.OtherNatural)
    (hz : c.lower = ⊥) : c.upper.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → BinaryLinearThree.Vector) :=
  ((c.wholeSectionEquiv hz).toLinearEquiv.trans t.tensor.copyCoordinates).trans
    (LinearEquiv.piCongrRight fun _ => o.coordinates)

omit [FiniteDimensional (ZMod 2) V] in
theorem Data.NaturalTensor.OtherNatural.wholeCopies_action (o : t.OtherNatural)
    (hz : c.lower = ⊥) (k : K) (v : c.upper.toSubmodule) :
    o.wholeCopies hz (c.upper.toRepresentation
      (inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k) v) =
      fun i => BinaryLinearThree.W (o.second k) (o.wholeCopies hz v i) := by
  let kE := inclusion (show K ≤ K ⊔ A from le_sup_left) k
  have he := LinearMap.congr_fun ((c.wholeSectionEquiv hz).isIntertwining'
    (inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k)) v
  have he' : c.wholeSectionEquiv hz (c.upper.toRepresentation
      (inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k) v) =
      c.productRepresentation hc (kE,1) (c.wholeSectionEquiv hz v) := by
    rw [c.productRepresentation_left]
    exact he
  funext i
  change o.coordinates (t.tensor.copyCoordinates (c.wholeSectionEquiv hz _) i) = _
  rw [he',t.tensor.copyCoordinates_action,o.second_action]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem Data.NaturalTensor.OtherNatural.matrixActor_eq_map (o : t.OtherNatural)
    (hAK : A ≤ K) : o.matrixActor = (A.subgroupOf K).map o.second.toMonoidHom := by
  rw [o.matrixActor_eq]
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨⟨a.val,hAK ha⟩,ha,?_⟩
    exact (o.matrixAction_second ⟨a.val,hAK ha⟩).symm
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨inclusion (show K ≤ K ⊔ A from le_sup_left) a,ha,?_⟩
    exact o.matrixAction_second a

/-- The original upper module's Sylow-fixed centralizer and the original
actor normalizer generate the full second factor. -/
theorem Data.NaturalTensor.OtherNatural.whole_generation [Finite Q] (o : t.OtherNatural)
    (hz : c.lower = ⊥) (hAK : A ≤ K) (P : Sylow 2 K)
    (hAP : A.subgroupOf K ≤ (P : Subgroup K))
    (haxis : o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2) :
    subspaceKernel (ρ.comp K.subtype)
      (c.upper.toSubmodule ⊓ fixedSpace (ρ.comp K.subtype) (P : Subgroup K)) ⊤ ⊔
      normalizer (A.subgroupOf K : Set K) = ⊤ := by
  let Pm := P.mapSurjective (f := o.second.toMonoidHom) o.second.surjective
  have hAm : o.matrixActor ≤ (Pm : Subgroup BinaryLinearThree.Group) := by
    rw [o.matrixActor_eq_map hAK]
    exact map_mono hAP
  have hdim := o.matrixActor_fixed_plane
  have hgen := BinaryLinearThree.sylow_fixed_axis_generation Pm o.matrixActor hAm hdim haxis
  let F := subspaceKernel (ρ.comp K.subtype)
    (c.upper.toSubmodule ⊓ fixedSpace (ρ.comp K.subtype) (P : Subgroup K)) ⊤
  let N := normalizer (A.subgroupOf K : Set K)
  have hnorm : normalizer (o.matrixActor : Set BinaryLinearThree.Group) = N.map o.second.toMonoidHom := by
    rw [o.matrixActor_eq_map hAK, map_normalizer_eq_of_bijective _ o.second.bijective]
  have hfix : subspaceKernel BinaryLinearThree.W
      (fixedSpace BinaryLinearThree.W (Pm : Subgroup BinaryLinearThree.Group)) ⊤ ≤
      F.map o.second.toMonoidHom := by
    intro x hx
    let k := o.second.symm x
    refine ⟨k,⟨mem_top _,?_⟩,o.second.apply_symm_apply x⟩
    intro v hv
    let vU : c.upper.toSubmodule := ⟨v,hv.1⟩
    let kF := inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k
    have he : c.upper.toRepresentation kF vU = vU := by
      apply (o.wholeCopies hz).injective
      rw [o.wholeCopies_action]
      funext i
      change BinaryLinearThree.W (o.second (o.second.symm x)) _ = _
      rw [o.second.apply_symm_apply]
      apply hx.2
      intro p
      obtain ⟨a,ha,hea⟩ := p.property
      have haf : c.upper.toRepresentation
          (inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) a) vU = vU :=
        Subtype.ext (hv.2 ⟨a,ha⟩)
      have hh := congrArg (fun w => o.wholeCopies hz w i) haf
      rw [o.wholeCopies_action] at hh
      change BinaryLinearThree.W (p : BinaryLinearThree.Group) _ = _
      rw [←hea]
      exact hh
    exact congrArg Subtype.val he
  apply o.second.mapSubgroup.injective
  change (F ⊔ N).map o.second.toMonoidHom = (⊤ : Subgroup K).map o.second.toMonoidHom
  rw [Subgroup.map_sup,map_top_of_surjective _ o.second.surjective]
  apply top_unique
  rw [←hgen]
  exact sup_le_sup hfix hnorm.le
end Representation.CommonChief
