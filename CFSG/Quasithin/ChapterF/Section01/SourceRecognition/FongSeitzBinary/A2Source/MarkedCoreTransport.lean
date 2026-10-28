module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.CoreSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# Natural-core coordinates through an independent amalgam marking

Restrict the supplied full endpoint isomorphism to its intrinsic two-core,
then embed it as the actual parabolic core of the independent finite quotient.
The resulting coordinates retain the original actor and its original SL₂
quotient in the conjugation equation. No ambient homomorphism from the
original completion, and no identification of the actor with Lᵢ, is used.
Both endpoint embeddings agree on the source core intersection because they
use the same middle map on the whole original Sylow. The two actual target
cores therefore generate precisely the specified split U.

MarkedPlane and MarkedAffineIncidence use these local transports to construct
the independent-quotient incidence bridge; MarkedRecognition applies its roots.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224;
AS F.1.1--3. The original-source consumer is originalCoordinates_conjugate.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedCoreTransport
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {G Y : Type*} [Group G] [Group Y]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}
  {k W : Type*} [Field k] [Finite k] [CharP k 2] [AddCommGroup W] [Module (ZMod 2) W]
local instance transportFieldAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)
  (h : LocallyRankOneTriple P B) (hcore : Q (family P) v = Z (family P) v)
  (hcenter : centerIn c.actor = ⊥) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
  (J : Subgroup Y) (e : stabilizer (family P) v ≃* J)

/-- The local marking transports the full intrinsic core to its actual ambient image. -/
def coreEquiv : Q (family P) v ≃* J.pCoreIn 2 :=
  ((pCore 2 (stabilizer (family P) v)).equivMapOfInjective _ Subtype.val_injective).symm.trans
    ((LocalCoreTransport.coreEquiv 2 e).trans
      ((pCore 2 J).equivMapOfInjective _ Subtype.val_injective))

/-- Evaluation follows the given full-endpoint marking, not a local-factor identification. -/
theorem coreEquiv_apply (a : Q (family P) v) :
    (coreEquiv J e a : Y) = e ⟨a,Q_le_stabilizer _ _ a.property⟩ := by
  let f := (pCore 2 (stabilizer (family P) v)).equivMapOfInjective
    (stabilizer (family P) v).subtype Subtype.val_injective
  change (e (f.symm a : stabilizer (family P) v) : Y) = _
  apply congrArg (fun z : stabilizer (family P) v => (e z : Y))
  apply Subtype.ext
  exact congrArg (fun z : Q (family P) v => (z : G)) (f.apply_symm_apply a)

/-- The original one-field coordinates on the independently marked quotient core. -/
def coordinates : J.pCoreIn 2 ≃* Multiplicative (Fin 2 → k) :=
  (coreEquiv J e).symm.trans (A2Source.coreCoordinates c h hcore hcenter E)

/-- The literal marked local map preserves each original core parameter. -/
theorem coordinates_apply (a : Q (family P) v) :
    coordinates c h hcore hcenter E J e (coreEquiv J e a) =
      A2Source.coreCoordinates c h hcore hcenter E a := by
  exact congrArg (A2Source.coreCoordinates c h hcore hcenter E) ((coreEquiv J e).symm_apply_apply a)

/-- Embed the actual original actor through its own full endpoint. -/
def actorMap : c.actor →* Y :=
  J.subtype.comp (e.toMonoidHom.comp (inclusion c.actor_le))

/-- Transport of the natural action retains the SAME original SL₂ quotient. -/
theorem coordinates_conjugate (a : c.actor) (x : J.pCoreIn 2) :
    ∃ y : J.pCoreIn 2,
      (y : Y) = actorMap c J e a * (x : Y) * (actorMap c J e a)⁻¹ ∧
      (coordinates c h hcore hcenter E J e y).toAdd =
        Matrix.mulVec (c.quotient a).val (coordinates c h hcore hcenter E J e x).toAdd := by
  obtain ⟨z,rfl⟩ := (coreEquiv J e).surjective x
  obtain ⟨t,ht,hφ⟩ := coreCoordinates_conjugate c h hcore hcenter E a z
  refine ⟨coreEquiv J e t,?_,?_⟩
  · rw [coreEquiv_apply,coreEquiv_apply]
    have he : (⟨t,Q_le_stabilizer _ _ t.property⟩ : stabilizer (family P) v) =
        ⟨a,c.actor_le a.property⟩ * ⟨z,Q_le_stabilizer _ _ z.property⟩ *
          (⟨a,c.actor_le a.property⟩ : stabilizer (family P) v)⁻¹ := Subtype.ext ht
    rw [he,map_mul,map_mul,map_inv]
    rfl
  · rw [coordinates_apply,coordinates_apply]
    exact hφ

section Original
variable {H X : Type*} [Group H] [Group X] {L : Fin 2 → Subgroup H} {S : Subgroup H}
  {PX : Fin 2 → Subgroup X} (d : MarkedQuotient PX)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)

/-- The original vertex stabilizer is the full original endpoint in its generated carrier. -/
theorem original_stabilizer (i : Bool) :
    stabilizer (fullFamily L S) (base (fullFamily L S) i) =
      (parabolic L S (if i then 1 else 0)).subgroupOf (generated L S) := by
  simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
  cases i <;> rfl

/-- Both original generated endpoints follow the independent full amalgam marking. -/
def endpointMarking (i : Bool) :
    stabilizer (fullFamily L S) (base (fullFamily L S) i) ≃*
      d.tits.standardParabolic {d.simple (if i then 1 else 0)} :=
  (MulEquiv.subgroupCongr (original_stabilizer (L := L) (S := S) i)).trans
    ((subgroupOfEquivOfLe (parabolic_le_generated (if i then 1 else 0))).trans
      (MarkedLocal.endpoint d mark (if i then 1 else 0)))

/-- Exact right-endpoint evaluation, without an ambient homomorphism or descent premise. -/
theorem endpointMarking_right (a : stabilizer (fullFamily L S) (base (fullFamily L S) true)) :
    (endpointMarking d mark true a : X ⧸ d.D) =
      (mark.right ⟨(a : generated L S),by
        exact (original_stabilizer (L := L) (S := S) true).le a.property⟩ : X ⧸ d.D) := rfl

/-- Exact left-endpoint evaluation, using the other map of the SAME marking. -/
theorem endpointMarking_left (a : stabilizer (fullFamily L S) (base (fullFamily L S) false)) :
    (endpointMarking d mark false a : X ⧸ d.D) =
      (mark.left ⟨(a : generated L S),by
        exact (original_stabilizer (L := L) (S := S) false).le a.property⟩ : X ⧸ d.D) := rfl

/-- Each original core maps to the actual full parabolic core in the independent quotient. -/
def originalCoreEquiv (i : Bool) :
    Q (fullFamily L S) (base (fullFamily L S) i) ≃*
      (d.tits.standardParabolic {d.simple (if i then 1 else 0)}).pCoreIn 2 :=
  coreEquiv _ (endpointMarking d mark i)

/-- The full-core transport is literally the supplied local marking. -/
theorem originalCoreEquiv_apply (i : Bool)
    (a : Q (fullFamily L S) (base (fullFamily L S) i)) :
    (originalCoreEquiv d mark i a : X ⧸ d.D) =
      endpointMarking d mark i ⟨a,Q_le_stabilizer _ _ a.property⟩ :=
  coreEquiv_apply _ _ a

/-- The ambient core embedding induced by the independent marking. -/
def originalCoreMap (i : Bool) :
    Q (fullFamily L S) (base (fullFamily L S) i) →* X ⧸ d.D :=
  ((d.tits.standardParabolic {d.simple (if i then 1 else 0)}).pCoreIn 2).subtype.comp
    (originalCoreEquiv d mark i).toMonoidHom

/-- This is the entire actual target core, not merely an isomorphic subgroup. -/
theorem originalCoreMap_range (i : Bool) :
    (originalCoreMap d mark i).range =
      (d.tits.standardParabolic {d.simple (if i then 1 else 0)}).pCoreIn 2 := by
  rw [originalCoreMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
    (originalCoreEquiv d mark i).surjective,←MonoidHom.range_eq_map,range_subtype]

/-- Every source-core element uses the original common Sylow's literal middle map.
Consequently the independently embedded cores agree on their full intersection. -/
theorem originalCoreMap_sylow (hf : HypothesisF11 L S) (i : Bool)
    (a : Q (fullFamily L S) (base (fullFamily L S) i)) :
    originalCoreMap d mark i a = MarkedLocal.sylowMap d mark hf
      ⟨(a : generated L S),ProjectiveCoordinates.original_core_le_sylow hf i a.property⟩ := by
  change (originalCoreEquiv d mark i a : X ⧸ d.D) = _
  rw [originalCoreEquiv_apply]
  cases i
  · rw [endpointMarking_left]
    simpa only [MarkedLocal.endpointMap,MarkedLocal.endpoint, Fin.cases_zero, Fin.cases_succ,
      MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,Subgroup.coe_subtype] using
      MarkedLocal.endpoint_sylow d mark hf 0
        ⟨(a : generated L S),ProjectiveCoordinates.original_core_le_sylow hf false a.property⟩
  · rw [endpointMarking_right]
    let s : S := ⟨(a : generated L S),ProjectiveCoordinates.original_core_le_sylow hf true a.property⟩
    let b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup H) :=
      ⟨s,(show S ≤ parabolic L S 0 from le_sup_right.trans le_sup_left) s.property,
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left) s.property⟩
    have hr (u : d.tits.B) : (d.standardAmalgam.right u : X ⧸ d.D) = u := by
      obtain ⟨t,rfl⟩ := d.markedIso.middle.surjective u
      rw [←d.markedIso.right_commutes,d.markedIso_right_apply,d.markedIso_middle_apply]
      rfl
    exact (congrArg Subtype.val (mark.right_commutes b)).trans (hr (mark.middle b))

/-- The two core embeddings coincide on their literal original overlap. -/
theorem originalCoreMap_intersection (hf : HypothesisF11 L S)
    (a : (Q (fullFamily L S) (base (fullFamily L S) false) ⊓
      Q (fullFamily L S) (base (fullFamily L S) true) : Subgroup (generated L S))) :
    originalCoreMap d mark false ⟨a,a.property.1⟩ =
      originalCoreMap d mark true ⟨a,a.property.2⟩ := by
  rw [originalCoreMap_sylow d mark hf,originalCoreMap_sylow d mark hf]

variable (hf : HypothesisF11 L S)
  {k₀ W₀ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀]
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k W)
  (hc : centerIn c₁.actor = ⊥) (E₁ : W ≃ₗ[ZMod 2] (Fin 2 → k))

include mark hf c₀ c₁ in
/-- The original two natural cores generate the specified U in the independent quotient.
The agreement on the entire source Sylow is supplied by the actual middle marking. -/
theorem original_core_sup_eq_unipotent (split : SplitData d.tits) :
    (d.tits.standardParabolic {d.simple 0}).pCoreIn 2 ⊔
      (d.tits.standardParabolic {d.simple 1}).pCoreIn 2 = split.U := by
  let S' := S.subgroupOf (generated L S)
  let es : S' ≃* S := subgroupOfEquivOfLe (show S ≤ generated L S from le_sup_right)
  let f := (MarkedLocal.sylowMap d mark hf).comp es.toMonoidHom
  have hr (i : Bool) :
      ((Q (fullFamily L S) (base (fullFamily L S) i)).subgroupOf S').map f =
        (originalCoreMap d mark i).range := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      refine ⟨⟨a,ha⟩,?_⟩
      exact originalCoreMap_sylow d mark hf i ⟨a,ha⟩
    · rintro _ ⟨a,rfl⟩
      refine ⟨⟨a,ProjectiveCoordinates.original_core_le_sylow hf i a.property⟩,a.property,?_⟩
      exact (originalCoreMap_sylow d mark hf i a).symm
  have he : (Q (fullFamily L S) (base (fullFamily L S) false)).subgroupOf S' ⊔
      (Q (fullFamily L S) (base (fullFamily L S) true)).subgroupOf S' = ⊤ := by
    rw [←subgroupOf_sup (ProjectiveCoordinates.original_core_le_sylow hf false)
      (ProjectiveCoordinates.original_core_le_sylow hf true),
      ProjectiveCoordinates.original_core_sup_eq_sylow hf c₀ c₁]
    exact subgroupOf_self S'
  have hh := congrArg (Subgroup.map f) he
  rw [Subgroup.map_sup,hr false,hr true,originalCoreMap_range,originalCoreMap_range,
    ←MonoidHom.range_eq_map] at hh
  have hfU : f.range = split.U := by
    change ((MarkedLocal.sylowMap d mark hf).comp es.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr es.surjective,
      ←MonoidHom.range_eq_map,MarkedLocal.sylow_range d mark hf split]
  exact hh.trans hfU

/-- One-field natural coordinates on the independently marked quotient's actual right core. -/
def originalCoordinates : (d.tits.standardParabolic {d.simple 1}).pCoreIn 2 ≃*
    Multiplicative (Fin 2 → k) :=
  coordinates c₁ hf.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions hf.generatedLocallyRankOneTriple c₀ c₁).2 hc E₁
    _ (endpointMarking d mark true)

/-- The natural action is transported through the original actor, retaining its given SL₂ map. -/
theorem originalCoordinates_conjugate (a : c₁.actor)
    (x : (d.tits.standardParabolic {d.simple 1}).pCoreIn 2) :
    ∃ y : (d.tits.standardParabolic {d.simple 1}).pCoreIn 2,
      (y : X ⧸ d.D) = actorMap c₁ _ (endpointMarking d mark true) a * (x : X ⧸ d.D) *
        (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ ∧
      (originalCoordinates d mark hf c₀ c₁ hc E₁ y).toAdd =
        Matrix.mulVec (c₁.quotient a).val (originalCoordinates d mark hf c₀ c₁ hc E₁ x).toAdd :=
  coordinates_conjugate c₁ hf.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions hf.generatedLocallyRankOneTriple c₀ c₁).2 hc E₁
    _ (endpointMarking d mark true) a x

end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedCoreTransport
