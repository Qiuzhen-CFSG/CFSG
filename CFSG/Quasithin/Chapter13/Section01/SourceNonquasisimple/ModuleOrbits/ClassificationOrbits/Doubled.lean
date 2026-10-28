module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.Natural
public import Theory.Representation.SL3DoubledNaturalOffenders.BinaryNormalizer

/-!
# The classified doubled natural module in the original LT action

The actual normalizer action on U normalizes its marked component image.
The binary doubled-natural normalizer theorem factors each operator into
natural and multiplicity factors. On LT the multiplicity image equals the
image of T, hence is a two-group. Simultaneous swap coordinates therefore
construct the precise DoubledNaturalMarking consumed by the orbit, core,
and quaternion-action theorems. All maps retain the original conjugation
and the original quotient on L.

Source: Aschbacher--Smith 13.1.10(3) and 13.1.12, pp.871--874.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource
open Representation.SL3DoubledNaturalOffenders
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}
variable [IsElementaryAbelian 2 (normalizerMoved L)]

omit [Finite G] in
/-- Construct the full LT orbit marking from the two original natural copies. -/
theorem doubledOrbitMarking
    (hT : (T : Subgroup G) ≤ Subgroup.normalizer (L : Set G))
    (a : ActionEquiv (componentRepresentation (L := L))
      (repeated (linearNatural BinaryField.two 3) 2)) :
    Nonempty (LinearThree.DoubledNaturalMarking T L) := by
  let F := ZMod 2
  let M := Subgroup.normalizer (L : Set G)
  let A := L.subgroupOf M
  let e := a.linearEquiv
  let ρ := Representation.elementaryRepresentation (p := 2) (ModuleOrbits.action L)
  let ν : Representation F M (Space F) := e.conjRingEquiv.toMonoidHom.comp ρ
  let k : L →* SL F := a.groupEquiv.toMonoidHom.comp (componentAction L).rangeRestrict
  have hk : Function.Surjective k :=
    a.groupEquiv.surjective.comp (componentAction L).rangeRestrict_surjective
  have he (m : M) (v : normalizerMoved L) :
      e (Additive.ofMul (ModuleOrbits.action L m v)) = ν m (e (Additive.ofMul v)) := by
    change e _ = e (ρ m (e.symm (e (Additive.ofMul v))))
    rw [e.symm_apply_apply]
    rfl
  have hcomp (l : L) : ν.asGroupHom (inclusion L.le_normalizer l) =
      (representation F).asGroupHom (k l) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := e.surjective v
    exact (he (inclusion L.le_normalizer l) w.toMul).symm.trans
      (a.intertwines ((componentAction L).rangeRestrict l) w)
  have hrange : A.map ν.asGroupHom = component F := by
    have hc : ν.asGroupHom.comp (inclusion L.le_normalizer) =
        (representation F).asGroupHom.comp k := MonoidHom.ext hcomp
    rw [show A = (inclusion L.le_normalizer).range from (inclusion_range L.le_normalizer).symm,
      ← MonoidHom.range_comp,hc,MonoidHom.range_comp,k.range_eq_top_of_surjective hk,
      ← MonoidHom.range_eq_map]
    rfl
  have hn (m : M) : ν.asGroupHom m ∈ normalizer F := by
    let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
    have hm : m ∈ Subgroup.normalizer (A : Set M) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    have hh := (Subgroup.le_normalizer_map ν.asGroupHom)
      (show ν.asGroupHom m ∈ (Subgroup.normalizer (A : Set M)).map ν.asGroupHom from
        ⟨m,hm,rfl⟩)
    rwa [hrange] at hh
  let q : M →* SL F × MultiplicitySL F := binaryNormalizerEquiv.toMonoidHom.comp
    (ν.asGroupHom.codRestrict (normalizer F) hn)
  have hq (m : M) : (tensorRepresentation F).asGroupHom (q m) = ν.asGroupHom m := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (binaryNormalizerEquiv_action ⟨ν.asGroupHom m,hn m⟩ v).symm
  have hqL (l : L) : q (inclusion L.le_normalizer l) = (k l,1) := by
    apply binary_tensor_injective
    rw [hq,hcomp]
    apply Units.ext
    change representation F (k l) = representation F (k l) * multiplicityRepresentation F 1
    rw [map_one,mul_one]
  have hJ : L ⊔ (T : Subgroup G) ≤ M := sup_le L.le_normalizer hT
  let qJ := q.comp (inclusion hJ)
  let q₂ := (MonoidHom.snd (SL F) (MultiplicitySL F)).comp qJ
  let qT := q₂.comp (inclusion (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
  have hq₂ : q₂.range = qT.range := by
    apply le_antisymm
    · rintro _ ⟨m,rfl⟩
      have hm := m.property
      rw [← SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hT] at hm
      obtain ⟨l,hl,t,ht,helt⟩ := hm
      let lL : L := ⟨l,hl⟩
      let tT : T := ⟨t,ht⟩
      have hem : m = inclusion le_sup_left lL * inclusion le_sup_right tT :=
        Subtype.ext helt.symm
      refine ⟨tT,?_⟩
      rw [hem,map_mul]
      have hz : q₂ (inclusion le_sup_left lL) = 1 := congrArg Prod.snd (hqL lL)
      rw [hz,one_mul]
      rfl
    · rintro _ ⟨t,rfl⟩
      exact ⟨inclusion le_sup_right t,rfl⟩
  have hp : IsPGroup 2 q₂.range := by
    rw [hq₂]
    exact T.isPGroup'.of_surjective qT.rangeRestrict qT.rangeRestrict_surjective
  obtain ⟨b,r,hr,hrL⟩ := BinaryNormalizer.two_group_extension qJ hp
  refine ⟨{ invariant := hJ
            quotient := r
            component_quotient := k
            component_surjective := hk
            component_eq := ?_
            coordinates := (e.trans b).toAddEquiv.toMultiplicative
            equivariant := ?_ }⟩
  · intro l
    have hh := hrL (inclusion le_sup_left l) (congrArg Prod.snd (hqL l))
    exact hh.trans (congrArg (fun g : SL F × MultiplicitySL F => (g.1,(1 : Equiv.Perm (Fin 2))))
      (hqL l))
  · intro m v
    change b (e (Additive.ofMul (ModuleOrbits.action L (inclusion hJ m) v))) =
      BinaryOrbits.outerRepresentation (r m) (b (e (Additive.ofMul v)))
    rw [he]
    exact (congrArg (fun f : (Module.End F (Space F))ˣ => b ((f : Module.End F (Space F))
      (e (Additive.ofMul v)))) (hq (inclusion hJ m)).symm).trans (hr m _)

/-- The two-copy classification row supplies both literal centralizer interfaces. -/
theorem centralizer_inputs_of_two_copies {p : ℕ} [Fact p.Prime]
    (h : Context T L p)
    (ha : IsRepeatedLinearNatural (componentRepresentation (L := L)) BinaryField.two 3 2) :
    OrbitFacts T L p ∧ SieveActions h := by
  obtain ⟨a⟩ := ha
  obtain ⟨d⟩ := doubledOrbitMarking h.sylow_normalizes a
  exact ⟨d.orbitFacts h,d.sieveActions h⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
