module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.VertexCorrection
public import Theory.GroupTheory.Recognition.QuasithinM23.HeptadComparison

/-!
# Recognition after the original vertex comparison

Apply core correction to the original coset system and its fixed heptad marking.
The corrected vertex map agrees on the entire Ix and preserves the original edge
fixer. The resulting similarity, edge rigidity and native cycle base give an
actual G equivalence with M23. It maps the whole original vertex group to the
pair stabilizer, the original L to the edge fixer, and extends the fixed heptad
marking on the entire local group I.

The source application constructs this same coset system and all its markings
under either compatible linear-amalgam orientation. It is a conditional reduction:
existence of the initial vertex comparison preserving Ix and L and agreeing on
O2(J) remains to be proved. It does not establish unconditional source 5.2.10.

Source: Aschbacher--Smith 5.2.20(5) and the proof of 5.2.10, printed pp.656--658.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G]

/-- The core correction suffices for actual ambient recognition. The result
retains the entire original vertex and edge subgroups, and the same local map. -/
theorem heptad_marked_recognition_of_core_comparison {V : Type*} [MulAction G V]
    (U : System G V) (J : Subgroup G) (hUJ : U.H ≤ J)
    (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hUL : J.pCoreIn 2 ≤ U.edgeGroup)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer)
    (hvM : ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (hesM : ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
      fourEdgeStabilizer.subgroupOf heptadStabilizer)
    (hrigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup))
    (β : U.vertexGroup ≃* pairStabilizer)
    (hβR : ((U.H ⊓ U.vertexGroup).subgroupOf U.vertexGroup).map β.toMonoidHom =
      fourPairStabilizer.subgroupOf pairStabilizer)
    (hβcore : ∀ r : (U.H ⊓ U.vertexGroup : Subgroup G), (r : G) ∈ J.pCoreIn 2 →
      (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23))
    (hβedge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ e : G ≃* Sporadic.Mathieu.M23,
      U.vertexGroup.map e.toMonoidHom = pairStabilizer ∧
      U.edgeGroup.map e.toMonoidHom = standardSystem.edgeGroup ∧
      ∀ a : U.H, e a = (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23) := by
  obtain ⟨β',hagree,hedge⟩ := heptad_marked_vertex_correction J
    (U.H ⊓ U.vertexGroup) U.vertexGroup U.edgeGroup (inf_le_left.trans hUJ)
    inf_le_right ζ hcore hvM hUL β hβR hβcore hβedge
  obtain ⟨e,he,_⟩ := QuasithinM23.heptad_marked_recognition U J hUJ ζ hIm hvM hesM hrigid
    β' hagree hedge
  refine ⟨e,?_,?_,he.2⟩
  · ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      change e a ∈ pairStabilizer
      rw [he.1 ⟨a,ha⟩]
      exact (β' ⟨a,ha⟩).property
    · intro hg
      refine ⟨β'.symm ⟨g,hg⟩,(β'.symm ⟨g,hg⟩).property,?_⟩
      change e (β'.symm ⟨g,hg⟩) = g
      rw [he.1,β'.apply_symm_apply]
  · ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      change e a ∈ standardSystem.edgeGroup
      rw [he.1 ⟨a,ha.1⟩]
      exact (hedge ⟨a,ha.1⟩).mp ha
    · intro hg
      have hgp : g ∈ pairStabilizer := by
        rw [standardSystem_edgeGroup] at hg
        exact hg.1
      let a := β'.symm ⟨g,hgp⟩
      have ha : (a : G) ∈ U.edgeGroup := (hedge a).mpr (by
        change (β' (β'.symm ⟨g,hgp⟩) : Sporadic.Mathieu.M23) ∈ _
        rw [β'.apply_symm_apply]
        exact hg)
      refine ⟨a,ha,?_⟩
      change e a = g
      rw [he.1]
      exact congrArg Subtype.val (β'.apply_symm_apply ⟨g,hgp⟩)


variable [Finite G]

/-- The original source system has all the data needed for ambient recognition
apart from an initial vertex comparison preserving Ix and the edge fixer and
agreeing with its heptad marking on the sixteen-core. This conditional reduction
does not assert existence of that comparison. -/
theorem Preparation.linear_nonmaximal_recognition_reduction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (hUJ : U.H ≤ J),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      ∀ β : U.vertexGroup ≃* pairStabilizer,
        ((U.H ⊓ U.vertexGroup).subgroupOf U.vertexGroup).map β.toMonoidHom =
          fourPairStabilizer.subgroupOf pairStabilizer →
        (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G), (r : G) ∈ J.pCoreIn 2 →
          (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
            (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) →
        (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
          (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) →
        ∃ e : G ≃* Sporadic.Mathieu.M23,
          U.vertexGroup.map e.toMonoidHom = pairStabilizer ∧
          U.edgeGroup.map e.toMonoidHom = standardSystem.edgeGroup ∧
          ∀ a : U.H, e a = (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23) := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,_⟩ :=
    d.linear_nonmaximal_coset_core_correction h hH hp F hm hF he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,?_⟩
  intro β hβR hβcore hβedge
  exact heptad_marked_recognition_of_core_comparison U J hUJ ζ hcore
    (hcoreEdge.trans inf_le_right) hIm hvM hesM hrigid β hβR hβcore hβedge

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
