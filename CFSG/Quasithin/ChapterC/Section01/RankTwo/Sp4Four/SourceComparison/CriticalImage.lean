module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.QuadraticAction
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter

/-!
# The original critical image in natural coordinates

The critical seed acts quadratically on its embedded moving cover and hence
on the marked ambient natural quotient. Over the field of four elements a
quadratic quotient image of order greater than two lies in the normal
symplectic component. Restriction gives its exact derived-symplectic model
homomorphism, retaining conjugation and the original image cardinality.
The quotient-image count equals the source's literal relative subgroup index.

Source: MS93 (3.3), first symplectic branch, printed p.867, using (3.2)(vi).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource
open Representation.SymplecticFourOrthogonalCover
variable {M J V : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The original quotient image has cardinality equal to its literal relative
index, even though the graph ambient group itself is infinite. -/
theorem quotient_image_card {G D : Type*} [Group G] [Group D]
    (A B Q : Subgroup G) (hAB : A ≤ B) (κ : B →* D)
    (hk : κ.ker.map B.subtype = Q) :
    Nat.card (κ.comp (inclusion hAB)).range = Q.relIndex A := by
  have hmap : (κ.comp (inclusion hAB)).range = (A.subgroupOf B).map κ := by
    rw [MonoidHom.range_comp, inclusion_range]
  rw [hmap, ←relIndex_ker]
  have hi := relIndex_map_map_of_injective κ.ker (A.subgroupOf B) B.subtype_injective
  rw [hk, map_subgroupOf_eq_of_le hAB] at hi
  exact hi.symm

omit [B.Normal] [Finite F] [CharP F 2] in
/-- Quadraticity of the critical actor descends through the actual ambient
cover projection, without assuming it already lies in the component. -/
theorem critical_ambient_quadratic (path : CriticalPath R geometry a z)
    (hb : 0 < geometry.b R)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹) :
    IsQuadratic (MovedSection.ambientAction s e) δ.range := by
  have hu := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_actor_quadratic
    path hb s.space.toRepresentation j hj hjr δ hδ
  intro x hx y hy v
  obtain ⟨w,rfl⟩ := hp.1 v
  have hh := congrArg (MovedSection.coverProjection s e) (hu x hx y hy w)
  simpa only [map_sub, MovedSection.coverProjection_ambient] using hh

/-- Once its original quotient image has order greater than two, the critical
actor has the exact inner model homomorphism required by the plane comparison. -/
theorem critical_inner_model_actor (path : CriticalPath R geometry a z)
    (hb : 0 < geometry.b R) (hF : Nat.card F = 4)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹)
    (hlarge : 2 < Nat.card δ.range) :
    ∃ β : Z R a →* L (K := F),
      Nat.card β.range = Nat.card δ.range ∧
      (∀ x, (e.groupEquiv.symm (β x) : J) = δ x) ∧
      (∀ x : Z R a, ∀ v : s.space.toSubmodule,
        j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
          (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹) := by
  have hcard : 2 < Nat.card F := by omega
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  have hfaith := MovedSection.ambientAction_faithful s e binaryNatural_injective hcent
  have hinner : δ.range ≤ B :=
    SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card hF B
      (hcent ▸ bot_le) (e.groupEquiv.trans d) (MovedSection.ambientAction s e) hfaith
      (fun b v => MovedSection.ambientAction_component s e b v)
      δ.range (critical_ambient_quadratic path hb s e hp j hj hjr δ hδ) hlarge
  let β := e.groupEquiv.toMonoidHom.comp (δ.codRestrict B (fun x => hinner ⟨x,rfl⟩))
  have he (x) : (e.groupEquiv.symm (β x) : J) = δ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δ x,_⟩) : J) = δ x
    rw [e.groupEquiv.symm_apply_apply]
  have hk : β.ker = δ.ker := by
    ext x
    change e.groupEquiv ⟨δ x,_⟩ = 1 ↔ δ x = 1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  refine ⟨β,?_,he,?_⟩
  · rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv,
      ←Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, hk]
  · intro x v
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) v)) = _
    rw [he]
    exact hδ x v

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
