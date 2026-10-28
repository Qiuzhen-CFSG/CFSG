module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# The Sylow marking of the lifted rank-one Borel

The component is normal only inside H. Intersect the given Sylow subgroup
with that component, then map it through the literal H/O₂(H) projection.
The inverse image in K of its normalizer contains the component Sylow,
which therefore restricts to a Sylow subgroup of the lifted Borel.

For PSL₂(4), this normalizer is precisely the rank-one Borel. These
constructions supply the two Borel markings used by the five-point overlap
argument, without presuming that the overlap is a point stabilizer.
Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
open HigherFieldReduction
variable {G : Type*} [Group G] [Finite G]

/-- Intersect the source Sylow subgroup with a relatively normal component. -/
theorem exists_component_sylow_in_source (H K : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] (T : Sylow 2 H) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤
      (T : Subgroup H).map H.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e := subgroupOfEquivOfLe hKH
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hS] at hy
  exact ⟨y.val, hy, rfl⟩

/-- The Sylow image uses the source star quotient, including its actual kernel. -/
noncomputable def componentStarSylow (H K : Subgroup G) (hKH : K ≤ H)
    (S : Sylow 2 K) : Sylow 2 (Source.starImage H K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := starHom H K hKH
  let e := MulEquiv.subgroupCongr (range_starHom H K hKH)
  exact S.mapSurjective (f := e.toMonoidHom.comp f.rangeRestrict)
    (e.surjective.comp f.rangeRestrict_surjective)

/-- The actual ambient image of the component Sylow normalizer. -/
def componentBorelImage (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K) :
    Subgroup (Source.Hstar H) :=
  (normalizer (componentStarSylow H K hKH S : Set (Source.starImage H K))).map
    (Source.starImage H K).subtype

/-- The Borel is lifted inside K, not inside the whole local group H. -/
def componentBorel (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K) : Subgroup G :=
  borelLift H K hKH (componentBorelImage H K hKH S)

/-- Both the literal star normalizer identity and the source Sylow supplement.
No isomorphism between B₀ and its image is used. -/
theorem componentBorel_marking (H K T : Subgroup G) (hKH : K ≤ H)
    (S : Sylow 2 K) (hST : (S : Subgroup K).map K.subtype ≤ T) :
    componentBorel H K hKH S ≤ H ∧
    Source.starImage H (componentBorel H K hKH S) = componentBorelImage H K hKH S ∧
    ∃ U : Sylow 2 (componentBorel H K hKH S),
      (U : Subgroup (componentBorel H K hKH S)).map
        (componentBorel H K hKH S).subtype ≤ T := by
  let f := starHom H K hKH
  let e := MulEquiv.subgroupCongr (range_starHom H K hKH)
  let g := e.toMonoidHom.comp f.rangeRestrict
  let B₀ := componentBorel H K hKH S
  have hBK : B₀ ≤ K := borelLift_le H K hKH _
  have hSB : (S : Subgroup K) ≤ B₀.subgroupOf K := by
    intro x hx
    apply mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    change f x ∈ componentBorelImage H K hKH S
    apply mem_map.mpr
    refine ⟨g x, ?_, rfl⟩
    apply le_normalizer
    exact mem_map.mpr ⟨x, hx, rfl⟩
  let U := S.comapOfInjective (inclusion hBK) (inclusion_injective hBK)
    (by
      intro x hx
      exact ⟨⟨x.val, hSB hx⟩, rfl⟩)
  refine ⟨hBK.trans hKH, starImage_borelLift H K hKH _ (map_subtype_le _), U, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hST ⟨inclusion hBK x, hx, rfl⟩

/-- The source Sylow hypothesis discharges the supplement choice. Relative
normality in H suffices; K need not be normal in the ambient simple group. -/
theorem exists_componentBorel_marking (H K : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) :
    ∃ (S : Sylow 2 K) (U : Sylow 2 (componentBorel H K hKH S)),
      componentBorel H K hKH S ≤ H ∧
      Source.starImage H (componentBorel H K hKH S) = componentBorelImage H K hKH S ∧
      (U : Subgroup (componentBorel H K hKH S)).map
        (componentBorel H K hKH S).subtype ≤ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := exists_component_sylow_in_source H K hKH (T.subtype hTH)
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hS
  obtain ⟨hH, hstar, U, hU⟩ := componentBorel_marking H K T hKH S hST
  exact ⟨S, U, hH, hstar, hU⟩

/-- The image of the intrinsic component Sylow is the literal ambient star image. -/
theorem componentStarSylow_image (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K) :
    (componentStarSylow H K hKH S : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype = Source.starImage H ((S : Subgroup K).map K.subtype) := by
  rw [starImage_map_subtype H K hKH]
  change ((S : Subgroup K).map _).map _ = _
  rw [map_map]
  rfl

/-- The selected Sylow is exactly T* ∩ K*, so the Borel marking uses the
specified source Sylow, rather than an independently chosen conjugate. -/
theorem componentStarSylow_source_intersection (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (T : Sylow 2 G) (hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G)) :
    (componentStarSylow H K hKH S : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype = Source.starImage H T ⊓ Source.starImage H K := by
  have he := componentStarSylow_image H K hKH S
  let A := (Source.starImage H T).subgroupOf (Source.starImage H K)
  have hA : IsPGroup 2 A := ((T.isPGroup'.comap_of_injective H.subtype H.subtype_injective).map
    (QuotientGroup.mk' (pCore 2 H))).comap_of_injective
    (Source.starImage H K).subtype (Source.starImage H K).subtype_injective
  have hP : (componentStarSylow H K hKH S : Subgroup (Source.starImage H K)) ≤ A := by
    change _ ≤ (Source.starImage H T).comap (Source.starImage H K).subtype
    rw [← map_le_iff_le_comap, he]
    exact map_mono (subgroupOf_mono H hST)
  have hAP := (componentStarSylow H K hKH S).is_maximal' hA hP
  rw [← hAP]
  change ((Source.starImage H T).comap (Source.starImage H K).subtype).map _ = _
  rw [map_comap_eq, range_subtype, inf_comm]

/-- In actual even PSL₂ coordinates, the normalizer image is the genuine
upper triangular Borel. Its lift may have an additional two-group kernel. -/
noncomputable def componentBorelImageEquiv {F : Type*} [Field F] [Finite F] [CharP F 2]
    (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (e : Source.starImage H K ≃* PSL(2,F)) :
    componentBorelImage H K hKH S ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := componentStarSylow H K hKH S
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let N := normalizer (P : Set (Source.starImage H K))
  have he : N.map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) := by
    change (normalizer (P : Set (Source.starImage H K))).map e.toMonoidHom = _
    exact map_normalizer_eq_of_bijective (P : Subgroup (Source.starImage H K))
      (f := e.toMonoidHom) e.bijective
  exact ((equivMapOfInjective N (Source.starImage H K).subtype
      (Source.starImage H K).subtype_injective).symm.trans
    ((e.subgroupMap N).trans (MulEquiv.subgroupCongr he))).trans
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Q)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
