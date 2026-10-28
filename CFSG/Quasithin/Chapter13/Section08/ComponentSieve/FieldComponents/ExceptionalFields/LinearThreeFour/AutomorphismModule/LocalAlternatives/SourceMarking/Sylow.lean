module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.QuotientIntersection

/-!
# The Sylow marking supplied by T∩K

The Sylow of H maps to H/O₂(H) and restricts to the normal component K*.
The actual K* ≃ SL₃(4) equivalence transports that restriction. Since the
quotient kernel lies in T, the resulting subgroup is exactly the model
image of T∩K. Conjugation by the prescribed t in T preserves this marking.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(PDF pp.971–972), combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
variable {G : Type*} [Group G] [Finite G]

/-- The Sylow in the model comes from the actual T* intersection with K*. -/
theorem exists_sourceSylow (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hT : Chapter1.IsSylowIn 2 T H) :
    ∃ S : Sylow 2 SL, (S : Subgroup SL) = modelImage H K T eK := by
  obtain ⟨P, hP⟩ := hT
  have hPH : T.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let q := QuotientGroup.mk' (pCore 2 H)
  let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPS : (P' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    rw [Source.starImage, hPH]
    rfl
  obtain ⟨S, hS⟩ := P'.exists_subgroupOf_eq_of_normal (Source.starImage H K)
  refine ⟨S.mapSurjective (f := eK.toMonoidHom) eK.surjective, ?_⟩
  change (S : Subgroup (Source.starImage H K)).map eK.toMonoidHom = _
  rw [hS, hPS]
  ext x
  rw [mem_map_equiv]
  rfl

def sourceSylow (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hT : Chapter1.IsSylowIn 2 T H) : Sylow 2 SL :=
  (exists_sourceSylow H K T eK hT).choose

theorem sourceSylow_eq (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hT : Chapter1.IsSylowIn 2 T H) :
    (sourceSylow H K T eK hT : Subgroup SL) = modelImage H K T eK :=
  (exists_sourceSylow H K T eK hT).choose_spec

/-- The quotient intersection is the image of T∩K, since O₂(H) lies in T. -/
theorem sourceSylow_intersection (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hT : Chapter1.IsSylowIn 2 T H) :
    (sourceSylow H K T eK hT : Subgroup SL) = modelImage H K (T ⊓ K) eK := by
  rw [sourceSylow_eq]
  obtain ⟨P, hP⟩ := hT
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk', ← hP, ← comap_subtype,
      comap_map_eq_self_of_injective H.subtype_injective]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hi : Source.starImage H (T ⊓ K) = Source.starImage H T ⊓ Source.starImage H K := by
    have he : (T ⊓ K).subgroupOf H = K.subgroupOf H ⊓ T.subgroupOf H := by
      ext x
      exact and_comm
    rw [Source.starImage, he, map_inf_of_ker_le _ _ _ hk]
    exact inf_comm _ _
  ext x
  change sourceActor H K eK x ∈ Source.starImage H T ↔
    sourceActor H K eK x ∈ Source.starImage H (T ⊓ K)
  rw [hi]
  exact ⟨fun hx => ⟨hx, (eK.symm x).property⟩, And.left⟩

/-- Every prescribed element of T stabilizes this same Sylow marking. -/
theorem sourceSylow_stable (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hT : Chapter1.IsSylowIn 2 T H)
    (t : H) (ht : t.val ∈ T) :
    (sourceSylow H K T eK hT : Subgroup SL).map
      (sourceConjugation H K eK (QuotientGroup.mk' (pCore 2 H) t)).toMonoidHom =
        sourceSylow H K T eK hT := by
  rw [sourceSylow_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    change sourceActor H K eK (sourceConjugation H K eK _ x) ∈ Source.starImage H T
    rw [sourceActor_sourceConjugation]
    have ht' : QuotientGroup.mk' (pCore 2 H) t ∈ Source.starImage H T := ⟨t, ht, rfl⟩
    exact (Source.starImage H T).mul_mem
      ((Source.starImage H T).mul_mem ((Source.starImage H T).inv_mem ht') hx) ht'
  · rw [card_map_of_injective (sourceConjugation H K eK _).injective]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
