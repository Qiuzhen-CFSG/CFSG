module
public import Theory.SpecificGroups.Alternating.FiveSquareCoreImage
public import Theory.Alternating.FivePairSylowGeneration

/-!
# Lifting two Sylow generators through the full point core

The literal image of a normal A₅ square is its intrinsic two-core quotient.
Once an order-sixteen actor is placed in that image, two conjugates generate
it. Surjectivity of the original quotient map lifts the conjugator into the
original normal subgroup, retaining the full ambient core as denominator.
Source: Aschbacher--Smith 8.3.12, printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveSquareCoreImage
variable {G : Type*} [Group G] [Finite G]

/-- The two generating conjugates use an element of the original subgroup K. -/
theorem exists_core_image_generating_conjugate
    (H K V : Subgroup G) (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hVK : V ≤ K ⊔ H.pCoreIn 2)
    (hcard : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 16) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := (V.subgroupOf H).map π
    let N := (K.subgroupOf H).map π
    ∃ k : K, A ⊔ A.map (MulAut.conj (π (inclusion hKH k))).toMonoidHom = N := by
  dsimp only
  let π := QuotientGroup.mk' (pCore 2 H)
  let A := (V.subgroupOf H).map π
  let N := (K.subgroupOf H).map π
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHK
  let c := subgroupOfEquivOfLe hKH
  let d := (coreQuotientEquivImage 2 (K.subgroupOf H)).symm.trans
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e)
  obtain ⟨S,hS⟩ := exists_sylow_core_image H K V hKH hHK e hVK hcard
  obtain ⟨g,hg⟩ := Theory.AlternatingFive.two_conjugates_of_pair_equiv d S
  have hm := congrArg (Subgroup.map N.subtype) hg
  rw [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype] at hm
  have he : ((S : Subgroup N).map (MulAut.conj g).toMonoidHom).map N.subtype =
      A.map (MulAut.conj (g : H ⧸ pCore 2 H)).toMonoidHom := by
    change ((S : Subgroup N).map (MulAut.conj g).toMonoidHom).map N.subtype =
      ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map _
    rw [←hS,map_map,map_map]
    rfl
  rw [he] at hm
  obtain ⟨k,hk,hkg⟩ := g.property
  refine ⟨⟨k,hk⟩,?_⟩
  change A ⊔ A.map (MulAut.conj (π k)).toMonoidHom = N
  rw [hkg]
  exact hm
end Theory.SpecificGroups.Alternating.FiveSquareCoreImage
