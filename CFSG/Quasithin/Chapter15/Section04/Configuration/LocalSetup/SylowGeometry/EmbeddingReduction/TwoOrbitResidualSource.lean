module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SwappedResidual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualSource
/-!
# The original exchanged residual in Chapter 15

The actual simple two-core quotient is marked by one of the two retained
rank-one models. The source pair theorem applies inside H, where the
component normalizer has index two. Mapping its residual equality along
the actual subtype inclusion identifies the original X-normal closure.
No universal residual theorem or residual equality is assumed.
Source: Aschbacher--Smith 1.2.2(a), p.504; 15.4.20, p.1164.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Source 1.2.2(a) on the exact exchanged rank-one component retained by
1.3.4. Both model families and the original quotient maps are preserved. -/
theorem swapped_normalClosure_eq_residual_source {κ : GroupClass.{u}}
    {U X P H L : Subgroup G} (hsq : IsSQTK κ H)
    (h : Chapter1.XiEmbedding.LocalInput 3 U X P H)
    (hL : L ∈ Chapter1.cComponentsIn H)
    (hq : IsQuasisimple (Chapter1.XiQuotient L))
    (hqs : IsSimpleGroup (Chapter1.XiQuotient L))
    (hX : X ≤ componentOrbit L U)
    (hs : Chapter1.XiEmbedding.SwappedFactors U P L)
    (hm : Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient L))
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2) :
    normalClosureIn X H = (primeToResidual 3 H).map H.subtype := by
  have hUH : U ≤ H := le_sup_right.trans h.overgroup
  obtain ⟨t,ht,htn,_⟩ := hs.2
  let tH : H := ⟨t,hUH ht.1⟩
  let B := L.subgroupOf H
  let eL := subgroupOfEquivOfLe hL.1
  let eQ : (B ⧸ pCore 2 B) ≃* Chapter1.XiQuotient L :=
    QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  let := hq
  let := hqs
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eQ.isSimpleGroup
  have htB : tH ∉ normalizer (B : Set H) := by
    rw [←subgroupOf_normalizer_eq hL.1]
    exact htn
  have hd : 3 ∣ Nat.card (B ⧸ pCore 2 B) := by
    rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hL.2).toEquiv]
    exact swapped_three_dvd_quotient_image h hs
  have hmB : (∃ n, ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 p := by
    rcases hm with ⟨n,_,_,hn⟩ | ⟨p,hp,ho,hpmodel⟩
    · exact Or.inl ⟨n,hn.of_mulEquiv eQ⟩
    · exact Or.inr ⟨p,hp,ho,hpmodel.of_mulEquiv eQ⟩
  have hres := Chapter1.Section02.rankOne_pair_eq_primeToResidual_three hL.2 hi tH htB hd
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) hmB
  have hp : (B ⊔ B.conjBy tH).map H.subtype = L ⊔ L.conjBy t := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hL.1]
    congr 1
    change (B.map (MulAut.conj tH).toMonoidHom).map H.subtype = _
    rw [map_map]
    have he : H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hL.1]
    rfl
  have he := congrArg (Subgroup.map H.subtype) hres
  rw [hp] at he
  exact (swapped_normalClosure_eq_orbit h hL hqs hX hs hi).1.trans
    ((componentOrbit_eq_pair_of_index_two le_rfl hL.1 hi (hUH ht.1) htn).trans he)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
