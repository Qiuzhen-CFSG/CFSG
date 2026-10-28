module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration
/-!
# A concrete PSL₃ cover by overgroups of T

An actual equivalence L ≃ PSL₃(F) embeds the two standard parabolics in G.
Adjoining T produces a two-member family containing T. Matrix generation
shows that its join is G whenever L ⊔ T = G. No normality of these parabolics
in G is assumed.

If an element of T interchanges the embedded parabolics, the first of these
overgroups is already G. This explains why this cover does not by itself
reduce E-generation in the graph-automorphism case.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.12
and the PSL₃ case of E.1.14(1), printed p.214. E-generation of the cover
members, and the Sp₄(2^f)' calculation, are still separate obligations.
-/

@[expose] public section

open Subgroup Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper
variable {G F : Type*} [Group G] [Field F] [Finite F]

/-- The inverse of the model equivalence followed by inclusion in G. -/
noncomputable def linearThreeEmbedding (L : Subgroup G) (e : L ≃* PSL(3, F)) :
    PSL(3, F) →* G := L.subtype.comp e.symm.toMonoidHom

omit [Finite F] in
theorem linearThreeEmbedding_range (L : Subgroup G) (e : L ≃* PSL(3, F)) :
    (linearThreeEmbedding L e).range = L := by
  rw [linearThreeEmbedding, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective]
  rw [← MonoidHom.range_eq_map, L.range_subtype]

/-- The two transported parabolics, each enlarged to contain T. -/
def linearThreeOvergroups (L T : Subgroup G) (e : L ≃* PSL(3, F)) :
    Set (Subgroup G) :=
  {(pointParabolic F).map (linearThreeEmbedding L e) ⊔ T,
   (lineParabolic F).map (linearThreeEmbedding L e) ⊔ T}

/-- Concrete matrix generation supplies the covering clause of E.1.12. -/
theorem linearThreeOvergroups_generate (L T : Subgroup G) (e : L ≃* PSL(3, F))
    (hLT : L ⊔ T = ⊤) : sSup (linearThreeOvergroups L T e) = ⊤ := by
  simp only [linearThreeOvergroups, sSup_insert, sSup_singleton]
  calc
    _ = ((pointParabolic F).map (linearThreeEmbedding L e) ⊔
        (lineParabolic F).map (linearThreeEmbedding L e)) ⊔ T := by ac_rfl
    _ = (⊤ : Subgroup PSL(3, F)).map (linearThreeEmbedding L e) ⊔ T := by
      rw [← Subgroup.map_sup, parabolics_sup_eq_top]
    _ = ⊤ := by rw [← MonoidHom.range_eq_map, linearThreeEmbedding_range, hLT]

omit [Finite F] in
theorem le_linearThreeOvergroups (L T : Subgroup G) (e : L ≃* PSL(3, F))
    (H : Subgroup G) (hH : H ∈ linearThreeOvergroups L T e) : T ≤ H := by
  rcases hH with rfl | hH
  · exact le_sup_right
  · rw [Set.mem_singleton_iff] at hH
    subst H
    exact le_sup_right
/-- When an element of T interchanges the parabolics, adjoining T to the
point parabolic already gives G. A proper-parabolic reduction cannot handle
this branch without an additional E-generation argument. -/
theorem linearThree_point_sup_eq_top_of_swap
    (L T : Subgroup G) (e : L ≃* PSL(3, F)) (hLT : L ⊔ T = ⊤)
    (t : G) (ht : t ∈ T)
    (hswap : ((pointParabolic F).map (linearThreeEmbedding L e)).map
      (MulAut.conj t).toMonoidHom = (lineParabolic F).map (linearThreeEmbedding L e)) :
    (pointParabolic F).map (linearThreeEmbedding L e) ⊔ T = ⊤ := by
  let H := (pointParabolic F).map (linearThreeEmbedding L e) ⊔ T
  have hQ : (lineParabolic F).map (linearThreeEmbedding L e) ≤ H := by
    rw [← hswap]
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hx))
      (H.inv_mem (Subgroup.mem_sup_right ht))
  have hcover := linearThreeOvergroups_generate L T e hLT
  apply top_unique
  rw [← hcover]
  apply sSup_le
  intro J hJ
  rcases hJ with rfl | hJ
  · exact le_rfl
  · rw [Set.mem_singleton_iff] at hJ
    subst J
    exact sup_le hQ le_sup_right
end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper
