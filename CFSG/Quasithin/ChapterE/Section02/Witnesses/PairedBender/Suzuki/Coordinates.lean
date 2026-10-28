module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Core
public import Theory.GroupTheory.TwoConjugateProduct.Markings

/-!
# Paired Suzuki source coordinates

The original maximal two-core lies in the paired residual. Multiplication
from the two actual components therefore lifts the original V. The original
Sylow pulls back to the coordinate Sylows, and self-normalizing rank-one
Borels identify the exact preimage of the original unique maximal subgroup.
No placement or coordinate marking is assumed.

Source: Aschbacher–Smith E.2.7, printed p.219.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
variable {G : Type*} [Group G] [Finite G]

structure Coordinates (T : Sylow 2 G) (M V K : Subgroup G) (m : ℕ) where
  second : Subgroup G
  second_model : second ≃* SuzukiMatrixGroup m
  embedding : K × second →* G
  injective : Function.Injective embedding
  first_sylow : Sylow 2 K
  second_sylow : Sylow 2 second
  sylow_preimage : (T : Subgroup G).comap embedding =
    (first_sylow : Subgroup K).prod (second_sylow : Subgroup second)
  borel_preimage : M.comap embedding =
    (normalizer (first_sylow : Set K)).prod (normalizer (second_sylow : Set second))
  original_image : (V.comap embedding).map embedding = V

/-- Construct the actual two factors and the literal Sylow, Borel and V markings. -/
theorem source_coordinates
    {m : ℕ} (hm : 0<m)
    (hH : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable G)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup G} (hK : IsComponent G K)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup G) = ⊤) (hnot : ¬ K.Normal)
    (e : K ≃* SuzukiMatrixGroup m) (V : Subgroup G)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) :
    Nonempty (Coordinates T (ChapterB.minimalParabolicMax T hP) V K m) := by
  have ho := Structure.generating_component_orbit_eq_residual hH T hK hgen
  obtain ⟨t,hne,hDsimple,hD,hR,⟨d,hd⟩,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hK.isCComponent hgen hnot
  let D := K.map (MulAut.conj (t:G)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let eD : D ≃* SuzukiMatrixGroup m := ((MulAut.conj (t:G)).subgroupMap K).symm.trans e
  have hDt : D ⊔ (T : Subgroup G) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:G)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:G)).surjective] at he
    have ht : (T : Subgroup G).map (MulAut.conj (t:G)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property)
    rwa [ht] at he
  let f : K × D →* G := (K ⊔ D : Subgroup G).subtype.comp d.toMonoidHom
  have hf : Function.Injective f := (K ⊔ D : Subgroup G).subtype_injective.comp d.injective
  have hmul : ∀ k a, f (k,a) = (k:G)*(a:G) := hd
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  obtain ⟨R,hR'⟩ := T.exists_subgroupOf_eq_of_subnormal D hD.1
  have hb (L : Subgroup G) (hL : IsComponent G L) [IsSimpleGroup L]
      (eL : L ≃* SuzukiMatrixGroup m) (hLT : L ⊔ (T : Subgroup G) = ⊤)
      (P : Sylow 2 L) (hP' : (P : Subgroup L) = (T : Subgroup G).subgroupOf L) :
      (ChapterB.minimalParabolicMax T hP).subgroupOf L = normalizer (P : Set L) := by
    let := hL.2
    have heven : 2 ∣ Nat.card L := by
      by_contra hh
      exact Group.IsPerfect.not_isSolvable L (odd_order_theorem L
        (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hh)))
    have hmodel : ChapterF.Source.IsRankOneModel L := .suzuki m ⟨eL⟩
    change (ChapterB.minimalParabolicMax T hP).subgroupOf L = normalizer ((P : Subgroup L) : Set L)
    rw [hP']
    exact component_borel_intersection T hP L hL heven
      (Structure.generating_component_orbit_eq_residual hH T hL hLT) hmodel
  have hbK := hb K hK e hgen S hS
  have hbD := hb D hD eD hDt R hR'
  have hself : normalizer ((ChapterB.minimalParabolicMax T hP).subgroupOf K : Set K) =
      (ChapterB.minimalParabolicMax T hP).subgroupOf K := by
    rw [hbK]
    exact Sylow.normalizer_normalizer S
  have hM : (ChapterB.minimalParabolicMax T hP).comap f =
      (normalizer (S : Set K)).prod (normalizer (R : Set D)) := by
    rw [product_borel_comap K D _ f hmul
      (commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hD hne.symm)) hself,
      hbK,hbD]
  have hV : (V.comap f).map f = V := by
    rw [map_comap_eq]
    apply inf_eq_right.mpr
    have hfr : f.range = K ⊔ D := by
      change ((K ⊔ D : Subgroup G).subtype.comp d.toMonoidHom).range = _
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr d.surjective,
        ← MonoidHom.range_eq_map,range_subtype]
    rw [hfr,← hR]
    exact hVcore.trans (source_core_le_residual hH T hP hs hJ hK hgen hnot hm e)
  exact ⟨⟨D,eD,f,hf,S,R,product_sylow_comap K D T f hf hmul S R hS hR',hM,hV⟩⟩
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
