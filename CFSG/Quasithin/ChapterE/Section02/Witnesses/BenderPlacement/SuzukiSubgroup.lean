module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels

/-!
# Suzuki witnesses in a marked subgroup

The Suzuki subgroup need not be normal in the original group. Its prescribed
Sylow and Borel intersections transport the concrete two-conjugate witness
through the same inclusion, retaining the original elementary subgroup and
normal-core quotient. The symplectic source consumer supplies these two
intersection identities from the actual matrix geometry.
Source: Aschbacher--Smith E.2.7, printed p.221.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {G : Type*} [Group G] [Finite G]
theorem suzuki_subgroup_witness (T : Sylow 2 G) (M K V : Subgroup G)
    {m : ℕ} (hm : 0<m) (e : K ≃* SuzukiMatrixGroup m)
    (S : Sylow 2 K) (hS : (S : Subgroup K)=(T : Subgroup G).subgroupOf K)
    (hM : M.subgroupOf K=normalizer (S : Set K))
    [IsElementaryAbelian 2 V] (hVK : V≤K) (hVT : V≤T)
    (hrank : 1<primeRank 2 V) :
    Nonempty (OriginalWitness T M V (2*m+1)) := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let W := (V.subgroupOf K).map e.toMonoidHom
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hWQ : W ≤ (Q : Subgroup (SuzukiMatrixGroup m)) := by
    apply map_mono
    rw [hS]
    exact comap_mono hVT
  have hWr : 1 < primeRank 2 W := by
    rw [← primeRank_congr 2 ((V.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective),
      primeRank_congr 2 (subgroupOfEquivOfLe hVK)]
    exact hrank
  obtain ⟨w⟩ := Suzuki.source_witness_of_le_sylow hm Q W hWQ hWr
  let f : SuzukiMatrixGroup m →* G := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hTf : (T : Subgroup G).comap f = Q := by
    change ((T : Subgroup G).subgroupOf K).comap e.symm.toMonoidHom = _
    rw [← hS]
    exact comap_equiv_eq_map_symm e.symm (S : Subgroup K)
  have hMf : M.comap f = normalizer (Q : Set (SuzukiMatrixGroup m)) := by
    change (M.subgroupOf K).comap e.symm.toMonoidHom = _
    rw [hM]
    change (normalizer ((S : Subgroup K) : Set K)).comap e.symm.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (f := e.symm.toMonoidHom)
      (S : Subgroup K) e.symm.surjective]
    have heS : (S : Subgroup K).comap e.symm.toMonoidHom = (Q : Subgroup _) :=
      comap_equiv_eq_map_symm e.symm (S : Subgroup K)
    rw [heS]
    rfl
  have hWV : W.map f = V := by
    change ((V.subgroupOf K).map e.toMonoidHom).map f = _
    rw [map_map]
    have he : f.comp e.toMonoidHom = K.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [he,map_subgroupOf_eq_of_le hVK]
  have result := SuzukiWitness.map_model w f hf T M hTf hMf
  rw [hWV] at result
  exact ⟨OriginalWitness.of_suzuki result⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
