module

public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The core and Sylow conclusions from the alpha decomposition

The first conclusion of B.2.18 follows because O₂(L) lies in R, centralizes
V, and lies in L. For the Sylow-centralizer conclusion, LS is normal in LR
since R normalizes its Baumann subgroup S. Restrict the given Sylow subgroup
of C_{LR}(V) to C_{LS}(V). The alpha decomposition puts this intersection
inside S. Finally, maximality in the image and in the kernel lifts a Sylow
subgroup through the action quotient.

The decomposition is an explicit premise of these helpers. Proving it from
(a)–(e) remains the responsibility of B.2.18's assembly; these theorems do
not assert that the full Baumann argument has been completed.

Source: Aschbacher–Smith, B.2.18(1),(3), printed p.81. The final assertion
uses both Sylow hypotheses, as required in B.6.10 and C.1.37.
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument
open Stellmacher Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylowIn_maximal {H S T : Subgroup G}
    (hS : IsSylowSubgroupIn S H) (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hST : S ≤ T) : T = S := by
  obtain ⟨P, hP⟩ := hS
  have hPT : (P : Subgroup H) ≤ T.subgroupOf H := by
    intro x hx
    exact hST (hP ▸ mem_map_of_mem H.subtype hx)
  have he := P.is_maximal' (hT.comap_subtype (K := H)) hPT
  have hm := congrArg (map H.subtype) he
  change (T.subgroupOf H).map H.subtype = (P : Subgroup H).map H.subtype at hm
  rwa [map_subgroupOf_eq_of_le hTH, hP] at hm

private theorem sylowIn_normal_inf {H S N : Subgroup G}
    (hS : IsSylowSubgroupIn S H) (hNH : N ≤ H) [(N.subgroupOf H).Normal] :
    IsSylowSubgroupIn (S ⊓ N) N := by
  obtain ⟨P, hP⟩ := hS
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal (N.subgroupOf H)
  let e := subgroupOfEquivOfLe hNH
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((T : Subgroup (N.subgroupOf H)).map e.toMonoidHom).map N.subtype = _
  rw [map_map]
  change (T : Subgroup (N.subgroupOf H)).map
    (H.subtype.comp (N.subgroupOf H).subtype) = _
  rw [← map_map, hT, subgroupOf_map_subtype, map_inf _ _ _ H.subtype_injective,
    hP, map_subgroupOf_eq_of_le hNH]

omit [Finite G] in
private theorem sylowIn_of_image_and_kernel {K : Type*} [Group K]
    (f : G →* K) (S H : Subgroup G) (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hk : IsSylowSubgroupIn (S ⊓ f.ker) (H ⊓ f.ker))
    (hi : IsSylowSubgroupIn (S.map f) (H.map f)) : IsSylowSubgroupIn S H := by
  obtain ⟨P, hP⟩ := (hS.comap_subtype (K := H)).exists_le_sylow
  let T := (P : Subgroup H).map H.subtype
  have hTH : T ≤ H := map_subtype_le _
  have hT : IsPGroup 2 T := P.isPGroup'.map H.subtype
  have hST : S ≤ T := by
    intro s hs
    exact ⟨⟨s, hSH hs⟩, hP hs, rfl⟩
  have hi_eq : T.map f = S.map f := sylowIn_maximal hi (map_mono hTH)
    (hT.map f) (map_mono hST)
  have hk_eq : T ⊓ f.ker = S ⊓ f.ker := sylowIn_maximal hk
    (inf_le_inf_right _ hTH) (hT.to_le inf_le_left) (inf_le_inf_right _ hST)
  refine ⟨P, le_antisymm ?_ hST⟩
  intro t ht
  obtain ⟨s, hs, hst⟩ := hi_eq ▸ mem_map_of_mem f ht
  have hmem : s⁻¹ * t ∈ T ⊓ f.ker := by
    refine ⟨T.mul_mem (T.inv_mem (hST hs)) ht, ?_⟩
    change f (s⁻¹ * t) = 1
    rw [map_mul, map_inv, hst, inv_mul_cancel]
  have hz : s⁻¹ * t ∈ S := (hk_eq ▸ hmem).1
  simpa using S.mul_mem hs hz

omit [Finite G] in
/-- The alpha decomposition puts O₂(L) in the Baumann subgroup. -/
public theorem core_le_baumann_of_decomposition (V R L : Subgroup G)
    (hcore : (pCore 2 L).map L.subtype ≤ R ⊓ centralizer (V : Set G))
    (hd : thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G))) :
    (pCore 2 L).map L.subtype ≤ baumann R := by
  apply le_inf (hcore.trans inf_le_left)
  apply le_centralizer_iff.mpr
  rw [hd]
  apply sup_le
  · exact inf_le_right.trans (centralizer_le (map_subtype_le _))
  · exact inf_le_left.trans (le_centralizer_iff.mp (hcore.trans inf_le_right))

/-- Transfer the Sylow centralizer condition from R to its Baumann subgroup. -/
public theorem sylow_centralizer_of_decomposition (V R L : Subgroup G) [L.Normal]
    (hd : thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)))
    (hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((L ⊔ R) ⊓ centralizer (V : Set G))) :
    IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
      ((L ⊔ baumann R) ⊓ centralizer (V : Set G)) := by
  let S := baumann R
  have hSR : S ≤ R := inf_le_left
  have hnorm : ((L ⊔ S).subgroupOf (L ⊔ R)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (sup_le_sup_left hSR L)).mpr
    apply sup_le
    · exact (show L ≤ L ⊔ S from le_sup_left).trans (L ⊔ S).le_normalizer
    · exact (le_inf le_normalizer_of_normal
        (R.le_normalizer.trans (normalizer_le_normalizer_baumann R))).trans
        (normalizer_inf_normalizer_le_normalizer_sup L S)
  let _ := hnorm
  let _ := inf_subgroupOf_inf_normal_of_left (A' := L ⊔ S) (A := L ⊔ R)
    (centralizer (V : Set G))
  have hp := sylowIn_normal_inf hQ
    (inf_le_inf_right (centralizer (V : Set G)) (sup_le_sup_left hSR L))
  have hfix : L ⊔ S ≤ centralizer
      (thompsonAlpha R ⊓ centralizer (L : Set G) : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact (show S ≤ centralizer (thompsonAlpha R : Set G) from inf_le_right).trans
        (centralizer_le inf_le_left)
  have heq : (R ⊓ centralizer (V : Set G)) ⊓
      ((L ⊔ S) ⊓ centralizer (V : Set G)) = S ⊓ centralizer (V : Set G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨hx.1.1, ?_⟩, hx.1.2⟩
      have hx1 := hfix hx.2.1
      have hx2 : x ∈ centralizer (V ⊓ centralizer
          (elementaryAbelianMaxJ R : Set G) : Set G) := centralizer_le inf_le_left hx.1.2
      change x ∈ centralizer (thompsonAlpha R : Set G)
      rw [hd]
      exact le_centralizer_iff.mp (sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hx1))
        (le_centralizer_iff.mp (zpowers_le.mpr hx2))) (mem_zpowers x)
    · exact le_inf (inf_le_inf_right _ hSR)
        (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  rw [heq] at hp
  exact hp

/-- Lift the Sylow image when the original centralizer is also Sylow. -/
public theorem sylow_lift_of_decomposition (V R L : Subgroup G) [V.Normal] [L.Normal]
    (hR : IsPGroup 2 R)
    (hd : thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)))
    (hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((L ⊔ R) ⊓ centralizer (V : Set G)))
    (hi : IsSylowSubgroupIn ((baumann R).map (actionMap V))
      (L.map (actionMap V) ⊔ (baumann R).map (actionMap V))) :
    IsSylowSubgroupIn (baumann R) (L ⊔ baumann R) := by
  apply sylowIn_of_image_and_kernel (actionMap V) (baumann R) (L ⊔ baumann R)
    le_sup_right (hR.to_le inf_le_left)
  · simpa only [actionMap_ker] using sylow_centralizer_of_decomposition V R L hd hQ
  · simpa only [Subgroup.map_sup] using hi

end CFSG.Quasithin.ChapterB.BaumannArgument
