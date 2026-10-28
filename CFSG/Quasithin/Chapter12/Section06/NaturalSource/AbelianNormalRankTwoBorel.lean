module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalRankTwo
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.SpecificGroups.SymplecticFour.Sylow.FlagCounts
/-!
# The original Borel and field parity in the normal rank-two rows

The normal symplectic and G₂ models have solvable Sylow normalizers.
Lifting their full normalizers through O₂(K), the original solvable
overgroup theorem puts them in M. Conversely an element of K intersect M
normalizes the original L₁, hence its proved star core (T intersect K)-star.
The entire O₂(H) kernel lies in T, so this lifts to normalization of the
original Sylow intersection. Thus K intersect M is exactly its Borel,
with intrinsic two-core T intersect K.

The component-star equivalence preserves the same Sylow and Borel in
both K/O₂(K) and K-star. The original surviving E₉ lies in this Borel.
The native orders q⁴(q-1)² and q⁶(q-1)² then force three to divide q-1,
so the defining-field exponent is even.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
Earlier point, invariance, intersection, TI and nonsingular-centralizer
inputs remain explicit. The cyclic outer-action contradiction, signed
degree-three restrictions and later module exclusions remain obligations
of the universal natural-reduction assembly. SourceInputs is unchanged.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)

include hz hTV hTz hbound hTI hns hH hKH in
private theorem source_normal_rankTwo_borel
    (hn : (K.subgroupOf H).Normal)
    {X : Type*} [Group X] [Finite X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hsol : ∀ P : Sylow 2 X, Group.IsSolvable (normalizer (P : Set X)))
    (hc : (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K)) :
    ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K ∧
      (normalizer (P : Set K)).map K.subtype = K ⊓ M L ∧
      Group.IsSolvable (K ⊓ M L : Subgroup G) ∧
      (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
        normalizer ((K ⊓ M L : Subgroup G) : Set G) ∧
      ((K ⊓ M L : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
        normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K)) :
          Set (K ⧸ pCore 2 K)) := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hnK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp hn
  let : (K.subgroupOf H).Normal := hn
  obtain ⟨P₀,hP₀⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e₀ := subgroupOfEquivOfLe hKH
  let P := P₀.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    change (P₀ : Subgroup (K.subgroupOf H)).map e₀.toMonoidHom = _
    rw [hP₀]
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro ht
      exact ⟨⟨⟨c,hKH c.property⟩,c.property⟩,ht,rfl⟩
  have hPmap : (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hP,subgroupOf_map_subtype]
  let B := (normalizer (P : Set K)).map K.subtype
  have hBeq : B = K ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    have he : ((P : Subgroup K).map K.subtype).subgroupOf K = (P : Subgroup K) :=
      comap_map_eq_self_of_injective K.subtype_injective _
    have hh := subgroupOf_normalizer_eq (map_subtype_le (P : Subgroup K))
    rw [he] at hh
    change (normalizer (((P : Subgroup K).map K.subtype) : Set G)).subgroupOf K =
      normalizer (P : Set K) at hh
    change (normalizer (P : Set K)).map K.subtype = _
    rw [←hh,subgroupOf_map_subtype,hPmap,inf_comm]
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [hBeq]
    apply (le_inf (hTH.trans hnK) ?_).trans inf_normalizer_le_normalizer_inf
    apply le_trans (c := normalizer (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) : Set G)) ?_
      (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).le_normalizer
    exact (le_inf (T : Subgroup G).le_normalizer (hTH.trans hnK)).trans
      inf_normalizer_le_normalizer_inf
  let q : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let R := P.mapSurjective hq
  have hBN : (normalizer (P : Set K)).map q = normalizer (R : Set X) := by
    exact P.normalizer_map_surjective q hq
  let : Group.IsSolvable (normalizer (R : Set X)) := hsol R
  let : Group.IsNilpotent q.ker := (hk ▸ pCore_isPGroup).isNilpotent
  let : Group.IsSolvable (normalizer (P : Set K)) := by
    let : Group.IsSolvable ((normalizer (P : Set K)).map q) := hBN.symm ▸ inferInstance
    let : Group.IsSolvable (((normalizer (P : Set K)).map q).comap q) :=
      isSolvable_comap_of_solvable_ker q _
    exact Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (le_comap_map q (normalizer (P : Set K))))
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective _)
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes B T hTB
  have hBM : B ≤ M L := le_sup_left.trans
    (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns le_sup_right)
  have hMB : (K ⊓ M L : Subgroup G).subgroupOf K ≤ normalizer (P : Set K) := by
    apply le_normalizer_iff.mpr
    intro k hk p hp
    have hkNV : (k : G) ∈ normalizer (V : Set G) :=
      Mv_le_module_normalizer_of_TI hTI z hz ⟨hk.2,by
        have hh := hH.2.1 (hKH k.property)
        rwa [E.Gz_eq] at hh⟩
    have hkL : (k : G) ∈ normalizer (E.L₁ : Set G) :=
      S.original_module_normalizer_normalizes_residual D hZ z hTV hH ⟨hKH k.property,hkNV⟩
    let π := QuotientGroup.mk' (pCore 2 H)
    let kH : H := ⟨k,hKH k.property⟩
    let pH : H := ⟨p,hKH p.property⟩
    have hkA : π kH ∈ normalizer (actorImage H E.L₁ : Set (H ⧸ pCore 2 H)) := by
      apply (E.L₁.subgroupOf H).le_normalizer_map π
      apply mem_map_of_mem
      rw [←subgroupOf_normalizer_eq (show E.L₁ ≤ H from fun x hx => hH.1.2 (Or.inl hx))]
      exact hkL
    have hkC := normalizer_le_normalizer_characteristic_image
      (actorImage H E.L₁) (pCore 2 (actorImage H E.L₁)) hkA
    change π kH ∈ normalizer ((actorImage H E.L₁).pCoreIn 2 : Set (H ⧸ pCore 2 H)) at hkC
    rw [hc] at hkC
    have hpT : (p : G) ∈ (T : Subgroup G) := by rw [hP] at hp; exact hp
    have hpC : π pH ∈ actorImage H ((T : Subgroup G) ⊓ K) :=
      mem_map_of_mem π ⟨hpT,p.property⟩
    have hc' := (mem_normalizer_iff.mp hkC (π pH)).mp hpC
    obtain ⟨y,hy,he⟩ := hc'
    have hker : kH*pH*kH⁻¹*y⁻¹ ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (kH*pH*kH⁻¹*y⁻¹) = 1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,he,mul_inv_cancel]
    have hTker : (kH*pH*kH⁻¹*y⁻¹ : H).val ∈ (T : Subgroup G) :=
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)) hker
    rw [hP]
    have hh := (T : Subgroup G).mul_mem hTker hy.1
    change ((k:G)*(p:G)*(k:G)⁻¹*y.val⁻¹)*y.val ∈ (T : Subgroup G) at hh
    change (k:G)*(p:G)*(k:G)⁻¹ ∈ (T : Subgroup G)
    simpa only [inv_mul_cancel_right] using hh
  have hBM_eq : B = K ⊓ M L := by
    apply le_antisymm (le_inf (map_subtype_le _) hBM)
    intro x hx
    exact ⟨⟨x,hx.1⟩,hMB hx,rfl⟩
  have hLM : E.L₁ ≤ M L := (map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)
  have hJH : E.L₁ ⊔ (T : Subgroup G) ≤ H := sup_le
    (fun x hx => hH.1.2 (Or.inl hx)) hTH
  refine ⟨P,hPmap,hBM_eq,hBM_eq ▸ inferInstance,?_,?_⟩
  · exact (le_inf (hJH.trans hnK)
      ((sup_le hLM S.chosen.sylow_normalizes_component).trans (M L).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  · rw [←hBM_eq]
    change ((normalizer (P : Set K)).map K.subtype |>.comap K.subtype).map _ = _
    rw [comap_map_eq_self_of_injective K.subtype_injective]
    exact P.normalizer_map_surjective (QuotientGroup.mk' (pCore 2 K))
      (QuotientGroup.mk'_surjective _)

variable (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The literal original Borel in the normal symplectic and G₂ branches. -/
theorem SourceHypothesis.original_abelian_normal_rankTwo_borel
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n) ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K ∧
      (normalizer (P : Set K)).map K.subtype = K ⊓ M L ∧
      Group.IsSolvable (K ⊓ M L : Subgroup G) ∧
      (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
        normalizer ((K ⊓ M L : Subgroup G) : Set G) ∧
      ((K ⊓ M L : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
        normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K)) :
          Set (K ⧸ pCore 2 K)) := by
  rcases hm with hm | hm
  · have hc := S.original_abelian_normal_symplectic_star_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
    obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
    let := hF
    let := hfin
    exact source_normal_rankTwo_borel S D hZ z hz hTV hTz hbound hTI hns hH hKH hn eK
      (Theory.SpecificGroups.SymplecticFour.isSolvable_derived_sylow_normalizer hcard (by omega)) hc
  · have hc := S.original_abelian_normal_g2_star_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
    obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
    let := hF
    let := hfin
    exact source_normal_rankTwo_borel S D hZ z hz hTV hTz hbound hTI hns hH hKH hn eK
      (Atlas.G2.DerivedNormalizerSolvable.isSolvable_normalizer_of_card (by omega) hcard) hc

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The intrinsic two-core of the original Borel is exactly T ∩ K. -/
theorem SourceHypothesis.original_abelian_normal_rankTwo_borel_core
    (hn : (K.subgroupOf H).Normal)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n) ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    (K ⊓ M L : Subgroup G).pCoreIn 2 = (T : Subgroup G) ⊓ K := by
  obtain ⟨P,hP,hB,_,_,_⟩ := S.original_abelian_normal_rankTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hn2 hm
  let B := normalizer (P : Set K)
  have hPB : (P : Subgroup K) ≤ B := P.le_normalizer
  have hc : B.pCoreIn 2 = (P : Subgroup K) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow B (P.subtype hPB)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB] using hh
    · exact le_pCoreIn_of_normalizes P.isPGroup' hPB le_rfl
  have h := congrArg (map K.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ K.subtype K.subtype_injective,hB,hP] at h
  exact h


include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Both original quotient models carry this same Borel and Sylow marking. -/
theorem SourceHypothesis.original_abelian_normal_rankTwo_borel_star
    (hn : (K.subgroupOf H).Normal)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n) ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    ∃ P : Sylow 2 (K ⧸ pCore 2 K),
      let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
      let Pstar := P.mapSurjective (f := e.toMonoidHom) e.surjective
      ((K ⊓ M L : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
        normalizer (P : Set (K ⧸ pCore 2 K)) ∧
      (Pstar : Subgroup (actorImage H K)).map (actorImage H K).subtype =
        actorImage H ((T : Subgroup G) ⊓ K) ∧
      (normalizer (Pstar : Set (actorImage H K))).map (actorImage H K).subtype =
        actorImage H (K ⊓ M L) := by
  obtain ⟨P,hP,hB,_,_,hquot⟩ := S.original_abelian_normal_rankTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hn2 hm
  let q := QuotientGroup.mk' (pCore 2 K)
  let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
  have him (Y : Subgroup G) (hYK : Y ≤ K) :
      ((Y.subgroupOf K).map q).map ((actorImage H K).subtype.comp e.toMonoidHom) =
        actorImage H Y := by
    have hf : ((actorImage H K).subtype.comp e.toMonoidHom).comp q =
        (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH) := by
      ext k
      exact componentStarEquiv_mk H K hKH hK k
    rw [map_map,hf,←map_map]
    have hi : (Y.subgroupOf K).map (inclusion hKH) = Y.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hYK hx⟩,hx,rfl⟩
    rw [hi]
    rfl
  refine ⟨P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),hquot,?_,?_⟩
  · change (((P : Subgroup K).map q).map e.toMonoidHom).map (actorImage H K).subtype = _
    rw [map_map]
    have hi : ((T : Subgroup G) ⊓ K : Subgroup G).subgroupOf K = (P : Subgroup K) := by
      rw [←hP]
      exact comap_map_eq_self_of_injective K.subtype_injective _
    rw [←hi]
    exact him _ inf_le_right
  · change (normalizer (((P : Subgroup K).map q).map e.toMonoidHom : Set (actorImage H K))).map
      (actorImage H K).subtype = _
    change ((K ⊓ M L : Subgroup G).subgroupOf K).map q =
      normalizer ((P : Subgroup K).map q : Set (K ⧸ pCore 2 K)) at hquot
    rw [←map_normalizer_eq_of_bijective _ (f := e.toMonoidHom) e.bijective,map_map,←hquot]
    exact him _ inf_le_left


private theorem card_normalizer_transport {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (P : Sylow 2 X) :
    Nat.card (normalizer (P : Set X)) =
      Nat.card (normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set Y)) := by
  change _ = Nat.card (normalizer ((P : Subgroup X).map e.toMonoidHom : Set Y))
  rw [←map_normalizer_eq_of_bijective (P : Subgroup X) e.bijective,
    card_map_of_injective e.injective]
  rfl

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original E₉ lies in the same Borel, forcing even defining-field degree. -/
theorem SourceHypothesis.original_abelian_normal_rankTwo_even
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n) ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) : Even n := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  have hAB : A ≤ B := by
    rcases hm with hm | hm
    · exact S.original_abelian_normal_symplectic_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
    · exact S.original_abelian_normal_g2_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  have hAM : A ≤ actorImage H (M L) := map_mono (comap_mono
    ((map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)))
  have hkM : (QuotientGroup.mk' (pCore 2 H)).ker ≤ (M L).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact S.chosen.sylow_normalizes_component
      ((S.original_point_core_eq D hZ z hz hTz).2.2
        (S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hx)))
  have hAMK : A ≤ actorImage H (K ⊓ M L) := by
    change A ≤ ((K ⊓ M L).comap H.subtype).map (QuotientGroup.mk' (pCore 2 H))
    change (QuotientGroup.mk' (pCore 2 H)).ker ≤ (M L).comap H.subtype at hkM
    rw [comap_inf,map_inf_of_ker_le _ _ _ hkM]
    exact le_inf hAB hAM
  let R : Sylow 3 E.L₁ := Classical.choice inferInstance
  let R₀ := (R : Subgroup E.L₁).map E.L₁.subtype
  have h9 : 9 ∣ Nat.card (actorImage H (K ⊓ M L)) := by
    have hh := card_dvd_of_le ((map_mono (comap_mono (map_subtype_le (R : Subgroup E.L₁)))).trans hAMK)
    change Nat.card (actorImage H R₀) ∣ Nat.card (actorImage H (K ⊓ M L)) at hh
    have hc : Nat.card (actorImage H R₀) = 9 :=
      (S.original_point_sylow_star D hZ z hz hTz hH R).2.1
    rwa [hc] at hh
  obtain ⟨P,_,_,hB⟩ := S.original_abelian_normal_rankTwo_borel_star
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hn2 hm
  let c : (K ⧸ pCore 2 K) ≃* B := componentStarEquiv H K hKH hK
  let Pstar := P.mapSurjective (f := c.toMonoidHom) c.surjective
  have h9N : 9 ∣ Nat.card (normalizer (Pstar : Set B)) := by
    rw [←hB,card_map_of_injective (actorImage H K).subtype_injective] at h9
    exact h9
  have hc : ∃ r : ℕ, Nat.card (normalizer (Pstar : Set B)) =
      (2^n)^r * (2^n-1)^2 := by
    rcases hm with ⟨F,hF,hfin,hcard,⟨eK⟩⟩ | ⟨F,hF,hfin,hcard,⟨eK⟩⟩
    · let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
      have hq : 2 < Nat.card F := by
        rw [hcard]
        exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
      let e := c.symm.trans
        (eK.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq))
      refine ⟨4,?_⟩
      rw [card_normalizer_transport e Pstar,
        Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv
          hcard (by omega) (Pstar.mapSurjective (f := e.toMonoidHom) e.surjective)).toEquiv,
        Theory.SpecificGroups.SymplecticFour.card_borel,hcard]
    · let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
      let e := c.symm.trans
        (eK.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard))
      refine ⟨6,?_⟩
      rw [card_normalizer_transport e Pstar,
        Nat.card_congr (Atlas.G2.EvenBorelTorus.sylowNormalizerEquiv
          (Pstar.mapSurjective (f := e.toMonoidHom) e.surjective)).toEquiv,
        Atlas.G2.card_borel,hcard]
  obtain ⟨r,hr⟩ := hc
  have h3 := (by decide : 3 ∣ 9).trans h9N
  rw [hr] at h3
  have hnot : ¬ 3 ∣ (2^n)^r := fun h =>
    (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
    (Nat.prime_three.dvd_of_dvd_pow ((Nat.prime_three.dvd_mul.mp h3).resolve_left hnot))
end CFSG.Quasithin.Chapter12.Section06
