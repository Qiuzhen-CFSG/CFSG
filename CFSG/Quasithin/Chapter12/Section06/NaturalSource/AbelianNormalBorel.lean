module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalLinearTwo
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
/-!
# The original normal PSL₂ Borel in both quotient models

Choose the Sylow subgroup of K equal to the original T ∩ K. Its
normalizer B is solvable, including the full O₂(K) kernel. T normalizes
B, so source 12.6.29 puts BT in M. Conversely K ∩ M is a proper
Sylow overgroup in the rank-one cover and lies in B. This proves
B=K ∩ M and identifies O₂(B)=T ∩ K before taking any quotient.

The literal component-star equivalence transports both the Sylow and
its Borel from K/O₂(K) to K-star. Normality is always relative to H.
The actual reduced actor has H ∩ M=(K ∩ M)L₁T; the centralizing
part of L₁ is retained. Field parity and field-size restrictions, the
other normal Lie rows and the universal natural reduction remain for
source assembly. All earlier geometric inputs remain explicit.

Source: Aschbacher--Smith 12.6.31, printed pp.835--836, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
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
/-- The normal PSL₂ component's actual overlap with M is the Borel over T ∩ K. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_borel
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (_hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
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
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let q : K →* SL(2,F) := (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    change ((eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm).toMonoidHom.comp _).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _
      (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm).injective,
      QuotientGroup.ker_mk']
  have hkP : q.ker ≤ (P : Subgroup K) := hk.symm ▸ pCore_isPGroup.le_sylow_of_normal P
  let R := P.mapSurjective hq
  have hBN : (normalizer (P : Set K)).map q = normalizer (R : Set SL(2,F)) := by
    exact P.normalizer_map_surjective q hq
  let : Group.IsSolvable (normalizer (R : Set SL(2,F))) :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer 2 F (by decide) R
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
    apply Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel q hq P hkP
    · rw [hP]
      exact fun x hx => ⟨x.property,S.chosen.sylow_normalizes_component hx⟩
    · intro he
      apply hout
      intro k hk
      have hx := he.ge (mem_top (⟨k,hk⟩ : K))
      exact hx.2
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
include hz hTV hTz hbound hTI hns hH hKH in
/-- The intrinsic two-core of the original Borel is exactly T ∩ K. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_borel_core
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    (K ⊓ M L : Subgroup G).pCoreIn 2 = (T : Subgroup G) ⊓ K := by
  obtain ⟨P,hP,hB,_,_,_⟩ := S.original_abelian_normal_linearTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
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

include hH hKH in
/-- The overlap retains the whole original L₁ in the normal branch. -/
theorem SourceHypothesis.original_abelian_normal_overlap
    (hn : (K.subgroupOf H).Normal)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H) :
    H ⊓ M L = (K ⊓ M L) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hLM : E.L₁ ≤ M L := (map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)
  have hJM : J ≤ M L := sup_le hLM S.chosen.sylow_normalizes_component
  have hnJ : J ≤ normalizer (K : Set G) := (sup_le hLH hTH).trans
    ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hg : K ⊔ J = H := by
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hgen
    exact (sup_assoc _ _ _).symm.trans hgen
  rw [sup_assoc]
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((K ⊔ J : Subgroup G) : Set G) := hg.symm ▸ hx.1
    rw [coe_mul_of_right_le_normalizer_left K J hnJ] at hx'
    obtain ⟨k,hk,j,hj,rfl⟩ := hx'
    have hkM : k ∈ M L := by
      have hh := (M L).mul_mem hx.2 ((M L).inv_mem (hJM hj))
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem_sup ⟨hk,hkM⟩ hj
  · exact sup_le (le_inf (inf_le_left.trans hKH) inf_le_right)
      (le_inf (sup_le hLH hTH) hJM)

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- Both original quotient models carry this same Borel and Sylow marking. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_borel_star
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ∃ P : Sylow 2 (K ⧸ pCore 2 K),
      let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
      let Pstar := P.mapSurjective (f := e.toMonoidHom) e.surjective
      ((K ⊓ M L : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
        normalizer (P : Set (K ⧸ pCore 2 K)) ∧
      (Pstar : Subgroup (actorImage H K)).map (actorImage H K).subtype =
        actorImage H ((T : Subgroup G) ⊓ K) ∧
      (normalizer (Pstar : Set (actorImage H K))).map (actorImage H K).subtype =
        actorImage H (K ⊓ M L) := by
  obtain ⟨P,hP,hB,_,_,hquot⟩ := S.original_abelian_normal_linearTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
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

end CFSG.Quasithin.Chapter12.Section06
