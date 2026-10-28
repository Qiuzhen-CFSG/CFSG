module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreEscape
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.TorusCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.Alternating.FiveSylowCubicBorel
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# The two literal Borels in original 9.3.3

The actual order-nine Cartan contains a cubic in the original component L.
The opposite coordinate kernel in L₀/O₂(L₀) supplies that cubic: normality
of L in L₀ and the two-group quotient kernel put its entire inverse image
of order three inside L. Thus a cubic completes the actual component
Sylow normalizer. The prescribed cubic in the old residual gives the
same conclusion for K = O²(H).

Both source Borels, and hence their common Borel, lie in AS. The common
subgroup S is kept variable with its literal Sylow-intersection bounds,
so the original S = (T ∩ L₀)O₂(L₀T) can be supplied by 9.3.2. This proves
the Borel enclosure used to construct the genuine F.1.1 pair; rank-two
recognition is a separate source argument.

Source: Aschbacher–Smith 9.3.2–3, combined manuscript of 1 March 2004,
printed p.733, with the original quotient markings from D.3.5–7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_twoPerfect {C : Type*} [Group C] [Finite C]
    (hc : Nat.card C = 3) : IsPPerfect 2 C := by
  intro N hn hp
  let := hn
  apply index_eq_one.mp
  change Nat.card (C ⧸ N) = 1
  apply hp.card_eq_or_dvd.resolve_right
  intro hd
  have hh := hd.trans N.card_quotient_dvd_card
  rw [hc] at hh
  norm_num at hh

private theorem borel_le_cubic_sup
    (K S A C : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = S ⊓ K)
    (hCK : C ≤ K) (hCA : C ≤ A) (hc : Nat.card C = 3)
    (hAS : A ≤ normalizer (S : Set G)) :
    ChapterF.Source.borel K S ≤ A ⊔ S := by
  have hP' : (P : Subgroup K) = (S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le inf_le_right]
  have hN : (normalizer (P : Set K)).map K.subtype = ChapterF.Source.borel K S := by
    change (normalizer ((P : Subgroup K) : Set K)).map K.subtype = _
    rw [hP', ← subgroupOf_normalizer_eq (show S ⊓ K ≤ K from inf_le_right),
      subgroupOf_map_subtype]
    exact inf_comm _ _
  have hCN : C ≤ normalizer (S ⊓ K : Set G) :=
    (le_inf (hCA.trans hAS) (hCK.trans K.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hCP : C.subgroupOf K ≤ normalizer (P : Set K) := by
    change C.subgroupOf K ≤ normalizer ((P : Subgroup K) : Set K)
    rw [hP', ← subgroupOf_normalizer_eq (show S ⊓ K ≤ K from inf_le_right)]
    exact fun x hx => hCN hx
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : IsPGroup 2 q.ker := by
    have he : q.ker = pCore 2 K := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (N := pCore 2 K) x
    rw [he]
    exact pCore_isPGroup
  have hcs : Nat.card (C.subgroupOf K) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv).trans hc
  have hn := Theory.AlternatingFive.sylow_normalizer_eq_sup_cubic_of_two_kernel
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk P (C.subgroupOf K) hcs hCP
  have hm := congrArg (map K.subtype) hn
  rw [hN, Subgroup.map_sup, hP, map_subgroupOf_eq_of_le hCK] at hm
  rw [hm]
  exact sup_le (inf_le_left.trans le_sup_right) (hCA.trans le_sup_left)

variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original order-nine Cartan contains a cubic in the original component. -/
theorem old_residual_cartan_component_cubic
    (A : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA : Nat.card A = 9) :
    ∃ C : Subgroup G, C ≤ A ∧ C ≤ L ∧ Nat.card C = 3 := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp m.sylow_not_normalizes_component
  let R := localOrbit T L
  have hAR : A ≤ R := hAB.trans ((map_subtype_le _).trans inf_le_left)
  have hLR : L ≤ R := le_componentOrbit L T
  let q := originalA5ProductProjection D e m.sylow_not_normalizes_component ht htn
  have hk : IsPGroup 2 q.ker := by
    rw [originalA5ProductProjection_ker]
    exact pCore_isPGroup
  let r := q.comp (inclusion hAR)
  have hi : Function.Injective r :=
    source_a5_borel_torus_quotient_injective A hAB (IsPGroup.of_card (n := 2) hA) q hk
  have ha := Theory.AlternatingFive.nine_torus_coordinate_kernels r hi
    (IsPGroup.of_card (n := 2) hA) hA
  let E := ((MonoidHom.snd _ _).comp r).ker
  have hE : Nat.card E = 3 := ha.2.1
  let C := E.map A.subtype
  have hC : Nat.card C = 3 := by
    rw [card_map_of_injective A.subtype_injective]
    exact hE
  refine ⟨C, map_subtype_le _, ?_, hC⟩
  let J := L.subgroupOf R
  let ER := E.map (inclusion hAR)
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hLR).mpr
    (source_nonnormal_orbit_le_normalizer D m.sylow_not_normalizes_component)
  have hER : Nat.card ER = 3 := by
    rw [card_map_of_injective (inclusion_injective hAR)]
    exact hE
  have him : ER.map q ≤ J.map q := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨a,ha,rfl⟩ := hx
    have hs : (q (inclusion hAR a)).2 = 1 := ha
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)))
      (q (inclusion hAR a)).1
    refine mem_map.mpr ⟨inclusion hLR l,l.property,?_⟩
    change q ⟨l,hLR l.property⟩ = _
    rw [originalA5ProductProjection_first]
    exact Prod.ext hl hs.symm
  have hsup : ER ≤ J ⊔ q.ker := by
    have hh := map_le_iff_le_comap.mp him
    rwa [comap_map_eq] at hh
  have hle : ER ≤ J := le_normal_of_isPPerfect_of_le_sup_pGroup ER J q.ker
    (cubic_twoPerfect hER) hk hsup
  have hm := map_mono (f := R.subtype) hle
  rw [map_subgroupOf_eq_of_le hLR] at hm
  change (E.map (inclusion hAR)).map R.subtype ≤ L at hm
  rw [map_map] at hm
  exact hm

/-- The component Borel is contained in the supplied Cartan times S. -/
theorem old_residual_component_borel_le_cartan_sup
    (A S : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA : Nat.card A = 9)
    (hST : S ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ⊓ localOrbit T L ≤ S)
    (hAS : A ≤ normalizer (S : Set G)) :
    ChapterF.Source.borel L S ≤ A ⊔ S := by
  obtain ⟨C,hCA,hCL,hC⟩ := m.old_residual_cartan_component_cubic A hAB hA
  obtain ⟨P,hP⟩ := m.old_residual_component_sylow
  have heq : (T : Subgroup G) ⊓ L = S ⊓ L := by
    apply le_antisymm
    · exact le_inf ((inf_le_inf_left _ (le_componentOrbit L T)).trans hTL) inf_le_right
    · exact inf_le_inf_right _ hST
  exact borel_le_cubic_sup L S A C e P (hP.trans heq) hCL hCA hC hAS

omit m in
/-- The old residual Borel is contained in the same Cartan times S. -/
theorem old_residual_borel_le_cartan_sup
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸ pCore 2 ((pResidual 2 H).map H.subtype)) ≃*
      alternatingGroup (Fin 5))
    (A B S : Subgroup G) (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB : Nat.card B = 3) (hST : S ≤ (T : Subgroup G))
    (hTK : (T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype ≤ S)
    (hAS : A ≤ normalizer (S : Set G)) :
    ChapterF.Source.borel ((pResidual 2 H).map H.subtype) S ≤ A ⊔ S := by
  let K := (pResidual 2 H).map H.subtype
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hKH : K ≤ H := map_subtype_le _
  have hHN : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  obtain ⟨P,hP⟩ := (T.subtype hTH).exists_map_subtype_eq_inf_of_normalizes hKH hHN
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hP
  have heq : (T : Subgroup G) ⊓ K = S ⊓ K :=
    le_antisymm (le_inf hTK inf_le_right) (inf_le_inf_right _ hST)
  exact borel_le_cubic_sup K S A B eK P (hP.trans heq) hBK hBA hB hAS

/-- The literal common Borel for the ordered pair (K,L) lies in AS. -/
theorem old_residual_common_borel_le_cartan_sup
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸ pCore 2 ((pResidual 2 H).map H.subtype)) ≃*
      alternatingGroup (Fin 5))
    (A B S : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hST : S ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ⊓ localOrbit T L ≤ S)
    (hTK : (T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype ≤ S)
    (hAS : A ≤ normalizer (S : Set G)) :
    ChapterF.Source.commonBorel ![(pResidual 2 H).map H.subtype,L] S ≤ A ⊔ S := by
  have hL := m.old_residual_component_borel_le_cartan_sup A S hAB hA hST hTL hAS
  have hK := old_residual_borel_le_cartan_sup hH eK A B S hBA hBK hB hST hTK hAS
  exact sup_le (sup_le hK hL) le_sup_right
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
