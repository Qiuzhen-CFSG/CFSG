module

public import Theory.GroupTheory.GeneralizedFitting.TwoCoreOvergroup
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.GeneralizedFitting.PCoreImageCommutator
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Movement detected by the generalized Fitting preimage

An overgroup of O₂,F*(G) has its embedded two-core inside O₂(G).
Consequently a normal two-subgroup of a supplement outside O₂(G) moves
the other factor even modulo O₂(G). If that factor is two-perfect and
its image is a transitive orbit of ordinary components, the component
commutator dichotomy makes the commutator the whole factor. The local-core
lemma also excludes a factor already contained in an overgroup whose
core contains the actor.

Source application: Aschbacher--Smith, 15.2.27(2), printed p.1119.
The image-lifting proof follows the existing PCoreImageCommutator module.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem pCoreIn_le_of_generalizedFitting_preimage_le (D : Subgroup G)
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ D) : D.pCoreIn 2 ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hFq : generalizedFitting (G ⧸ pCore 2 G) ≤ D.map q := by
    have hh := map_mono (f := q) hF
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have he := twoCore_eq_bot_of_generalizedFitting_le (D.map q) hFq
    (pCore_quotient_pCore_eq_bot 2)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hm : (D.pCoreIn 2).map q = ⊥ := by
    rw [map_pCoreIn_of_ker_isPGroup q hk D, pCoreIn, he, Subgroup.map_bot]
  exact ((Subgroup.map_eq_bot_iff _).mp hm).trans_eq (QuotientGroup.ker_mk' _)

theorem commutator_not_le_twoCore_of_preimage_le (K E V : Subgroup G) [K.Normal]
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ K ⊔ E)
    (hV : IsPGroup 2 V) (hVE : V ≤ E) (hEV : E ≤ normalizer (V : Set G))
    (hne : ¬ V ≤ pCore 2 G) : ¬ ⁅K,V⁆ ≤ pCore 2 G := by
  intro hcomm
  let q := QuotientGroup.mk' (pCore 2 G)
  have hc : K.map q ≤ centralizer (V.map q : Set (G ⧸ pCore 2 G)) := by
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hcomm
  have hnorm : K.map q ⊔ E.map q ≤ normalizer (V.map q : Set (G ⧸ pCore 2 G)) :=
    sup_le (hc.trans (centralizer_le_normalizer _))
      ((map_mono hEV).trans (V.le_normalizer_map q))
  have hp : V.map q ≤ (K.map q ⊔ E.map q : Subgroup (G ⧸ pCore 2 G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hV.map q) ((map_mono hVE).trans le_sup_right) hnorm
  have hf : generalizedFitting (G ⧸ pCore 2 G) ≤ K.map q ⊔ E.map q := by
    rw [← Subgroup.map_sup]
    have hh := map_mono (f := q) hF
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have he := twoCore_eq_bot_of_generalizedFitting_le _ hf (pCore_quotient_pCore_eq_bot 2)
  rw [pCoreIn, he, Subgroup.map_bot] at hp
  exact hne (((Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hp)).trans_eq (QuotientGroup.ker_mk' _))

theorem le_twoCore_of_preimage_le_of_local_core (K E V H : Subgroup G) [K.Normal]
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ K ⊔ E)
    (hVE : V ≤ E) (hEV : E ≤ normalizer (V : Set G))
    (hKH : K ≤ H) (hVH : V ≤ H.pCoreIn 2) : V ≤ pCore 2 G := by
  let P := K ⊔ V
  let D := K ⊔ E
  have hPH : P ≤ H := sup_le hKH (hVH.trans (pCoreIn_le 2 H))
  have hVP : V ≤ P.pCoreIn 2 := by
    have hn : P ≤ normalizer ((H.pCoreIn 2 ⊓ P : Subgroup G) : Set G) :=
      (le_inf (hPH.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))) P.le_normalizer).trans inf_normalizer_le_normalizer_inf
    have hv := le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 H).to_le (show H.pCoreIn 2 ⊓ P ≤ H.pCoreIn 2 from inf_le_left))
      (show H.pCoreIn 2 ⊓ P ≤ P from inf_le_right) hn
    exact (le_inf hVH le_sup_right).trans hv
  have hnorm : D ≤ normalizer (P : Set G) := by
    apply sup_le
    · exact (show K ≤ P from le_sup_left).trans P.le_normalizer
    · exact (le_inf le_normalizer_of_normal hEV).trans
        (normalizer_inf_normalizer_le_normalizer_sup K V)
  exact hVP.trans ((pCoreIn_mono_of_normalizes (sup_le le_sup_left (hVE.trans le_sup_right))
    hnorm).trans (pCoreIn_le_of_generalizedFitting_preimage_le D hF))

omit [Finite G] in
theorem commutator_eq_of_component_orbit (K L A V : Subgroup G)
    (hL : IsComponent G L)
    (hK : K = ⨆ a : A, L.map (MulAut.conj (a : G)).toMonoidHom)
    (hAV : A ≤ normalizer (V : Set G)) (hVK : V ≤ normalizer (K : Set G))
    (hne : ⁅K,V⁆ ≠ ⊥) : ⁅K,V⁆ = K := by
  have hAK : A ≤ normalizer (K : Set G) := hK ▸ le_normalizer_iSup_conjugates L A
  have hAC : A ≤ normalizer ((⁅K,V⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hAK ha),
      mem_normalizer_iff_map_conj_eq.mp (hAV ha)]
  have hLC : L ≤ ⁅K,V⁆ := by
    rcases hL.commutator_dichotomy V with hz | he
    · have hKC : K ≤ centralizer (V : Set G) := by
        rw [hK]
        exact iSup_conjugates_le_of_le_normalizer L A _
          (commutator_eq_bot_iff_le_centralizer.mp hz)
          (hAV.trans (normalizer_le_normalizer_centralizer V))
      exact (hne (commutator_eq_bot_iff_le_centralizer.mpr hKC)).elim
    · exact (le_iSup_conjugates L V).trans (he.symm.le.trans
        (commutator_mono (hK ▸ le_iSup_conjugates L A) le_rfl))
  exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hVK)
    (hK.le.trans (iSup_conjugates_le_of_le_normalizer L A _ hLC hAC))

omit [Finite G] in
private theorem lift_pPerfect_image (K C Q : Subgroup G) [Q.Normal]
    (hCK : C ≤ K) (hn : K ≤ normalizer (C : Set G))
    (hQ : IsPGroup 2 Q) (hK : IsPPerfect 2 K)
    (hmap : C.map (QuotientGroup.mk' Q) = K.map (QuotientGroup.mk' Q)) : C = K := by
  let N := C.subgroupOf K
  let R := Q.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hs : N ⊔ R = ⊤ := by
    apply top_unique
    intro k _
    have hk : QuotientGroup.mk' Q (k : G) ∈ C.map (QuotientGroup.mk' Q) := by
      rw [hmap]
      exact mem_map_of_mem _ k.property
    obtain ⟨c, hc, he⟩ := hk
    have hu : c⁻¹ * (k : G) ∈ Q := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' Q (c⁻¹ * (k : G)) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hprod : (⟨c, hCK hc⟩ : K) *
        ⟨c⁻¹ * (k : G), K.mul_mem (K.inv_mem (hCK hc)) k.property⟩ = k := by
      ext
      simp
    rw [← hprod]
    exact (N ⊔ R).mul_mem ((show N ≤ N ⊔ R from le_sup_left) hc)
      ((show R ≤ N ⊔ R from le_sup_right) hu)
  have he : N = ⊤ := hK N inferInstance
    (isPGroup_quotient_of_sup_eq_top N R hQ.comap_subtype hs)
  exact le_antisymm hCK (subgroupOf_eq_top.mp he)

theorem commutator_eq_of_component_orbit_image (K E V A : Subgroup G) [K.Normal]
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ K ⊔ E)
    (hK : IsPPerfect 2 K) (hV : IsPGroup 2 V)
    (hVE : V ≤ E) (hEV : E ≤ normalizer (V : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hne : ¬ V ≤ pCore 2 G)
    (horbit : ∃ L : Subgroup (G ⧸ pCore 2 G), IsComponent (G ⧸ pCore 2 G) L ∧
      K.map (QuotientGroup.mk' (pCore 2 G)) =
        ⨆ a : A.map (QuotientGroup.mk' (pCore 2 G)),
          L.map (MulAut.conj (a : G ⧸ pCore 2 G)).toMonoidHom) : ⁅K,V⁆ = K := by
  let q := QuotientGroup.mk' (pCore 2 G)
  obtain ⟨L,hL,ho⟩ := horbit
  have hne' : ⁅K.map q,V.map q⁆ ≠ ⊥ := by
    intro he
    have hh : ⁅K,V⁆.map q = ⊥ := (map_commutator K V q).trans he
    exact commutator_not_le_twoCore_of_preimage_le K E V hF hV hVE hEV hne
      (((Subgroup.map_eq_bot_iff _).mp hh).trans_eq (QuotientGroup.ker_mk' _))
  have hnorm : A.map q ≤ normalizer (V.map q : Set (G ⧸ pCore 2 G)) :=
    (map_mono hAV).trans (V.le_normalizer_map q)
  have he : ⁅K,V⁆.map q = K.map q := by
    rw [map_commutator]
    exact commutator_eq_of_component_orbit (K.map q) L (A.map q) (V.map q) hL ho hnorm
      le_normalizer_of_normal hne'
  exact lift_pPerfect_image K ⁅K,V⁆ (pCore 2 G) (commutator_le_left K V)
    (normalizer_commutator_ge_left K V) pCore_isPGroup hK he

end Theory.GroupTheory
