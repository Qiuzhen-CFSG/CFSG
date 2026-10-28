module
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.OddSeries
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Minimal supplements in the odd quotient-lifting branch

In a genuine minimal supplement, suppose the image has a two--p series
and its prescribed Sylow subgroup is its whole local tau. E.1.10(3)
gives the two--p--two series upstairs. The Sylow subgroup then centralizes
the actor modulo the two-core, so it normalizes the odd-core commutator.
The preimage of this commutator joined with the Sylow covers the quotient.
Minimality makes it the whole supplement and removes the extra odd kernel.

The resulting lifting theorem accepts an arbitrary surjection. It transports
cores, the actor and its rank through the literal quotient by that map's
kernel, and constructs an E-member covering the reduced image. Its reduced
image assumptions remain explicit; shrinking the original E-member is a
separate step.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of E.1.10(7), printed pp.211--212 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] [Finite H] in
private theorem odd_core_map {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f : G →* H) (hf : Function.Surjective f)
    (hq : IsPGroup 2 (G ⧸ pCore p G)) :
    (pCore p G).map f = pCore p H := by
  let N := (pCore p G).map f
  let : N.Normal := Normal.map inferInstance f hf
  have hN : IsPGroup 2 (H ⧸ N) := hq.of_surjective
    (QuotientGroup.map (pCore p G) N f (le_comap_map f _))
    (QuotientGroup.map_surjective_of_surjective _ _ f
      (QuotientGroup.mk_surjective.comp hf) (le_comap_map f _))
  exact (odd_core_of_normal_p_subgroup hp N (pCore_isPGroup.map f) hN).symm

private theorem normal_sup_sylow_of_two_quotient (S : Sylow 2 G)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 (G ⧸ N)) :
    N ⊔ (S : Subgroup G) = ⊤ := by
  apply top_le_iff.mp
  rw [← pResidual_sup_sylow_eq_top S]
  exact sup_le_sup (sInf_le ⟨inferInstance, hN⟩) le_rfl

omit [Finite G] in
private theorem residual_two_p_series {p : ℕ}
    (hs : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ pCore p (G ⧸ pCore 2 G))) :
    IsPGroup p ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) := by
  let R := pResidual 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.subgroupMap R
  have hf : Function.Surjective f := q.subgroupMap_surjective R
  have hR : R.map q ≤ pCore p (G ⧸ pCore 2 G) :=
    (map_pResidual_le 2 q).trans (sInf_le ⟨inferInstance, hs⟩)
  have himage : IsPGroup p (R.map q) := pCore_isPGroup.to_le hR
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = (q.subgroupMap R).ker from rfl,
      ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hkle : f.ker ≤ pCore 2 R := le_sSup ⟨inferInstance, hk⟩
  have hi : IsPGroup p (R ⧸ f.ker) :=
    himage.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  exact hi.of_surjective (QuotientGroup.map f.ker (pCore 2 R) (MonoidHom.id R) hkle)
    (QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id R)
      QuotientGroup.mk_surjective hkle)

omit [Finite G] in
private theorem normalizes_commutator_of_normalizes (P B S : Subgroup G)
    (hP : S ≤ normalizer (P : Set G)) (hB : S ≤ normalizer (B : Set G)) :
    S ≤ normalizer (⁅P, B⁆ : Subgroup G) := by
  intro s hs
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hP hs),
    mem_normalizer_iff_map_conj_eq.mp (hB hs)]

/-- Minimality forces full odd-core commutation after the tau reduction.
The kernel may contain odd-order elements. -/
theorem IsMinimalSupplement.oddCore_eq_commutator (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hseries : IsPGroup 2 ((K ⧸ pCore 2 K) ⧸ pCore p (K ⧸ pCore 2 K)))
    (htau : tau (((T : Subgroup G).subgroupOf K).map
        ((QuotientGroup.mk' Y).subgroupMap K))
      ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)) =
        ((T : Subgroup G).subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))
    (hcomm : pCore p ((K.map (QuotientGroup.mk' Y)) ⧸
        pCore 2 (K.map (QuotientGroup.mk' Y))) =
      ⁅pCore p ((K.map (QuotientGroup.mk' Y)) ⧸
        pCore 2 (K.map (QuotientGroup.mk' Y))),
        ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)).map
          (QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y))))⁆) :
    pCore p (K ⧸ pCore 2 K) =
      ⁅pCore p (K ⧸ pCore 2 K),
        (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))⁆ := by
  let I := K.map (QuotientGroup.mk' Y)
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let S : Sylow 2 K := T.subtype h.1.1
  let q := QuotientGroup.mk' (pCore 2 K)
  let r := QuotientGroup.mk' (pCore 2 I)
  let S₂ : Sylow 2 (K ⧸ pCore 2 K) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  let B := (A.subgroupOf K).map q
  let P := pCore p (K ⧸ pCore 2 K)
  let C := ⁅P, B⁆
  have hc : pCore 2 K ≤ (pCore 2 I).comap f :=
    map_le_iff_le_comap.mp (h.map_twoCore T).le
  let g := QuotientGroup.map (pCore 2 K) (pCore 2 I) f hc
  have hg : Function.Surjective g := QuotientGroup.map_surjective_of_surjective
    _ _ f (QuotientGroup.mk_surjective.comp hf) hc
  have hqr : g.comp q = r.comp f := rfl
  have hPg : P.map g = pCore p (I ⧸ pCore 2 I) := odd_core_map hp g hg hseries
  have hBg : B.map g = ((A.subgroupOf K).map f).map r := by
    rw [map_map, hqr, ← map_map]
  have hCg : C.map g = pCore p (I ⧸ pCore 2 I) := by
    rw [map_commutator, hPg, hBg]
    exact hcomm.symm
  have ht : tau (S : Subgroup K) (A.subgroupOf K) = (S : Subgroup K) := by
    change tau ((T : Subgroup G).subgroupOf K) (A.subgroupOf K) = _
    rw [h.tau_eq_preimage T A hAT, htau]
    exact inf_eq_left.mpr (le_comap_map f _)
  have hSB : (S₂ : Subgroup (K ⧸ pCore 2 K)) ≤ centralizer (B : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅(S : Subgroup K).map q, (A.subgroupOf K).map q⁆ = ⊥
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha s hs
    exact (mem_centralizerModulo_iff.mp (ht.symm ▸ hs)).2 a ha
  have hSC : (S₂ : Subgroup (K ⧸ pCore 2 K)) ≤ normalizer (C : Set _) :=
    normalizes_commutator_of_normalizes P B _ le_normalizer_of_normal
      (hSB.trans (centralizer_le_normalizer _))
  let L := (C ⊔ (S₂ : Subgroup (K ⧸ pCore 2 K))).comap q
  have hSL : (S : Subgroup K) ≤ L := by
    intro s hs
    exact (le_sup_right : (S₂ : Subgroup (K ⧸ pCore 2 K)) ≤ _)
      (mem_map_of_mem q hs)
  have hLq : L.map q = C ⊔ (S₂ : Subgroup (K ⧸ pCore 2 K)) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hLf : L.map f = ⊤ := by
    have hm : (L.map f).map r = ⊤ := by
      rw [map_map, ← hqr, ← map_map, hLq, Subgroup.map_sup, hCg]
      have hSg : (S₂ : Subgroup (K ⧸ pCore 2 K)).map g =
          ((S : Subgroup K).map f).map r := by
        change ((S : Subgroup K).map q).map g = _
        rw [map_map, hqr, ← map_map]
      rw [hSg]
      exact normal_sup_sylow_of_two_quotient
        ((S.mapSurjective hf).mapSurjective (QuotientGroup.mk'_surjective _)) _
        (hseries.of_surjective
          (QuotientGroup.map P (pCore p (I ⧸ pCore 2 I)) g
            (map_le_iff_le_comap.mp hPg.le))
          (QuotientGroup.map_surjective_of_surjective _ _ g
            (QuotientGroup.mk_surjective.comp hg) (map_le_iff_le_comap.mp hPg.le)))
    have hcore : pCore 2 I ≤ L.map f :=
      (pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hf)).trans (map_mono hSL)
    have he := congrArg (Subgroup.comap r) hm
    rwa [comap_map_eq, comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hcore] at he
  have hLtop : L = ⊤ := h.eq_top_of_map_eq_top L hSL hLf
  have hCS : C ⊔ (S₂ : Subgroup (K ⧸ pCore 2 K)) = ⊤ := by
    rw [← hLq, hLtop, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have : C.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (by
    rw [← hCS]
    exact sup_le le_normalizer hSC))
  exact odd_core_of_normal_p_subgroup hp C
    (pCore_isPGroup.to_le (commutator_le_left P B))
    (isPGroup_quotient_of_sup_eq_top C _ S₂.isPGroup' hCS)

/-- The odd alternative lifts once the source residual--tau reduction has
provided the two--p image series and made the image Sylow equal its tau. -/
theorem IsMinimalSupplement.oddCase_of_reduced_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (hYX : Y ≤ X)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpX : IsPGroup p (((K ⊓ X).map (QuotientGroup.mk' Y)) ⧸
      pCore 2 ((K ⊓ X).map (QuotientGroup.mk' Y))))
    (htau : tau (((T : Subgroup G).subgroupOf K).map
        ((QuotientGroup.mk' Y).subgroupMap K))
      ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)) =
        ((T : Subgroup G).subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))
    (hne : pCore p ((K.map (QuotientGroup.mk' Y)) ⧸
        pCore 2 (K.map (QuotientGroup.mk' Y))) ≠ ⊥)
    (hcomm : pCore p ((K.map (QuotientGroup.mk' Y)) ⧸
        pCore 2 (K.map (QuotientGroup.mk' Y))) =
      ⁅pCore p ((K.map (QuotientGroup.mk' Y)) ⧸
        pCore 2 (K.map (QuotientGroup.mk' Y))),
        ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)).map
          (QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y))))⁆)
    (hrank : Group.rank (((A.subgroupOf K).map
        ((QuotientGroup.mk' Y).subgroupMap K)).map
          (QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y))))) = 1) :
    ECaseOdd A K := by
  have hs := h.oddSeries T hYX hp hpX
  refine ⟨p, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, hs, ?_,
    h.oddCore_eq_commutator T A hAT hp hs htau hcomm,
    (h.rank_twoCore_image T A hAT).trans hrank⟩
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hc := map_le_iff_le_comap.mp (h.map_twoCore T).le
  let g := QuotientGroup.map (pCore 2 K)
    (pCore 2 (K.map (QuotientGroup.mk' Y))) f hc
  have hg : Function.Surjective g := QuotientGroup.map_surjective_of_surjective
    _ _ f (QuotientGroup.mk_surjective.comp
      ((QuotientGroup.mk' Y).subgroupMap_surjective K)) hc
  intro hz
  apply hne
  rw [← odd_core_map hp g hg hs, hz, Subgroup.map_bot]

private theorem IsMinimalSupplement.isEMemberAt_of_oddCase {i : ℕ} (T : Sylow 2 G)
    {X Y K : Subgroup G} (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (ho : ECaseOdd A K) (hi : 1 ≤ i) : IsEMemberAt i (T : Subgroup G) A K := by
  have hr : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 1 := by
    obtain ⟨p, _, _, _, _, _, hr⟩ := ho
    exact hr
  refine ⟨⟨inferInstance, hAT, hAT.trans h.1.1,
    le_inf (tau_le _ _) ((tau_le _ _).trans h.1.1), ?_, Or.inl ho⟩,
    Or.inl ⟨ho, hr ▸ hi⟩⟩
  exact ⟨T.subtype h.1.1, Sylow.coe_subtype _ _⟩

/-- Lift a reduced odd quotient whose prescribed Sylow is its entire tau.
The homomorphism is arbitrary and may have an odd part in its kernel. -/
theorem exists_odd_lift_of_surjective_reduced_image {i : ℕ} (T : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (f : G →* H) (hf : Function.Surjective f)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H)))
    (hne : pCore p (H ⧸ pCore 2 H) ≠ ⊥)
    (hcomm : pCore p (H ⧸ pCore 2 H) =
      ⁅pCore p (H ⧸ pCore 2 H), (A.map f).map (QuotientGroup.mk' (pCore 2 H))⁆)
    (hrank : Group.rank ((A.map f).map (QuotientGroup.mk' (pCore 2 H))) = 1)
    (htau : tau ((T : Subgroup G).map f) (A.map f) = (T : Subgroup G).map f)
    (hi : 1 ≤ i) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧ J.map f = ⊤ := by
  let Y := f.ker
  let q := QuotientGroup.mk' Y
  obtain ⟨K, hK, hKtop⟩ := exists_minimalResidualSupplement T Y
  let eY := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e := (MulEquiv.subgroupCongr hKtop).trans (Subgroup.topEquiv.trans eY)
  have he : e.toMonoidHom.comp (q.subgroupMap K) = f.comp K.subtype := rfl
  let e₂ := QuotientGroup.congr (pCore 2 (K.map q)) (pCore 2 H) e (pCore_map_iso 2 e)
  have he₂ : e₂.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K.map q))) =
      (QuotientGroup.mk' (pCore 2 H)).comp e.toMonoidHom := rfl
  have hA : ((A.subgroupOf K).map (q.subgroupMap K)).map e.toMonoidHom = A.map f := by
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le (hAT.trans hK.1.1)]
  have hT : (((T : Subgroup G).subgroupOf K).map (q.subgroupMap K)).map
      e.toMonoidHom = (T : Subgroup G).map f := by
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le hK.1.1]
  have hA₂ : (((A.subgroupOf K).map (q.subgroupMap K)).map
      (QuotientGroup.mk' (pCore 2 (K.map q)))).map e₂.toMonoidHom =
        (A.map f).map (QuotientGroup.mk' (pCore 2 H)) := by
    rw [map_map, he₂, ← map_map, hA]
  let eY₂ := QuotientGroup.congr (pCore 2 (G ⧸ Y)) (pCore 2 H) eY
    (pCore_map_iso 2 eY)
  have hqY : IsPGroup 2 (((G ⧸ Y) ⧸ pCore 2 (G ⧸ Y)) ⧸
      pCore p ((G ⧸ Y) ⧸ pCore 2 (G ⧸ Y))) :=
    hquot.of_equiv (QuotientGroup.congr _ _ eY₂ (pCore_map_iso p eY₂)).symm
  have hpX : IsPGroup p (((K ⊓ (pResidual 2 G ⊔ Y)).map q) ⧸
      pCore 2 ((K ⊓ (pResidual 2 G ⊔ Y)).map q)) := by
    rw [hK.map_inf_eq le_sup_right, Subgroup.map_sup, QuotientGroup.map_mk'_self,
      sup_bot_eq, map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective Y)]
    exact residual_two_p_series hqY
  have ho : ECaseOdd A K := hK.oddCase_of_reduced_image T le_sup_right A hAT hp hpX
    (by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_tau_equiv e, hT, hA]
      exact htau)
    (by
      intro hz
      apply hne
      rw [← pCore_map_iso p e₂, hz, Subgroup.map_bot])
    (by
      apply map_injective (f := e₂.toMonoidHom) e₂.injective
      rw [map_commutator, pCore_map_iso p e₂, hA₂]
      exact hcomm)
    ((Group.rank_congr (((((A.subgroupOf K).map (q.subgroupMap K)).map
      (QuotientGroup.mk' (pCore 2 (K.map q)))).equivMapOfInjective
        e₂.toMonoidHom e₂.injective).trans (MulEquiv.subgroupCongr hA₂))).trans hrank)
  refine ⟨K, hK.isEMemberAt_of_oddCase T A hAT ho hi, ?_⟩
  have heY : eY.toMonoidHom.comp q = f := rfl
  rw [← heY, ← map_map, hKtop, map_top_of_surjective eY.toMonoidHom eY.surjective]

end CFSG.Quasithin.ChapterE
