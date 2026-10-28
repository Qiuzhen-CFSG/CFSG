module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.Inheritance.Tau
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Intrinsic transport of the E-cases

An embedding identifies `K` with its image and identifies the restrictions
of `A` and `T` to these groups. The induced isomorphisms modulo the two-core
and the solvable radical identify the quotient images of `A`, hence preserve
their ranks exactly. They also carry every clause of the odd-prime and
component alternatives to the corresponding clause in the image group.
In particular, the component orbit uses the intrinsic local tau, and both
the commutator and nonnormalizing alternatives are preserved.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Definitions E.1.2 and E.1.5 and Lemma E.1.8, printed pp.210--211.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H]

/-- The intrinsic intersection with `K` is preserved by the isomorphism onto its image. -/
theorem intrinsic_subgroupOf_map (f : G →* H) (hf : Function.Injective f)
    (A K : Subgroup G) :
    (A.subgroupOf K).map (K.equivMapOfInjective f hf).toMonoidHom =
      (A.map f).subgroupOf (K.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem f hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := y.property
    refine ⟨⟨x, hx⟩, ?_, Subtype.ext hxy⟩
    change x ∈ A
    have : f x ∈ A.map f := hxy ▸ hy
    exact (mem_map_iff_mem hf).mp this

private theorem intrinsic_quotient_image (e : G ≃* H) (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (hNM : N.map e.toMonoidHom = M) (A : Subgroup G) :
    (A.map (QuotientGroup.mk' N)).map
        (QuotientGroup.congr N M e hNM).toMonoidHom =
      (A.map e.toMonoidHom).map (QuotientGroup.mk' M) := by
  rw [map_map, map_map]
  congr 1

private theorem layer_map_le (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom ≤ componentLayer H := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  exact map_le_iff_le_comap.mp (le_sSup (hL.map_equiv e))

private theorem intrinsic_layer_map (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom = componentLayer H := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem conjugateJoin_map_le (u : G →* H) (B C : Subgroup G) :
    (conjugateJoin B C).map u ≤ conjugateJoin (B.map u) (C.map u) := by
  unfold conjugateJoin
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro b
  apply le_trans _ (le_iSup_of_le (⟨u b, mem_map_of_mem u b.property⟩ : B.map u) le_rfl)
  apply le_of_eq
  rw [map_map, map_map]
  congr 1
  ext x
  simp

private theorem intrinsic_conjugateJoin_map (e : G ≃* H) (D L : Subgroup G) :
    (conjugateJoin D L).map e.toMonoidHom =
      conjugateJoin (D.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  apply le_antisymm (conjugateJoin_map_le e.toMonoidHom D L)
  have h := map_mono (f := e.toMonoidHom)
    (conjugateJoin_map_le e.symm.toMonoidHom (D.map e.toMonoidHom) (L.map e.toMonoidHom))
  simpa [map_map] using h

private theorem IsTwoClosed.intrinsic_equiv [Finite G] (h : IsTwoClosed G) (e : G ≃* H) :
    IsTwoClosed H := by
  obtain ⟨S, hn⟩ := h
  exact ⟨S.mapSurjective e.surjective, hn.map e.toMonoidHom e.surjective⟩

private theorem HasTwoGroupQuotient.intrinsic_equiv {N : Subgroup G}
    (h : HasTwoGroupQuotient N) (e : G ≃* H) :
    HasTwoGroupQuotient (N.map e.toMonoidHom) := by
  obtain ⟨hn, hp⟩ := h
  let := hn
  let := hn.map e.toMonoidHom e.surjective
  exact ⟨inferInstance, hp.of_equiv (QuotientGroup.congr N _ e rfl)⟩

variable [Finite G] [Finite H]
/-- Exact preservation of the rank of the image of `A` modulo the intrinsic two-core. -/
theorem rank_pCore_quotient_image_map (f : G →* H) (hf : Function.Injective f)
    (A K : Subgroup G) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) =
    Group.rank (((A.map f).subgroupOf (K.map f)).map
      (QuotientGroup.mk' (pCore 2 (K.map f)))) := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map f)) e (pCore_map_iso 2 e)
  have hi := intrinsic_quotient_image e _ _ (pCore_map_iso 2 e) (A.subgroupOf K)
  rw [intrinsic_subgroupOf_map f hf A K] at hi
  exact Group.rank_congr
    ((((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).equivMapOfInjective
      q.toMonoidHom q.injective).trans (MulEquiv.subgroupCongr hi))

/-- Exact preservation of the rank of the image of `A` modulo the intrinsic radical. -/
theorem rank_solvableRadical_quotient_image_map (f : G →* H) (hf : Function.Injective f)
    (A K : Subgroup G) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) =
    Group.rank (((A.map f).subgroupOf (K.map f)).map
      (QuotientGroup.mk' (solvableRadical (K.map f)))) := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr (solvableRadical K) (solvableRadical (K.map f)) e
    (map_solvableRadical_equiv e)
  have hi := intrinsic_quotient_image e _ _ (map_solvableRadical_equiv e) (A.subgroupOf K)
  rw [intrinsic_subgroupOf_map f hf A K] at hi
  exact Group.rank_congr
    ((((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))).equivMapOfInjective
      q.toMonoidHom q.injective).trans (MulEquiv.subgroupCongr hi))

/-- The odd-prime alternative in E.1.2 is preserved by every embedding. -/
theorem ECaseOdd.map_injective {A K : Subgroup G} (h : ECaseOdd A K)
    (f : G →* H) (hf : Function.Injective f) : ECaseOdd (A.map f) (K.map f) := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map f)) e (pCore_map_iso 2 e)
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  have ha : a.map q.toMonoidHom = ((A.map f).subgroupOf (K.map f)).map
      (QuotientGroup.mk' (pCore 2 (K.map f))) := by
    rw [intrinsic_quotient_image, intrinsic_subgroupOf_map]
  obtain ⟨p, hp, ho, hq, hn, hc, hr⟩ := h
  refine ⟨p, hp, ho, ?_, ?_, ?_, ?_⟩
  · exact hq.of_equiv (QuotientGroup.congr _ _ q (pCore_map_iso p q))
  · intro hb
    apply hn
    apply Subgroup.map_injective (f := q.toMonoidHom) q.injective
    rw [pCore_map_iso, hb, Subgroup.map_bot]
  · have hm := congrArg (Subgroup.map q.toMonoidHom) hc
    rw [map_commutator, pCore_map_iso, ha] at hm
    exact hm
  · exact (rank_pCore_quotient_image_map f hf A K).symm.trans hr

/-- The component alternative in E.1.2, including its local tau orbit, is preserved by embeddings. -/
theorem ECaseComponent.map_injective {T A K : Subgroup G} (h : ECaseComponent T A K)
    (f : G →* H) (hf : Function.Injective f) :
    ECaseComponent (T.map f) (A.map f) (K.map f) := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr (solvableRadical K) (solvableRadical (K.map f)) e
    (map_solvableRadical_equiv e)
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  let d := (tau (T.subgroupOf K) (A.subgroupOf K)).map
    (QuotientGroup.mk' (solvableRadical K))
  have ha : a.map q.toMonoidHom = ((A.map f).subgroupOf (K.map f)).map
      (QuotientGroup.mk' (solvableRadical (K.map f))) := by
    rw [intrinsic_quotient_image, intrinsic_subgroupOf_map]
  have hd : d.map q.toMonoidHom =
      (tau ((T.map f).subgroupOf (K.map f)) ((A.map f).subgroupOf (K.map f))).map
        (QuotientGroup.mk' (solvableRadical (K.map f))) := by
    rw [intrinsic_quotient_image, map_tau_equiv, intrinsic_subgroupOf_map,
      intrinsic_subgroupOf_map]
  obtain ⟨hclosed, hlayer, hres, L, hL, horbit, halt⟩ := h
  refine ⟨?_, ?_, ?_, L.map q.toMonoidHom, hL.map_equiv q, ?_, ?_⟩
  · exact hclosed.intrinsic_equiv
      (((solvableRadical K).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (map_solvableRadical_equiv e)))
  · have hh := hlayer.intrinsic_equiv q
    rwa [intrinsic_layer_map] at hh
  · rw [← map_pResidual 2 e, ← map_solvableResidual_eq e.toMonoidHom e.surjective, hres]
  · have hh := congrArg (Subgroup.map q.toMonoidHom) horbit
    rw [intrinsic_layer_map, intrinsic_conjugateJoin_map, hd] at hh
    exact hh
  · rcases halt with hc | ⟨hn, hr⟩
    · left
      have hh := congrArg (Subgroup.map q.toMonoidHom) hc
      rw [map_commutator, ha] at hh
      exact hh
    · right
      refine ⟨?_, (rank_solvableRadical_quotient_image_map f hf A K).symm.trans hr⟩
      intro hh
      apply hn
      rw [← ha, ← map_normalizer_eq_of_bijective L (f := q.toMonoidHom) q.bijective] at hh
      intro x hx
      exact (mem_map_iff_mem (f := q.toMonoidHom) q.injective).mp (hh (mem_map_of_mem q.toMonoidHom hx))

end CFSG.Quasithin.ChapterE
