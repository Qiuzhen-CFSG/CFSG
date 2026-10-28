module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Radical
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Residual
public import Theory.GroupTheory.CComponent.LayerTransport

/-!
# Component data in a minimal quotient supplement

A minimal Sylow supplement has a solvable kernel, so its radical quotient is
canonically isomorphic to the radical quotient of its image. The exact local
tau identity identifies the conjugating subgroup under this isomorphism.
Consequently the chosen component, its entire local tau orbit, and both the
commutator and nonnormalizing alternatives lift. The actor's rank is unchanged.
The radical and residual conclusions are the corresponding clauses of E.1.10(4);
the layer quotient is transported through the actual radical isomorphism.

The consumer `ReverseLift.Component` constructs the image isomorphism and both
map identities from a minimal supplement in the full preimage of the member.
No component correspondence or orbit-generation premise is added there.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2(E2) and the component case of E.1.10(7), printed pp.210--212.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
private theorem closed_equiv (h : IsTwoClosed G) (e : G ≃* H) : IsTwoClosed H := by
  obtain ⟨S, hn⟩ := h
  exact ⟨S.mapSurjective e.surjective, hn.map e.toMonoidHom e.surjective⟩

omit [Finite G] [Finite H] in
private theorem two_quotient_equiv {N : Subgroup G}
    (h : HasTwoGroupQuotient N) (e : G ≃* H) :
    HasTwoGroupQuotient (N.map e.toMonoidHom) := by
  obtain ⟨hn, hp⟩ := h
  let := hn
  let := hn.map e.toMonoidHom e.surjective
  exact ⟨inferInstance, hp.of_equiv (QuotientGroup.congr N _ e rfl)⟩

omit [Finite G] [Finite H] in
private theorem conjugate_join_map_le (u : G →* H) (B C : Subgroup G) :
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

omit [Finite G] [Finite H] in
private theorem conjugate_join_map (e : G ≃* H) (D L : Subgroup G) :
    (conjugateJoin D L).map e.toMonoidHom =
      conjugateJoin (D.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  apply le_antisymm (conjugate_join_map_le e.toMonoidHom D L)
  have h := map_mono (f := e.toMonoidHom)
    (conjugate_join_map_le e.symm.toMonoidHom (D.map e.toMonoidHom) (L.map e.toMonoidHom))
  simpa [map_map] using h

private theorem quotient_image (e : G ≃* H) (B : Subgroup G) :
    (B.map (QuotientGroup.mk' (solvableRadical G))).map
        (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).toMonoidHom =
      (B.map e.toMonoidHom).map (QuotientGroup.mk' (solvableRadical H)) := by
  rw [map_map, map_map]
  rfl

/-- A minimal supplement lifts the component case, and preserves the actor's rank,
when its actual quotient image is identified with the given component member.
The hypotheses identify the prescribed Sylow and actor through the literal
quotient map; the local tau is then transported by minimality. -/
theorem IsMinimalSupplement.component_of_image_equiv (T : Sylow 2 G)
    {X Y K A : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (hAT : A ≤ (T : Subgroup G))
    {U B I : Subgroup H} (hc : ECaseComponent U B I)
    (e : K.map (QuotientGroup.mk' Y) ≃* I)
    (hT : (((T : Subgroup G).subgroupOf K).map
      ((QuotientGroup.mk' Y).subgroupMap K)).map e.toMonoidHom = U.subgroupOf I)
    (hA : ((A.subgroupOf K).map
      ((QuotientGroup.mk' Y).subgroupMap K)).map e.toMonoidHom = B.subgroupOf I) :
    ECaseComponent (T : Subgroup G) A K ∧
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) =
      Group.rank ((B.subgroupOf I).map (QuotientGroup.mk' (solvableRadical I))) := by
  let V := K.map (QuotientGroup.mk' Y)
  let eR := QuotientGroup.congr (solvableRadical V) (solvableRadical I) e
    (map_solvableRadical_equiv e)
  let r := (h.radicalQuotientEquiv T).trans eR
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  let b := (B.subgroupOf I).map (QuotientGroup.mk' (solvableRadical I))
  let d := (tau ((T : Subgroup G).subgroupOf K) (A.subgroupOf K)).map
    (QuotientGroup.mk' (solvableRadical K))
  let c := (tau (U.subgroupOf I) (B.subgroupOf I)).map
    (QuotientGroup.mk' (solvableRadical I))
  have ha : a.map r.toMonoidHom = b := by
    change a.map (eR.toMonoidHom.comp (h.radicalQuotientEquiv T).toMonoidHom) = b
    rw [← map_map, h.map_radical_quotient_image T, quotient_image, hA]
  have hd : d.map r.toMonoidHom = c := by
    change d.map (eR.toMonoidHom.comp (h.radicalQuotientEquiv T).toMonoidHom) = c
    rw [← map_map, h.map_local_tau_radical_image T A hAT, quotient_image,
      map_tau_equiv, hT, hA]
  have hrank : Group.rank a = Group.rank b :=
    Group.rank_congr ((a.equivMapOfInjective r.toMonoidHom r.injective).trans
      (MulEquiv.subgroupCongr ha))
  refine ⟨?_, hrank⟩
  obtain ⟨hclosed, hlayer, hres, L, hL, horbit, halt⟩ := hc
  have hclosedV : IsTwoClosed (solvableRadical V) := by
    exact closed_equiv hclosed
      (((solvableRadical I).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
        (MulEquiv.subgroupCongr (map_solvableRadical_equiv e.symm)))
  have hresV : pResidual 2 V = solvableResidual V := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pResidual 2 e, map_solvableResidual_eq e.toMonoidHom e.surjective, hres]
  refine ⟨h.twoClosed_solvableRadical T hclosedV, ?_,
    h.pResidual_eq_solvableResidual T hresV,
    L.map r.symm.toMonoidHom, hL.map_equiv r.symm, ?_, ?_⟩
  · have hh := two_quotient_equiv hlayer r.symm
    rwa [map_componentLayer_equiv_of_solvableRadical_eq_bot
      solvableRadical_quotient_solvableRadical solvableRadical_quotient_solvableRadical] at hh
  · have hh := congrArg (Subgroup.map r.symm.toMonoidHom) horbit
    rw [map_componentLayer_equiv_of_solvableRadical_eq_bot
      solvableRadical_quotient_solvableRadical solvableRadical_quotient_solvableRadical,
      conjugate_join_map] at hh
    have hd' : c.map r.symm.toMonoidHom = d := by rw [← hd]; simp [map_map]
    change componentLayer (K ⧸ solvableRadical K) = conjugateJoin d _
    exact hh.trans (congrArg (fun z => conjugateJoin z (L.map r.symm.toMonoidHom)) hd')
  · have ha' : b.map r.symm.toMonoidHom = a := by rw [← ha]; simp [map_map]
    rcases halt with hcomm | ⟨hn, hr⟩
    · left
      have hh := congrArg (Subgroup.map r.symm.toMonoidHom) hcomm
      rw [map_commutator] at hh
      change L.map r.symm.toMonoidHom = ⁅L.map r.symm.toMonoidHom, a⁆
      exact hh.trans (congrArg (fun z => ⁅L.map r.symm.toMonoidHom, z⁆) ha')
    · right
      refine ⟨?_, hrank.trans hr⟩
      intro hnorm
      apply hn
      have hh := map_mono (f := r.toMonoidHom) hnorm
      rw [ha, map_normalizer_eq_of_bijective _ r.bijective] at hh
      simpa [map_map] using hh

end CFSG.Quasithin.ChapterE
