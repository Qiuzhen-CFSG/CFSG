module
public import CFSG.Quasithin.ChapterE.Section01.Inheritance.OddRestriction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The same odd E-member inside a normal subgroup

Tau restricts exactly to a normal subgroup containing the actor, because
its two-core is the intersection with the ambient two-core. An odd E-member
therefore intersects a normal overgroup of the ambient two-residual to give
an actual rank-one E-member on the same actor and prescribed Sylow. All
quotients and embeddings are the literal subgroup restrictions.

Source: Aschbacher--Smith E.1.2 and E.1.4, pp.209--210, as used in the
changed-Sylow step of 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- In a normal subgroup containing the actor, intrinsic tau is exactly
the restriction of ambient tau. -/
theorem tau_subgroupOf_normal (N T A : Subgroup G) [N.Normal] (hAN : A ≤ N) :
    tau (T.subgroupOf N) (A.subgroupOf N) = (tau T A).subgroupOf N := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxT,hc⟩ := mem_centralizerModulo_iff.mp hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hxT,fun a ha => ?_⟩
    have hh := hc (⟨a,hAN ha⟩ : N) ha
    rw [pCore_eq_comap_of_normal] at hh
    exact hh
  · intro hx
    obtain ⟨hxT,hc⟩ := mem_centralizerModulo_iff.mp hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hxT,fun a ha => ?_⟩
    rw [pCore_eq_comap_of_normal]
    exact hc a ha

private theorem odd_of_map_injective {H : Type*} [Group H] [Finite H]
    {A K : Subgroup G} (f : G →* H) (hf : Function.Injective f)
    (h : ECaseOdd (A.map f) (K.map f)) : ECaseOdd A K := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map f)) e (pCore_map_iso 2 e)
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  have ha : a.map q.toMonoidHom = ((A.map f).subgroupOf (K.map f)).map
      (QuotientGroup.mk' (pCore 2 (K.map f))) := by
    rw [show a.map q.toMonoidHom = ((A.subgroupOf K).map e.toMonoidHom).map
      (QuotientGroup.mk' (pCore 2 (K.map f))) from by rw [map_map,map_map];rfl]
    rw [intrinsic_subgroupOf_map]
  obtain ⟨p,hp,ho,hq,hn,hc,hr⟩ := h
  refine ⟨p,hp,ho,?_,?_,?_,?_⟩
  · exact hq.of_equiv (QuotientGroup.congr _ _ q (pCore_map_iso p q)).symm
  · intro hb
    apply hn
    rw [←pCore_map_iso p q,hb,Subgroup.map_bot]
  · apply map_injective (f := q.toMonoidHom) q.injective
    rw [map_commutator,pCore_map_iso,ha]
    exact hc
  · exact (rank_pCore_quotient_image_map f hf A K).trans hr

/-- Intersecting an odd E-member with a normal subgroup containing the
ambient two-residual and the same actor gives a literal rank-one E-member. -/
theorem IsEMember.odd_subgroupOf_normal {T A K N : Subgroup G} [N.Normal]
    (hK : IsEMember T A K) (ho : ECaseOdd A K)
    (hRN : pResidual 2 G ≤ N) (hAN : A ≤ N) :
    IsEMemberAt 1 (T.subgroupOf N) (A.subgroupOf N) (K.subgroupOf N) ∧
      ECaseOdd (A.subgroupOf N) (K.subgroupOf N) := by
  have hRC : (pResidual 2 K).map K.subtype ≤ K ⊓ N :=
    le_inf (map_subtype_le _) ((map_pResidual_le 2 K.subtype).trans hRN)
  have hodd : ECaseOdd (A.subgroupOf N) (K.subgroupOf N) := by
    apply odd_of_map_injective N.subtype N.subtype_injective
    rw [map_subgroupOf_eq_of_le hAN,subgroupOf_map_subtype]
    exact ho.restrict_of_residual_le inf_le_left (le_inf hK.2.2.1 hAN) hRC
  obtain ⟨p,hp,hoddp,hquot,hne,hcomm,hrank⟩ := hodd
  have hodd' : ECaseOdd (A.subgroupOf N) (K.subgroupOf N) :=
    ⟨p,hp,hoddp,hquot,hne,hcomm,hrank⟩
  have hmember : IsEMember (T.subgroupOf N) (A.subgroupOf N) (K.subgroupOf N) := by
    let := hK.1
    refine ⟨IsElementaryAbelian.subgroupOf hAN,subgroupOf_mono N hK.2.1,
      subgroupOf_mono N hK.2.2.1,?_,?_,Or.inl hodd'⟩
    · rw [tau_subgroupOf_normal N T A hAN]
      exact le_inf (subgroupOf_mono N (hK.2.2.2.1.trans inf_le_left))
        (subgroupOf_mono N (hK.2.2.2.1.trans inf_le_right))
    · obtain ⟨P,hP⟩ := hK.2.2.2.2.1
      obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal (N.subgroupOf K)
      let e : N.subgroupOf K ≃* K.subgroupOf N := {
        toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
      refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
      change (Q : Subgroup (N.subgroupOf K)).map e.toMonoidHom = _
      rw [hQ,hP]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  exact ⟨⟨hmember,Or.inl ⟨hodd',hrank.le⟩⟩,hodd'⟩

end CFSG.Quasithin.ChapterE
