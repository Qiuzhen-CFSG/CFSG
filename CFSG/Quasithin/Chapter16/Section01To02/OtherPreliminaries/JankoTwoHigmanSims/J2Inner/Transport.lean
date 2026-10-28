module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion

/-!
# Transporting the J₂ shapes and identifying components in E₄ × A₅

An isomorphism transports the actual normal kernel, its embedded factors,
and its quotient. It also preserves the kernel-centralizer containment.
For a component in E₄ × A₅, perfectness kills the first projection. The
second projection is injective and has nontrivial subnormal image in the
simple group A₅, hence is surjective.

Source application: Aschbacher–Smith 16.1.5(8) and 16.1.7(f), pp.1172–1173.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem shape_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : IsQuaternionDihedralProduct G) : IsQuaternionDihedralProduct H := by
  obtain ⟨B, D, hB, hD, hBD, hcomm, hsup⟩ := h
  refine ⟨B.map e.toMonoidHom, D.map e.toMonoidHom,
    hB.map (fun f => (e.subgroupMap B).symm.trans f),
    hD.map (fun f => (e.subgroupMap D).symm.trans f), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf B D e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact hBD
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    exact (e.map_mul b d).symm.trans ((congrArg e (hcomm b hb d hd)).trans (e.map_mul d b))
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]

/-- Transport the actual normal kernel, central-product factors, and quotient. -/
theorem extension_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : IsJ2CoreExtension G) : IsJ2CoreExtension H := by
  obtain ⟨Q, hQn, hshape, ⟨q⟩⟩ := h
  let := hQn
  let : (Q.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  exact ⟨Q.map e.toMonoidHom, inferInstance, shape_transport (e.subgroupMap Q) hshape,
    ⟨(QuotientGroup.congr Q (Q.map e.toMonoidHom) e rfl).symm.trans q⟩⟩

/-- Self-centralization of a normal two-kernel is invariant under isomorphism. -/
theorem selfCentralizing_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : HasSelfCentralizingNormalTwoSubgroup G) :
    HasSelfCentralizingNormalTwoSubgroup H := by
  obtain ⟨Q, hQn, hQp, hQself⟩ := h
  let := hQn
  let : (Q.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  refine ⟨Q.map e.toMonoidHom, inferInstance, hQp.of_equiv (e.subgroupMap Q), ?_⟩
  intro x hx
  refine ⟨e.symm x, hQself ?_, e.apply_symm_apply x⟩
  apply mem_centralizer_iff.mpr
  intro q hq
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    mem_centralizer_iff.mp hx (e q) (Subgroup.mem_map_of_mem e.toMonoidHom hq)

/-- A component in the direct-product class is actually isomorphic to A₅. -/
theorem component_product_equiv (K : Subgroup (E4 × A5)) (hK : IsComponent (E4 × A5) K) :
    Nonempty (K ≃* A5) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  let fst : K →* E4 := (MonoidHom.fst E4 A5).comp K.subtype
  have hfst (k : K) : k.val.1 = 1 := by
    let : Group.IsPerfect fst.range := Group.IsPerfect.range fst
    exact congrArg Subtype.val (Subsingleton.elim (fst.rangeRestrict k) 1)
  let f : K →* A5 := (MonoidHom.snd E4 A5).comp K.subtype
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext ((hfst x).trans (hfst y).symm) h
  have hr : f.range = K.map (MonoidHom.snd E4 A5) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hs : f.range.IsSubnormal := hr ▸ hK.1.map (Prod.snd_surjective)
  have htop : f.range = ⊤ := by
    rcases hs.lt_normal with ht | ⟨N, hN, hKN, hNt⟩
    · exact ht
    rcases hN.eq_bot_or_eq_top with hNb | hNt'
    · have hb : f.range = ⊥ := le_bot_iff.mp (hNb ▸ hKN)
      have htriv : ∀ x : K, x = 1 := by
        intro x
        apply hf
        have hx : f x ∈ f.range := ⟨x, rfl⟩
        simpa only [hb, Subgroup.mem_bot, map_one] using hx
      obtain ⟨x, hx⟩ := exists_ne (1 : K)
      exact (hx (htriv x)).elim
    · exact (hNt.ne hNt').elim
  exact ⟨MulEquiv.ofBijective f ⟨hf, MonoidHom.range_eq_top.mp htop⟩⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
