module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Basic
public import Theory.GroupAction.ExtendingSubgroupAutomorphisms
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient

/-!
# Enlarging the moved-space action and identifying its kernels

The order-eight condition forces each Y-member to move the source four-group.
An I₂ image of order 24 is consequently the actual maximal hyperplane stabilizer,
and adjoining X gives all automorphisms. Residual functoriality shows that LX
already induces that image. Once the component argument supplies its PSL₃(2)
core quotient, cardinalities identify the kernel on LX. The kernel on LXT is
then an extension of two-groups, and the quotient equivalences retain the
literal conjugation formula in both automorphism and binary matrix coordinates.

The I₂ image computation and the selected-component argument remain explicit
premises of the assembly at the end; this module does not claim their source
construction. Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.8(2), printed p.1009.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G]

theorem member_not_normalizes_plane [Finite G] {H T V₂ E X : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) (hV₂ : Nat.card V₂ = 4) :
    ¬ X ≤ normalizer (V₂ : Set G) := by
  intro hn
  have hle : movedSpace V₂ X ≤ V₂ := le_normalizer_iff_commutator_le_left.mp hn
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [hX.2.1, hV₂] at hc
  omega

theorem member_normalizes_movedSpace (V₂ X : Subgroup G) :
    X ≤ normalizer (movedSpace V₂ X : Set G) :=
  normalizer_commutator_ge_right V₂ X

theorem sylow_normalizes_movedSpace {H T V₂ X : Subgroup G}
    (hX : ThreeExtension H T X) (hV₂ : T ≤ normalizer (V₂ : Set G)) :
    T ≤ normalizer (movedSpace V₂ X : Set G) := by
  intro t ht
  rw [movedSpace, mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hV₂ ht),
    mem_normalizer_iff_map_conj_eq.mp (hX.T_normalizes ht)]

theorem localJoin_normalizes_movedSpace {H T V₂ X I₂ L₂ U : Subgroup G}
    (hX : ThreeExtension H T X) (hV₂ : T ≤ normalizer (V₂ : Set G))
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ T)
    (hIW : I₂ ≤ normalizer (movedSpace V₂ X : Set G)) :
    localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G) := by
  have hLT : L₂ ⊔ T ≤ normalizer (movedSpace V₂ X : Set G) := by
    rw [← source_I₂_join_T I₂ L₂ U T hI hUT]
    exact sup_le hIW (sylow_normalizes_movedSpace hX hV₂)
  exact sup_le (sup_le (le_sup_left.trans hLT) (member_normalizes_movedSpace V₂ X))
    (le_sup_right.trans hLT)

/-- Restriction of the literal action agrees with conjugation by the smaller actor. -/
theorem conjugation_restrict {A B W : Subgroup G}
    (hA : A ≤ normalizer (W : Set G)) (hB : B ≤ normalizer (W : Set G))
    (hle : A ≤ B) :
    (conjugation B W hB).comp (inclusion hle) = conjugation A W hA := by
  ext a w
  simp only [MonoidHom.comp_apply,conjugation_apply]
  rfl

private theorem action_range_mono {A B W : Subgroup G}
    (hA : A ≤ normalizer (W : Set G)) (hB : B ≤ normalizer (W : Set G))
    (hle : A ≤ B) : (conjugation A W hA).range ≤ (conjugation B W hB).range := by
  rintro a ⟨x,rfl⟩
  exact ⟨inclusion hle x,DFunLike.congr_fun (conjugation_restrict hA hB hle) x⟩

private theorem normalizes_of_action_range_le {A B W D : Subgroup G}
    (hA : A ≤ normalizer (W : Set G)) (hB : B ≤ normalizer (W : Set G))
    (hD : D ≤ W) (hBD : B ≤ normalizer (D : Set G))
    (hr : (conjugation A W hA).range ≤ (conjugation B W hB).range) :
    A ≤ normalizer (D : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha d hd
  obtain ⟨b,hb⟩ := hr ⟨⟨a,ha⟩,rfl⟩
  have he := congrArg (fun f : MulAut W => (f ⟨d,hD hd⟩ : G)) hb
  simp only [conjugation_apply] at he
  rw [← he]
  exact le_normalizer_iff.mp hBD b b.property d hd

private theorem eq_top_of_prime_index {K : Type*} [Group K]
    (P A : Subgroup K) (hP : Nat.Prime P.index) (hPA : P ≤ A) (hAP : ¬ A ≤ P) :
    A = ⊤ := by
  rcases hP.eq_one_or_self_of_dvd _ (index_dvd_of_le hPA) with h | h
  · exact index_eq_one.mp h
  · have hr := relIndex_mul_index hPA
    rw [h] at hr
    have hrel : P.relIndex A = 1 := by nlinarith [hP.pos]
    exact (hAP (relIndex_eq_one.mp hrel)).elim

/-- A Y-member escapes the actual stabilizer of V₂ inside Aut(VX). -/
theorem member_image_not_le_plane_stabilizer [Finite G]
    {H T V₂ E X : Subgroup G} (hX : X ∈ YFamily H T V₂ E)
    (hV₂ : Nat.card V₂ = 4) (hVW : V₂ ≤ movedSpace V₂ X) :
    ¬ (conjugation X (movedSpace V₂ X) (member_normalizes_movedSpace V₂ X)).range ≤
      MulAction.stabilizer (MulAut (movedSpace V₂ X))
        (V₂.subgroupOf (movedSpace V₂ X)) := by
  intro h
  apply member_not_normalizes_plane hX hV₂
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hm := h ⟨⟨x,hx⟩,rfl⟩
  have he := (mem_automorphism_stabilizer_iff _ _).mp hm ⟨v,hVW hv⟩
  have hmemb := he.mpr hv
  change (conjugation X (movedSpace V₂ X) (member_normalizes_movedSpace V₂ X)
    ⟨x,hx⟩ ⟨v,hVW hv⟩ : G) ∈ V₂ at hmemb
  simpa only [conjugation_apply] using hmemb

/-- Order 24 identifies the I₂ image with the literal hyperplane stabilizer.
Its maximality has prime-index seven; no conjugacy or model tag replaces the action. -/
theorem I₂_image_eq_plane_stabilizer [Finite G]
    {H T V₂ E X I₂ : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) (hV₂ : Nat.card V₂ = 4)
    (hVW : V₂ ≤ movedSpace V₂ X) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hIP : I₂ ≤ normalizer (V₂ : Set G))
    (hIW : I₂ ≤ normalizer (movedSpace V₂ X : Set G))
    (himage : Nat.card (conjugation I₂ (movedSpace V₂ X) hIW).range = 24) :
    (conjugation I₂ (movedSpace V₂ X) hIW).range =
        MulAction.stabilizer (MulAut (movedSpace V₂ X))
          (V₂.subgroupOf (movedSpace V₂ X)) ∧
      IsCoatom (conjugation I₂ (movedSpace V₂ X) hIW).range := by
  let W := movedSpace V₂ X
  let P := (conjugation I₂ W hIW).range
  let S := MulAction.stabilizer (MulAut W) (V₂.subgroupOf W)
  have hPS : P ≤ S := by
    rintro a ⟨i,rfl⟩
    rw [mem_automorphism_stabilizer_iff]
    intro w
    change (conjugation I₂ W hIW i w : G) ∈ V₂ ↔ (w : G) ∈ V₂
    rw [conjugation_apply]
    exact (mem_normalizer_iff.mp (hIP i.property) w).symm
  have hi : P.index = 7 := by
    have hc := P.card_mul_index
    rw [himage,card_mulAut_of_elementary_eight W hX.2.1] at hc
    omega
  have hprime : Nat.Prime P.index := hi ▸ (by decide : Nat.Prime 7)
  have hp : IsCoatom P := by
    constructor
    · intro he
      exact hprime.ne_one (by rw [he,index_top])
    · intro Q hQ
      exact eq_top_of_prime_index P Q hprime hQ.le (not_le_of_gt hQ)
  refine ⟨?_,hp⟩
  by_contra hne
  have he : S = ⊤ := hp.2 S (lt_of_le_of_ne hPS hne)
  have hn := member_image_not_le_plane_stabilizer hX hV₂ hVW
  apply hn
  change (conjugation X W (member_normalizes_movedSpace V₂ X)).range ≤ S
  rw [he]
  exact le_top

/-- Enlarge the literal I₂ image using a Y-family member. The only image
calculation required is order 24 for I₂; X escaping the plane is proved. -/
theorem localJoin_action_surjective_of_I₂_image [Finite G]
    {H T V₂ E X I₂ L₂ U : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) (hV₂ : Nat.card V₂ = 4)
    (hVW : V₂ ≤ movedSpace V₂ X) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ T)
    (hIP : I₂ ≤ normalizer (V₂ : Set G))
    (hIW : I₂ ≤ normalizer (movedSpace V₂ X : Set G))
    (hAW : localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G))
    (himage : Nat.card (conjugation I₂ (movedSpace V₂ X) hIW).range = 24) :
    Function.Surjective (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hAW) := by
  let W := movedSpace V₂ X
  let P := (conjugation I₂ W hIW).range
  let A := (conjugation (localJoin L₂ X ⊔ T) W hAW).range
  have hIA : I₂ ≤ localJoin L₂ X ⊔ T := by
    rw [hI]
    exact sup_le (le_sup_left.trans le_sup_left) (hUT.trans le_sup_right)
  have hPA : P ≤ A := action_range_mono hIW hAW hIA
  have hindex : P.index = 7 := by
    have hc := P.card_mul_index
    rw [himage, card_mulAut_of_elementary_eight W hX.2.1] at hc
    omega
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_prime_index P A (hindex ▸ (by decide : Nat.Prime 7)) hPA
  intro hAP
  have hXP : X ≤ normalizer (V₂ : Set G) :=
    normalizes_of_action_range_le (member_normalizes_movedSpace V₂ X) hIW hVW hIP
      ((action_range_mono _ hAW (le_sup_right.trans le_sup_left)).trans hAP)
  exact member_not_normalizes_plane hX hV₂ hXP

private theorem elementaryEight_twoPerfect {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8) : IsPPerfect 2 (MulAut W) := by
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hW
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect (MulAut W) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (MulAut W ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (MulAut W ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (MulAut W ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (MulAut W ⧸ N) inferInstance

/-- The residual calculation concerns LX itself, not I₂. -/
theorem localJoin_twoResidual {H T L₂ X : Subgroup G}
    (hL₂ : twoResidual L₂ = L₂) (hX : ThreeExtension H T X) :
    twoResidual (localJoin L₂ X) = localJoin L₂ X := by
  apply le_antisymm (map_subtype_le _)
  exact sup_le
    (hL₂.ge.trans (embedded_pResidual_mono 2 (show L₂ ≤ localJoin L₂ X from le_sup_left)))
    (hX.residual_eq.ge.trans (embedded_pResidual_mono 2 (show X ≤ localJoin L₂ X from le_sup_right)))

/-- Adjoining T cannot account for any missing part of the full perfect
image. Thus LX itself induces all automorphisms whenever LXT does. -/
theorem localJoin_action_surjective_of_join_T [Finite G]
    {H T V₂ E X L₂ : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hL₂ : twoResidual L₂ = L₂) (hTL₂ : T ≤ normalizer (L₂ : Set G))
    (hT : IsPGroup 2 T)
    (hAW : localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G))
    (hsurj : Function.Surjective
      (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hAW)) :
    Function.Surjective (conjugation (localJoin L₂ X) (movedSpace V₂ X)
      (le_sup_left.trans hAW)) := by
  let A := localJoin L₂ X ⊔ T
  let L := localJoin L₂ X
  let f := conjugation A (movedSpace V₂ X) hAW
  have hnorm : T ≤ normalizer (L : Set G) :=
    (le_inf hTL₂ hX.1.T_normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup L₂ X)
  have hr : (pResidual 2 A).map A.subtype = L :=
    embedded_pResidual_join_pGroup L T
      (isPPerfect_of_twoResidual_eq (localJoin_twoResidual hL₂ hX.1)) hT hnorm
  have hi : pResidual 2 A = L.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hr, map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left)]
  have hm : (L.subgroupOf A).map f = ⊤ := by
    rw [← hi, map_pResidual_of_surjective 2 f hsurj,
      (pResidual_eq_top_iff 2 _).mpr (elementaryEight_twoPerfect hX.2.1)]
  intro a
  obtain ⟨l,hl,he⟩ := show a ∈ (L.subgroupOf A).map f by rw [hm]; trivial
  refine ⟨⟨l,hl⟩,?_⟩
  have hr := DFunLike.congr_fun
    (conjugation_restrict (le_sup_left.trans hAW) hAW le_sup_left) (⟨l,hl⟩ : L)
  exact hr.symm.trans he


private theorem elementaryEight_core_eq_bot {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8) : pCore 2 (MulAut W) = ⊥ := by
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hW
  apply ((pCore 2 (MulAut W)).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso, Matrix.PSL3Two.pCore_two_PSL_eq_bot]

private theorem core_le_action_kernel {A W : Type*} [Group A] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8)
    (f : A →* MulAut W) (hf : Function.Surjective f) : pCore 2 A ≤ f.ker := by
  have hn : ((pCore 2 A).map f).Normal := Normal.map inferInstance f hf
  have hi : (pCore 2 A).map f ≤ pCore 2 (MulAut W) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  rw [elementaryEight_core_eq_bot hW] at hi
  intro a ha
  exact hi (mem_map_of_mem f ha)

/-- A full action on the eight-group and a PSL₃(2) core quotient identify
the kernel, without assuming the centralizer equals the core. -/
theorem kernel_eq_core_of_full_action_and_quotient
    {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8)
    (f : A →* MulAut W) (hf : Function.Surjective f)
    (e : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL) : f.ker = pCore 2 A := by
  have hi : (pCore 2 A).index = 168 := by
    rw [index_eq_card, Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL]
  have hk : f.ker.index = 168 := by
    rw [index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      card_mulAut_of_elementary_eight W hW]
  apply Eq.symm
  apply eq_of_le_of_card_ge (core_le_action_kernel hW f hf)
  have hc := (pCore 2 A).card_mul_index
  have hd := f.ker.card_mul_index
  rw [hi] at hc
  rw [hk] at hd
  omega

private theorem join_kernel_isPGroup {D : Type*} [Group D]
    (L T : Subgroup G) (hn : T ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (f : (L ⊔ T : Subgroup G) →* D)
    (hk : (f.comp (inclusion le_sup_left)).ker = pCore 2 L) : IsPGroup 2 f.ker := by
  let A := L ⊔ T
  let N := L.subgroupOf A
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer hn)
  have hgen : N ⊔ T.subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (A ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (T.subgroupOf A) hT.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (A.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      exact hk.le x.val.property
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

/-- The component quotient also determines the whole LXT action kernel.
The additional kernel is an extension of two-groups through LXT/LX. -/
theorem localJoin_join_T_action_kernel [Finite G]
    {H T V₂ E X L₂ : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hL₂ : twoResidual L₂ = L₂) (hTL₂ : T ≤ normalizer (L₂ : Set G))
    (hT : IsPGroup 2 T)
    (hAW : localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G))
    (hsurj : Function.Surjective
      (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hAW))
    (e : coreQuotient (localJoin L₂ X) ≃* Matrix.PSL3Two.PSL) :
    (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hAW).ker =
      pCore 2 (localJoin L₂ X ⊔ T : Subgroup G) := by
  have hsurjL := localJoin_action_surjective_of_join_T hX hL₂ hTL₂ hT hAW hsurj
  have hkL := kernel_eq_core_of_full_action_and_quotient hX.2.1 _ hsurjL e
  have hn : T ≤ normalizer (localJoin L₂ X : Set G) :=
    (le_inf hTL₂ hX.1.T_normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup L₂ X)
  apply le_antisymm _ (core_le_action_kernel hX.2.1 _ hsurj)
  apply le_sSup
  refine ⟨inferInstance,join_kernel_isPGroup (localJoin L₂ X) T hn hT _ ?_⟩
  rw [conjugation_restrict]
  exact hkL

/-- The equivalence induced by the literal conjugation map. -/
noncomputable def coreConjugationEquiv (A W : Subgroup G)
    (hn : A ≤ normalizer (W : Set G))
    (hs : Function.Surjective (conjugation A W hn))
    (hk : (conjugation A W hn).ker = pCore 2 A) : coreQuotient A ≃* MulAut W :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (conjugation A W hn) hs)

theorem coreConjugationEquiv_mk (A W : Subgroup G)
    (hn : A ≤ normalizer (W : Set G))
    (hs : Function.Surjective (conjugation A W hn))
    (hk : (conjugation A W hn).ker = pCore 2 A) (a : A) :
    coreConjugationEquiv A W hn hs hk (QuotientGroup.mk' (pCore 2 A) a) =
      conjugation A W hn a := by rfl

/-- Attach actual binary matrix coordinates to the action-induced quotient;
the displayed equation retains the literal conjugation convention. -/
theorem coreConjugation_GL_coordinates [Finite G] (A W : Subgroup G)
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8)
    (hn : A ≤ normalizer (W : Set G))
    (hs : Function.Surjective (conjugation A W hn))
    (hk : (conjugation A W hn).ker = pCore 2 A) :
    ∃ e : MulAut W ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      ∃ q : coreQuotient A ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
        ∀ a : A, q (QuotientGroup.mk' (pCore 2 A) a) = e (conjugation A W hn a) := by
  obtain ⟨e⟩ := elementaryEight_mulAut_equiv_GL W hW
  exact ⟨e,(coreConjugationEquiv A W hn hs hk).trans e,fun _ => rfl⟩

/-- A source-facing assembly of the image and kernel deductions. The remaining
premises are the extraspecial I₂ image calculation and the selected-component
quotient; neither is asserted by this conditional theorem. -/
theorem action_and_quotient_of_I₂_image_and_component [Finite G]
    {H T V₂ E X I₂ L₂ U : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) (hV₂ : Nat.card V₂ = 4)
    (hVW : V₂ ≤ movedSpace V₂ X) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hTV₂ : T ≤ normalizer (V₂ : Set G))
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ T)
    (hIP : I₂ ≤ normalizer (V₂ : Set G))
    (hIW : I₂ ≤ normalizer (movedSpace V₂ X : Set G))
    (himage : Nat.card (conjugation I₂ (movedSpace V₂ X) hIW).range = 24)
    (hL₂ : twoResidual L₂ = L₂) (hTL₂ : T ≤ normalizer (L₂ : Set G))
    (hT : IsPGroup 2 T)
    (eL : coreQuotient (localJoin L₂ X) ≃* Matrix.PSL3Two.PSL) :
    ∃ hn : localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G),
      Function.Surjective (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hn) ∧
      Function.Surjective (conjugation (localJoin L₂ X) (movedSpace V₂ X)
        (le_sup_left.trans hn)) ∧
      (conjugation (localJoin L₂ X) (movedSpace V₂ X) (le_sup_left.trans hn)).ker =
        pCore 2 (localJoin L₂ X) ∧
      (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hn).ker =
        pCore 2 (localJoin L₂ X ⊔ T : Subgroup G) ∧
      ∃ q : coreQuotient (localJoin L₂ X ⊔ T) ≃* Matrix.PSL3Two.PSL,
        ∃ e : MulAut (movedSpace V₂ X) ≃* Matrix.PSL3Two.PSL,
          ∀ a : (localJoin L₂ X ⊔ T : Subgroup G),
            q (QuotientGroup.mk' (pCore 2 (localJoin L₂ X ⊔ T : Subgroup G)) a) =
              e (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hn a) := by
  have hn := localJoin_normalizes_movedSpace hX.1 hTV₂ hI hUT hIW
  have hs := localJoin_action_surjective_of_I₂_image hX hV₂ hVW hI hUT hIP hIW hn himage
  have hsL := localJoin_action_surjective_of_join_T hX hL₂ hTL₂ hT hn hs
  have hkL := kernel_eq_core_of_full_action_and_quotient hX.2.1 _ hsL eL
  have hk := localJoin_join_T_action_kernel hX hL₂ hTL₂ hT hn hs eL
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hX.2.1
  exact ⟨hn,hs,hsL,hkL,hk,(coreConjugationEquiv _ _ hn hs hk).trans e,e,fun _ => rfl⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
