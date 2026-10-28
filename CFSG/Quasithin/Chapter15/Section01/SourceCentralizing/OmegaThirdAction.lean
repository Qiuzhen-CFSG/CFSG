module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import Theory.GroupTheory.SymmetricThreeImage
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.CoreQuotient
/-!
# The original third local has a symmetric-three action

In the full Omega row, A.5.3 places the centralizer of V(M) inside the
centralizer of V(N). The literal action on V(N) is consequently an image
of the order-twelve intersection action. Its two-core is trivial by the
source reduced-module theorem, and it is not a two-group because N≠Mc.
It therefore factors through, and is isomorphic to, the S₃ quotient of
the coordinate parabolic. The original subgroups and both action maps
are retained throughout.

Source: Aschbacher--Smith15.2.5, printed p.1108.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Subgroup
variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
private theorem symmetricThree_of_core_free_image
    (e : A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3))
    (f : A →* B) (hf : Function.Surjective f)
    (hb : pCore 2 B = ⊥) (hn : ¬ IsPGroup 2 B) :
    Nonempty (B ≃* Equiv.Perm (Fin 3)) := by
  have hk : pCore 2 A ≤ f.ker := by
    have hi : (pCore 2 A).map f ≤ pCore 2 B :=
      le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
    rw [hb] at hi
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hi)
  let g := QuotientGroup.lift (pCore 2 A) f hk
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a,rfl⟩
  let q : g.range ≃* B := MulEquiv.ofBijective g.range.subtype
    ⟨Subtype.val_injective,by
      intro b
      obtain ⟨a,rfl⟩ := hg b
      exact ⟨⟨g a,⟨a,rfl⟩⟩,rfl⟩⟩
  obtain ⟨j⟩ := symmetricThree_image_of_not_isPGroup e g
    (fun hp => hn (hp.of_equiv q))
  exact ⟨q.symm.trans j⟩
end Subgroup
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
private theorem maximal_local_action_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    pCore 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) = ⊥ := by
  let V := localModule T N
  let f := actionHom N V (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  have hred := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let := hred.normal
  have hk : f.ker = centralizer (V.subgroupOf N : Set N) := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf N from actionHom_ker N _ _]
    ext n
    constructor
    · intro hn v hv
      exact Subtype.ext (hn v hv)
    · intro hn v hv
      exact congrArg N.subtype (hn ⟨v,localModule_le T hN.2 hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change pCore 2 f.range = ⊥
  rw [←pCore_map_iso 2 e,hred.quotient_pCore_eq_bot,Subgroup.map_bot]

private theorem maximal_local_action_not_twoGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc) :
    ¬ IsPGroup 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) := by
  let f := (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict
  intro hp
  have hcore := maximal_local_action_twoCore hG T hN
  have ht : (⊤ : Subgroup (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) ≤ pCore 2 _ :=
    le_sSup ⟨inferInstance,hp.of_injective (⊤ : Subgroup _).subtype (Subgroup.subtype_injective _)⟩
  have hi (x : N) : f x = 1 := ht.trans hcore.le (mem_top _)
  have hle : N ≤ Mc := by
    intro x hx
    have hh : (⟨x,hx⟩ : N) ∈ (actionHom N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := congrArg Subtype.val (hi ⟨x,hx⟩)
    have hc : (⟨x,hx⟩ : N) ∈ (centralizer (localModule T N : Set G)).subgroupOf N :=
      (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) ▸ hh
    exact localModule_centralizer_le_partner T N hu hc
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact hne (le_antisymm hle (hN.1.2 hMc.1.1 hle))

/-- A third local in the full Omega row has its own literal action S₃. -/
theorem PreparedChosenModule.omega_full_third_action_symmetricThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (UniqueFactor.imageRepresentation M V hV.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    Nonempty (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃*
      Equiv.Perm (Fin 3)) := by
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let H := (M ⊓ N).subgroupOf M
  let A := H.map f
  let P := (T.subtype hM.1.2).mapSurjective
    (f := f) (actionHom M V hV.normalized).rangeRestrict_surjective
  obtain ⟨_,hnot,hproper⟩ := hV.third_maximal_action_constraints
    hG T hempty hM hJ hu hN hNM hNMc
  have hPA : (P : Subgroup D) < A := by
    refine lt_of_le_of_ne (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))) ?_
    intro he
    have hh : IsPGroup 2 A := by rw [←he]; exact P.isPGroup'
    exact hnot hh
  obtain ⟨e⟩ := SymmetricThreeProduct.intermediate_core_quotient ho.2.2.2.1.some P A hPA hproper
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hCN : M ⊓ centralizer (V : Set G) ≤
      N ⊓ centralizer (localModule T N : Set G) := by
    rw [hfull]
    exact (lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)
  let Dn := internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  let g : N →* Dn :=
    (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict
  let i : H →* N := (M.subtype.comp H.subtype).codRestrict N (fun x => x.property.2)
  let j := f.subgroupMap H
  let k := g.comp i
  have hk : Function.Surjective k := by
    intro d
    obtain ⟨n,hn⟩ := (actionHom N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict_surjective d
    change g n = d at hn
    obtain ⟨a,ha,b,hb,he⟩ := hord n n.property
    have haH : (⟨a,ha.2⟩ : M) ∈ H := ⟨ha.2,ha.1⟩
    have hbker : (⟨b,hb.1⟩ : N) ∈
        (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := by
      exact (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).symm ▸ hb.2
    have hgb : g ⟨b,hb.1⟩ = 1 := by
      apply Subtype.ext
      exact hbker
    refine ⟨⟨⟨a,ha.2⟩,haH⟩,?_⟩
    have hnprod : n = (⟨a,ha.1⟩ : N) * ⟨b,hb.1⟩ := Subtype.ext he.symm
    rw [hnprod,map_mul,hgb,mul_one] at hn
    exact hn
  have hker : j.ker ≤ k.ker := by
    intro x hx
    have hfx : f (x : M) = 1 := congrArg Subtype.val hx
    have hxker : (x : M) ∈ (actionHom M V hV.normalized).ker := congrArg Subtype.val hfx
    rw [actionHom_ker] at hxker
    have hxc := (hCN ⟨(x : M).property,hxker⟩).2
    have hxg : i x ∈ (actionHom N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := by
      exact (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).symm ▸ hxc
    apply Subtype.ext
    exact hxg
  let q : A →* Dn := j.liftOfSurjective (f.subgroupMap_surjective H) ⟨k,hker⟩
  have hq : Function.Surjective q := by
    intro d
    obtain ⟨x,rfl⟩ := hk d
    exact ⟨j x,by simp [q]⟩
  exact Subgroup.symmetricThree_of_core_free_image e q hq
    (maximal_local_action_twoCore hG T hN) (maximal_local_action_not_twoGroup hG T hN hu hNMc)

end CFSG.Quasithin.Chapter15.Section01
