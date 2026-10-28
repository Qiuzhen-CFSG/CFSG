module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.KernelBound
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
public import Theory.GroupTheory.GeneralizedFitting.JointCoreDetection
public import Theory.GroupTheory.PCoreCentralKernelTransfer

/-!
# Motion on the odd endpoint closure

Use the literal normalizer action of KT on U=⟨V^(KT)⟩. The proved kernel
bound on K remains central modulo O₂(K) after passing to the faithful action
image and removing its two-core. The residual of KT is K; its perfectness
puts the quotient center inside its Frattini subgroup. Residual Frattini
kernel detection then puts every centralizing two-subgroup inside O₂(KT).
Transporting by the same left conjugation as the critical endpoint proves
nontrivial [V,Uᵍ] from the already established core escape.

Only the preceding relative component and rank-one quotient are explicit:
qt-d-1222-natural-relative-components and qt-d-1222-natural-flag-cartan supply
them. This result uses neither an OddPair nor a transvection hypothesis.
The amalgam owner applies it to the actual normalized endpoint and retains
the remaining Sp₄ core-intersection argument.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Two-subgroups centralizing the literal KT-closure lie in O₂(KT).
The normalizer action, its faithful image and the quotient by its two-core
are all constructed here; no odd-pair or motion premise is used. -/
theorem centralizing_two_subgroup_le_core (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (A : Subgroup G) (hAH : A ≤ KT E) (hA : IsPGroup 2 A)
    (hcent : A ≤ centralizer (localClosure E : Set G)) : A ≤ (KT E).pCoreIn 2 := by
  let H := KT E
  let U := localClosure E
  let hn : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V H
  let ρ := U.normalizerMonoidHom.comp (inclusion hn)
  let r := ρ.rangeRestrict
  let f := (QuotientGroup.mk' (pCore 2 ρ.range)).comp r
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp ρ.rangeRestrict_surjective
  have hrker (a : H) (ha : r a = 1) : (a : G) ∈ centralizer (U : Set G) := by
    have hz : inclusion hn a ∈ U.normalizerMonoidHom.ker := congrArg Subtype.val ha
    rwa [normalizerMonoidHom_ker] at hz
  let j : E.K →* H := inclusion le_sup_left
  let u := r.comp j
  have hu : u.rangeRestrict.ker ≤ (center (E.K ⧸ pCore 2 E.K)).comap
      (QuotientGroup.mk' (pCore 2 E.K)) := by
    rw [MonoidHom.ker_rangeRestrict]
    intro k hk
    obtain ⟨k',hk',he⟩ := Chief.K_centralizer_le_two_center_of_rank_one E h hK hlt hlocal
      ⟨k.property,hrker (j k) hk⟩
    exact (show k' = k from Subtype.ext he) ▸ hk'
  have huCore : pCore 2 E.K ≤ (pCore 2 u.range).comap u.rangeRestrict :=
    map_le_iff_le_comap.mp (le_sSup ⟨Normal.map inferInstance _ u.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩)
  have hz := u.rangeRestrict.coreMap_ker_le_center_of_map_ker
    u.rangeRestrict_surjective huCore (map_le_iff_le_comap.mpr hu)
  have hkK (k : E.K) (hk : f (j k) = 1) :
      QuotientGroup.mk' (pCore 2 E.K) k ∈ center (E.K ⧸ pCore 2 E.K) := by
    apply hz
    apply (QuotientGroup.eq_one_iff _).mpr
    have hm : u k ∈ pCore 2 ρ.range := (QuotientGroup.eq_one_iff _).mp hk
    exact (show (pCore 2 ρ.range).comap u.range.subtype ≤ pCore 2 u.range from
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective _ u.range.subtype_injective⟩) hm
  let N := E.K.subgroupOf H
  let e : N ≃* E.K := subgroupOfEquivOfLe (show E.K ≤ H from le_sup_left)
  have hres : pResidual 2 H = N := by
    apply map_injective H.subtype_injective
    rw [residual_KT E h,map_subgroupOf_eq_of_le (show E.K ≤ H from le_sup_left)]
  let : N.Normal := hres ▸ inferInstance
  let : Group.IsPerfect (⊤ : Subgroup E.K) := (Chief.Models.component_top E hK).perfect
  let : Group.IsPerfect E.K := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup E.K) ≃* E.K).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hquot : IsPGroup 2 (H ⧸ N) := (isPGroup_quotient_pResidual (G := H) 2).of_equiv
    (QuotientGroup.quotientMulEquivOfEq hres)
  let eQ := QuotientGroup.congr (pCore 2 N) (pCore 2 E.K) e (pCore_map_iso 2 e)
  have hk : N ⊓ f.ker ≤ ((center (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype := by
    rintro a ⟨ha,haf⟩
    let n : N := ⟨a,ha⟩
    refine ⟨n,?_,rfl⟩
    exact (centerCongr eQ.symm ⟨QuotientGroup.mk' (pCore 2 E.K) (e n),hkK (e n) haf⟩).property
  have hkill : pCore 2 H ≤ f.ker := by
    intro a ha
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show (pCore 2 H).map r ≤ pCore 2 ρ.range from
      le_sSup ⟨Normal.map inferInstance _ ρ.rangeRestrict_surjective,pCore_isPGroup.map _⟩)
      (mem_map_of_mem r ha)
  have hAf : A.subgroupOf H ≤ f.ker := by
    intro a ha
    have hz : inclusion hn a ∈ U.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hcent ha
    have hr : r a = 1 := Subtype.ext hz
    change QuotientGroup.mk' (pCore 2 ρ.range) (r a) = 1
    rw [hr,map_one]
  have hc := two_subgroup_le_core_of_central_residual_kernel N hquot f hf hkill hk
    (A.subgroupOf H) hA.comap_subtype hAf
  have hm := map_mono (f := H.subtype) hc
  rwa [map_subgroupOf_eq_of_le hAH] at hm

/-- Conjugation transports the centralizer criterion to the actual endpoint.
Critical escape therefore forces nontrivial action on Uᵍ. -/
theorem moves_closure_of_escape (g : G) (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hV : V ≤ (KT E).map (MulAut.conj g).toMonoidHom)
    (hescape : ¬ V ≤ ((KT E).map (MulAut.conj g).toMonoidHom).pCoreIn 2) :
    ⁅V,(localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  let c := (MulAut.conj g).symm
  have hcancel (B : Subgroup G) : (B.map (MulAut.conj g).toMonoidHom).map c.toMonoidHom = B := by
    rw [map_map]
    have hid : c.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    rw [hid,map_id]
  have hAH : V.map c.toMonoidHom ≤ KT E := by
    simpa only [hcancel] using map_mono (f := c.toMonoidHom) hV
  intro hzero
  have hzero' := congrArg (map c.toMonoidHom) hzero
  rw [map_commutator,hcancel,Subgroup.map_bot] at hzero'
  let := D.elementary
  have hc := centralizing_two_subgroup_le_core E h hK hlt hlocal _ hAH
    ((IsElementaryAbelian.isPGroup 2 V).map c.toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mp hzero')
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hc
  rw [map_map,show (MulAut.conj g).toMonoidHom.comp c.toMonoidHom = MonoidHom.id G from
    by ext x; exact (MulAut.conj g).apply_symm_apply x,map_id,
    ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj g).injective] at hm
  exact hescape hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
