module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryAction
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryRatio
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# The actual whole secondary product and its cubic bound

Multiplication of the original disjoint commuting U and V_Y gives coordinates
on their whole join. The original centralizer quotient identifies with the
full hexacode actor, with its complete core kernel retained. The proved
source3.1.8 bound therefore transfers to the full product of the chosen
six-space and the constructed secondary S6 action, in the same marking.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes

private theorem product_coordinates {H : Type*} [Group H]
    (A B J : Subgroup H) [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 J]
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set H)) (hs : A ⊔ B = J)
    (c : A ≃* Multiplicative hexacode) :
    ∃ e : (hexacode × Additive B) ≃ₗ[ZMod 2] Additive J,
      ∀ a b, ((e ((c a).toAdd,Additive.ofMul b)).toMul : H) = (a : H) * b := by
  obtain ⟨m,hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let n : Multiplicative hexacode × B ≃* J :=
    (c.symm.prodCongr (MulEquiv.refl B)).trans (m.trans (MulEquiv.subgroupCongr hs))
  let d : (hexacode × Additive B) ≃+ Additive J := {
    toFun w := Additive.ofMul (n (Multiplicative.ofAdd w.1,w.2.toMul))
    invFun w := ((n.symm w.toMul).1.toAdd,Additive.ofMul (n.symm w.toMul).2)
    left_inv w := congrArg (fun y : Multiplicative hexacode × B =>
      (y.1.toAdd,Additive.ofMul y.2)) (n.symm_apply_apply _)
    right_inv w := congrArg Additive.ofMul (n.apply_symm_apply w.toMul)
    map_add' w v := congrArg Additive.ofMul (n.map_mul _ _) }
  let e := LinearEquiv.ofBijective (d.toAddMonoidHom.toZModLinearMap 2) d.bijective
  refine ⟨e,?_⟩
  intro a b
  change (m (c.symm (c a),b) : H) = _
  rw [c.symm_apply_apply]
  exact hm a b

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Compare the actual whole U V_Y with the native product, retaining the
original coordinate marking and all scalar/core kernels; transport the
already proved source ratio without assuming a new numerical premise. -/
theorem original_tripleSix_central_closure_secondary_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    let J := (U ⊔ V).subgroupOf M
    ∃ (hr : IsPReduced 2 (V.subgroupOf M)) (hj : IsPReduced 2 J),
      letI := hr.elementary
      letI := hj.elementary
      ∃ (hMU : M ≤ normalizer (U : Set G)) (f : Automizer U →* HexAutomorphisms),
        Function.Bijective f ∧
        (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩) =
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
        (∀ (b : Automizer U) (u : U),
          (tripleSixPointCoordinates D a (b.val u)).toAdd =
            Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
        (let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
         let q := hexCoordinateSixHom.comp π
         Function.Surjective π ∧ π.ker = pCore 2 M ∧ Function.Surjective q ∧
         q.ker = (X.subgroupOf M) ⊔ pCore 2 M ∧
         ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (V.subgroupOf M)),
           (∀ (m : M) (v : Additive (V.subgroupOf M)),
             ((σ (q m) v).toMul : M) = m * (v.toMul : M) * m⁻¹) ∧
           (∃ e : (hexacode × Additive (V.subgroupOf M)) ≃ₗ[ZMod 2] Additive J,
             ∀ (u : U) (v : V.subgroupOf M),
               (((e ((tripleSixPointCoordinates D a u).toAdd,Additive.ofMul v)).toMul : M) : G) =
                 (u : G) * (v : M)) ∧
           cubicRatio (Hexacode.action.prod (σ.comp hexCoordinateSixHom)) ≤ 2) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  let J := (U ⊔ V).subgroupOf M
  obtain ⟨hr,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hσ⟩ :=
    original_tripleSix_central_closure_secondary_action h structural D a z hz hzT hnot houter
  let := hr.elementary
  obtain ⟨hj,hbound⟩ := original_tripleSix_central_closure_secondary_cubicRatio
    h structural D a z hz hzT hnot houter
  let := hj.elementary
  let := hj.normal
  let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
  let q := hexCoordinateSixHom.comp π
  let τ := Hexacode.action.prod (σ.comp hexCoordinateSixHom)
  have hs := original_tripleSix_central_closure_scalar_fixed_module h structural D a z hz hzT hnot houter
  have hVM : V ≤ M := hs.2.2.1.trans (inf_le_left.trans (pCoreIn_le 2 M))
  have hUM : U ≤ M := D.le_component.trans le_sup_left
  let A := U.subgroupOf M
  let B := V.subgroupOf M
  have hAB : A ⊔ B = J := (subgroupOf_sup hUM hVM).symm
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    ext x
    change ((x : G) ∈ U ∧ (x : G) ∈ V) ↔ x = 1
    constructor
    · intro hx
      have hx' : (x:G) ∈ U ⊓ V := hx
      rw [hs.2.2.2.2.2.2.1.eq_bot] at hx'
      exact Subtype.ext hx'
    · intro hx
      subst x
      exact ⟨U.one_mem,V.one_mem⟩
  have hc : A ≤ centralizer (B : Set M) := by
    intro u hu v hv
    apply Subtype.ext
    exact (le_centralizer_iff.mp D.core_centralizes hu) v (hs.2.2.1 hv).1
  let c : A ≃* Multiplicative hexacode :=
    (subgroupOfEquivOfLe hUM).trans (tripleSixPointCoordinates D a)
  obtain ⟨e,he⟩ := product_coordinates A B J hd hc hAB c
  have heG (u : U) (v : B) :
      (((e ((tripleSixPointCoordinates D a u).toAdd,Additive.ofMul v)).toMul : M) : G) =
        (u : G) * (v : M) :=
    congrArg M.subtype (he ⟨⟨u,hUM u.property⟩,u.property⟩ v)
  have heA (u : U) (v : Additive B) :
      (((e ((tripleSixPointCoordinates D a u).toAdd,v)).toMul : M) : G) =
        (u : G) * (v.toMul : M) := heG u v.toMul
  have hcentral : centralizer (J : Set M) = pCore 2 M := by
    apply le_antisymm
    · intro x hx
      have hxu : (x:G) ∈ centralizer (U : Set G) := by
        intro u hu
        exact congrArg M.subtype (hx ⟨u,hUM hu⟩ (show (⟨u,hUM hu⟩ : M) ∈ J from mem_sup_left hu))
      have hQ := (original_tripleSix_action_kernel h structural D a).1 ⟨x.property,hxu⟩
      obtain ⟨y,hy,heq⟩ := hQ
      exact (show y=x from Subtype.ext heq) ▸ hy
    · exact le_centralizer_iff.mp hj.le_centralizer_pCore
  let N := centralizer (J : Set M)
  let p := QuotientGroup.mk' N
  let ρ := NormalElementaryQuotient.representation J p
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let d : (M ⧸ N) ≃* HexAutomorphisms :=
    (QuotientGroup.quotientMulEquivOfEq (hcentral.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hdπ (m : M) : d (p m) = π m := rfl
  have hequiv (g : M ⧸ N) (w : Additive J) : e.symm (ρ g w) = τ (d g) (e.symm w) := by
    obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨w,rfl⟩ := e.surjective w
    obtain ⟨u,hu⟩ := (tripleSixPointCoordinates D a).surjective (Multiplicative.ofAdd w.1)
    have hu' : (tripleSixPointCoordinates D a u).toAdd = w.1 := hu
    have hw : w = ((tripleSixPointCoordinates D a u).toAdd,w.2) := by rw [hu']
    rw [hw,e.symm_apply_apply,hdπ]
    apply e.injective
    rw [e.apply_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have hrep := NormalElementaryQuotient.representation_apply J p
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m
      (e ((tripleSixPointCoordinates D a u).toAdd,w.2))
    have hσm := congrArg M.subtype (hσ m w.2)
    change (((σ (q m) w.2).toMul : M) : G) =
      (m:G) * (w.2.toMul:M) * (m:G)⁻¹ at hσm
    have hrepG := congrArg M.subtype hrep
    change (((ρ (p m) (e ((tripleSixPointCoordinates D a u).toAdd,w.2))).toMul : M) : G) =
      (m:G) * (((e ((tripleSixPointCoordinates D a u).toAdd,w.2)).toMul : M) : G) * (m:G)⁻¹ at hrepG
    let b := U.normalizerMonoidHom.rangeRestrict ⟨m,hMU m.property⟩
    have hcm := hchart b u
    change (tripleSixPointCoordinates D a (b.val u)).toAdd =
      Hexacode.action (π m) (tripleSixPointCoordinates D a u).toAdd at hcm
    change (((ρ (p m) (e ((tripleSixPointCoordinates D a u).toAdd,w.2))).toMul : M) : G) =
      (((e (Hexacode.action (π m) (tripleSixPointCoordinates D a u).toAdd,
        σ (q m) w.2)).toMul : M) : G)
    rw [hrepG,heA,←hcm,heA,hσm]
    change (m:G) * ((u:G)*(w.2.toMul:M)) * (m:G)⁻¹ =
      ((m:G)*(u:G)*(m:G)⁻¹) * ((m:G)*(w.2.toMul:M)*(m:G)⁻¹)
    group
  have hb : cubicRatio τ ≤ 2 := cubicRatio_le_nat_of_equivariant ρ τ
    d.toMonoidHom d.injective e.symm hequiv 2 hbound
  exact ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hσ,⟨e,heG⟩,hb⟩

end CFSG.Quasithin.Chapter12.Section07
