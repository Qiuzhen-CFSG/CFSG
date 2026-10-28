module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NineIrreducible
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
public import Theory.Representation.RepEquiv
public import Theory.Representation.Quotient
public import Theory.ElementaryAbelian.Injective
/-!
# Irreducibility on the original local-action image

The literal quotient by the local module centralizer identifies with its
conjugation image. An explicit equivariant linear equivalence transports
the normal nine-core and its full moved space to that quotient, where the
original component irreducibility theorem applies. Pulling back removes
any additional irreducibility premise from the full-orbit E9 branch.

Source: Aschbacher–Smith 15.1.2, printed pp.1085–1086.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
set_option synthInstance.maxSize 10000
set_option backward.isDefEq.respectTransparency false

theorem source_localAction_nine_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (P : Subgroup D) [P.Normal] [IsElementaryAbelian 3 P], Nat.card P = 9 →
      Module.finrank (ZMod 2) (Additive V) = 4 →
      subspaceCommutator ρ ⊤ P = ⊤ → IsIrreducible ρ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let hVM := localModule_le T hM.1.2
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let U := V.subgroupOf M
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hVM).toMonoidHom (subgroupOfEquivOfLe hVM).injective
  let := (localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩).normal
  dsimp only
  intro P hPn hPe hP hdim hm
  have hk : f.ker = centralizer (U : Set M) := by
    rw [show f.ker = (centralizer (V : Set G)).subgroupOf M from actionHom_ker M V _]
    ext m
    constructor
    · intro hm v hv
      exact Subtype.ext (hm v hv)
    · intro hm v hv
      exact congrArg M.subtype (hm ⟨v,hVM hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let σ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let gU := subgroupOfEquivOfLe hVM
  let x : Additive U ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective
    (gU.toMonoidHom.toAdditive.toZModLinearMap 2) gU.bijective
  have he (m : M) : e (q m) = f.rangeRestrict m := by
    dsimp [e,q]
    rfl
  have hx (a : M ⧸ centralizer (U : Set M)) (v : Additive U) :
      x (σ a v) = ρ (e a) (x v) := by
    obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective _ a
    rw [he]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg M.subtype (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m v)
  let P0 := P.comap e.toMonoidHom
  let : P0.Normal := Subgroup.Normal.comap hPn e.toMonoidHom
  let : IsElementaryAbelian 3 P0 := IsElementaryAbelian.comap_of_injective _ e.injective P
  have hmap : P0.map e.toMonoidHom = P := map_comap_eq_self_of_surjective e.surjective P
  have hc0 : Nat.card P0 = 9 := (card_map_of_injective e.injective).symm.trans (hmap ▸ hP)
  have hm0 : subspaceCommutator σ ⊤ P0 = ⊤ := by
    have h := subspaceCommutator_map_embedding σ ρ e.toMonoidHom x.symm.toLinearMap
      (fun g v => by
        apply x.injective
        change x (σ g (x.symm v)) = x (x.symm (ρ (e g) v))
        rw [hx,x.apply_symm_apply,x.apply_symm_apply]) P0 ⊤
    rw [Submodule.map_top,LinearEquiv.range,hmap,hm,Submodule.map_top,LinearEquiv.range] at h
    exact h
  have hi := source_nine_extension_irreducible hG T hempty hM hJ hu hne U P0 hc0
    (x.finrank_eq.trans hdim) hm0 ⊤ le_top
  rw [top_sup_eq] at hi
  have hiσ : IsIrreducible σ := (irreducible_comp_surjective_iff
    (⊤ : Subgroup _).subtype (by intro a; exact ⟨⟨a,mem_top a⟩,rfl⟩) σ).mp hi
  let z : (ρ.comp e.toMonoidHom) ≃ₗ σ := {
    toLinearEquiv := x.symm
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro v
      apply x.injective
      change x (x.symm (ρ (e a) v)) = x (σ a (x.symm v))
      rw [hx,x.apply_symm_apply,x.apply_symm_apply] }
  have hiz : IsIrreducible (ρ.comp e.toMonoidHom) := RepEquiv.irreducible_of_euqiv z hiσ
  exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective ρ).mp hiz
end CFSG.Quasithin.Chapter15.Section01
