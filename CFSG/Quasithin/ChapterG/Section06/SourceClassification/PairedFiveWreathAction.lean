module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.PairedFiveSpaceDisjoint
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Theory.Representation.BinaryPermutation.FivePairWreath

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open BinaryPermutation BinaryPermutation.FivePair BinaryPermutation.FiveCentralExtension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-!
# The paired S₅ action in the literal two-core wreath model

Two exchanged S₅ factors have disjoint moved spaces, so their sum identifies the
ambient module with two copies of the alternating-five core.  The factor models
then identify the normalizer action with the literal two-core wreath action.
The resulting homomorphism is injective by faithfulness of the original action.

Source: Aschbacher–Smith G.6.4(3)(ii), pp.345–346.
-/

/-- The paired S₅ factors admit a faithful coordinatewise wreath action. -/
theorem TwoFactors.exists_paired_five_wreath_action
    [Finite G]
    (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hf : Function.Injective ρ) :
    ∃ (c : V ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core))
      (q : G →* FivePair.Wreath) (e : G ≃* FivePair.Wreath),
      Function.Injective q ∧ Function.Surjective q ∧
      (∀ z : FiveCentralExtension.Sym × FiveCentralExtension.Sym, ∃ x : G, q x = FivePair.base z) ∧
      (∀ g v, c (ρ g v) = FivePair.wreathRepresentation (e g) (c v)) := by
  classical
  let U₁ := subspaceCommutator ρ ⊤ d.first
  let U₂ := subspaceCommutator ρ ⊤ d.second
  have hcompl : IsCompl U₁ U₂ := d.paired_five_spaces_isCompl h₁
  obtain ⟨e₁, E₁, hs₁, he₁⟩ := h₁
  obtain ⟨e₂, E₂, hs₂, he₂⟩ := h₂
  let p : (U₁ × U₂) ≃ₗ[ZMod 2] V := Submodule.prodEquivOfIsCompl U₁ U₂ hcompl
  let z : FivePair.Core ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let F₁ : U₁ ≃ₗ[ZMod 2] FivePair.Core := E₁.trans z.symm
  let F₂ : U₂ ≃ₗ[ZMod 2] FivePair.Core := E₂.trans z.symm
  let c : V ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core) :=
    p.symm.trans (F₁.prodCongr F₂)
  obtain ⟨ep, hep⟩ := d.exists_paired_five_product_equiv
  let es : (d.first × d.second) ≃* (Sym × Sym) :=
    e₁.prodCongr e₂
  let ek : (normalClosure ({a} : Set G)) ≃* (Sym × Sym) :=
    ep.symm.trans es
  let j : (Sym × Sym) →* G :=
    (normalClosure ({a} : Set G)).subtype.comp ek.symm.toMonoidHom
  let σ : Representation (ZMod 2) G (FivePair.Core × FivePair.Core) :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  have hσ (g : G) (v : FivePair.Core × FivePair.Core) :
      σ g v = c (ρ g (c.symm v)) := rfl
  have hc₁ (u : U₁) : c (u : V) = (F₁ u, 0) := by
    simp only [c, LinearEquiv.trans_apply]
    change (F₁.prodCongr F₂) ((Submodule.prodEquivOfIsCompl U₁ U₂ hcompl).symm (u : V)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left U₁ U₂ hcompl u]
    simp [F₁, F₂]
  have hc₂ (u : U₂) : c (u : V) = (0, F₂ u) := by
    simp only [c, LinearEquiv.trans_apply]
    change (F₁.prodCongr F₂) ((Submodule.prodEquivOfIsCompl U₁ U₂ hcompl).symm (u : V)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right U₁ U₂ hcompl u]
    simp [F₁, F₂]
  have hF₁ (k : d.first) (u : U₁) :
      F₁ ⟨ρ k (u : V), hs₁ k u⟩ = BinaryPermutation.coreRepresentation (Fin 5) (e₁ k) (F₁ u) := by
    simp only [F₁, LinearEquiv.trans_apply]
    rw [he₁]
    apply z.injective
    simp only [z, LinearEquiv.apply_symm_apply]
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    rw [z.apply_symm_apply]
  have hF₂ (k : d.second) (u : U₂) :
      F₂ ⟨ρ k (u : V), hs₂ k u⟩ = BinaryPermutation.coreRepresentation (Fin 5) (e₂ k) (F₂ u) := by
    simp only [F₂, LinearEquiv.trans_apply]
    rw [he₂]
    apply z.injective
    simp only [z, LinearEquiv.apply_symm_apply]
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    rw [z.apply_symm_apply]
  have hactor (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) :
      σ (j g) v = FivePair.action g v := by
    obtain ⟨⟨u₁, u₂⟩, hv⟩ := (F₁.prodCongr F₂).surjective v
    rw [← hv]
    have hk : ek.symm g = ep (e₁.symm g.1, e₂.symm g.2) := by
      change ep (es.symm g) = ep (e₁.symm g.1, e₂.symm g.2)
      congr 1
    have hja : (j g : G) = (e₁.symm g.1 : G) * (e₂.symm g.2 : G) := by
      change ((ek.symm g : normalClosure ({a} : Set G)) : G) = _
      rw [hk]
      exact hep _ _
    have hu₁ : ρ (j g) (u₁ : V) = ρ (e₁.symm g.1) (u₁ : V) := by
      rw [hja, map_mul, Module.End.mul_apply]
      have hz : ρ (e₂.symm g.2) (u₁ : V) = (u₁ : V) := by
        apply sub_eq_zero.mp
        apply d.cross_second.le
        exact Submodule.subset_span ⟨e₂.symm g.2, (e₂.symm g.2).property, u₁, u₁.property, rfl⟩
      rw [hz]
    have hu₂ : ρ (j g) (u₂ : V) = ρ (e₂.symm g.2) (u₂ : V) := by
      rw [hja, map_mul, Module.End.mul_apply]
      have hz : ρ (e₁.symm g.1) (ρ (e₂.symm g.2) (u₂ : V)) =
          ρ (e₂.symm g.2) (u₂ : V) := by
        apply sub_eq_zero.mp
        apply d.cross_first.le
        exact Submodule.subset_span ⟨e₁.symm g.1, (e₁.symm g.1).property,
          ρ (e₂.symm g.2) (u₂ : V), hs₂ (e₂.symm g.2) u₂,
          rfl⟩
      rw [hz]
    have hcv : c.symm (F₁ u₁, F₂ u₂) = p (u₁, u₂) := by simp [c]
    change σ (j g) (F₁ u₁, F₂ u₂) = _
    rw [hσ, hcv]
    rw [show (p (u₁, u₂) : V) = (u₁ : V) + (u₂ : V) by rfl]
    rw [map_add, hu₁, hu₂]
    have hu₁' : ρ (e₁.symm g.1) (u₁ : V) ∈ U₁ := hs₁ _ u₁
    have hu₂' : ρ (e₂.symm g.2) (u₂ : V) ∈ U₂ := hs₂ _ u₂
    rw [map_add]
    rw [show c (ρ (e₁.symm g.1) (u₁ : V)) =
      c (⟨ρ (e₁.symm g.1) (u₁ : V), hu₁'⟩ : U₁) by rfl]
    rw [show c (ρ (e₂.symm g.2) (u₂ : V)) =
      c (⟨ρ (e₂.symm g.2) (u₂ : V), hu₂'⟩ : U₂) by rfl]
    rw [hc₁, hc₂, hF₁, hF₂]
    simp
  let K := normalClosure ({a} : Set G)
  have hfirst_le : d.first ≤ K := by
    change d.first ≤ normalClosure ({a} : Set G)
    rw [← d.join_eq]
    exact le_sup_left
  have haxis₁ : ((⊤ : Subgroup Sym).prod ⊥).map ek.symm.toMonoidHom =
      d.first.subgroupOf K := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hfirst_le]
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g = (g.1, 1) := Prod.ext rfl (Subgroup.mem_bot.mp hg.2)
      rw [hg']
      change ((ek.symm (g.1, 1) : K) : G) ∈ d.first
      change ((ep (e₁.symm g.1, e₂.symm 1) : K) : G) ∈ d.first
      rw [hep]
      simp
    · intro hx
      let k : d.first := ⟨x, hx⟩
      refine ⟨(e₁ k, 1), ?_, ?_⟩
      · change e₁ k ∈ (⊤ : Subgroup Sym) ∧ (1 : Sym) ∈ (⊥ : Subgroup Sym)
        simp
      · change (K.subtype.comp ek.symm.toMonoidHom) (e₁ k, 1) = x
        rw [MonoidHom.comp_apply]
        change ((ek.symm (e₁ k, 1) : K) : G) = x
        change ((ep (es.symm (e₁ k, (1 : Sym))) : K) : G) = x
        have hes : es.symm (e₁ k, (1 : Sym)) = (k, (1 : d.second)) := by
          change (e₁.symm (e₁ k), e₂.symm (1 : Sym)) = _
          simp
        rw [hes, hep]
        simp [k]
  have hsecond_le : d.second ≤ K := by
    change d.second ≤ normalClosure ({a} : Set G)
    rw [← d.join_eq]
    exact le_sup_right
  have haxis₂ : ((⊥ : Subgroup Sym).prod ⊤).map ek.symm.toMonoidHom =
      d.second.subgroupOf K := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hsecond_le]
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g = (1, g.2) := Prod.ext (Subgroup.mem_bot.mp hg.1) rfl
      rw [hg']
      change ((ek.symm (1, g.2) : K) : G) ∈ d.second
      change ((ep (e₁.symm 1, e₂.symm g.2) : K) : G) ∈ d.second
      rw [hep]
      simp
    · intro hx
      let k : d.second := ⟨x, hx⟩
      refine ⟨(1, e₂ k), ?_, ?_⟩
      · change (1 : Sym) ∈ (⊥ : Subgroup Sym) ∧ e₂ k ∈ (⊤ : Subgroup Sym)
        simp
      · change (K.subtype.comp ek.symm.toMonoidHom) (1, e₂ k) = x
        rw [MonoidHom.comp_apply]
        change ((ek.symm (1, e₂ k) : K) : G) = x
        change ((ep (es.symm ((1 : Sym), e₂ k)) : K) : G) = x
        have hes : es.symm ((1 : Sym), e₂ k) = ((1 : d.first), k) := by
          change (e₁.symm (1 : Sym), e₂.symm (e₂ k)) = _
          simp
        rw [hes, hep]
        simp [k]
  have hexw (x : G) : ∃ w : FivePair.Wreath, FivePair.wreathToLinear w =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom (σ.asGroupHom x) := by
    let r : (FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core) :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _ (σ.asGroupHom x)
    let ψ : MulAut (normalClosure ({a} : Set G)) := MulAut.conjNormal x
    let φ : MulAut (Sym × Sym) := ek.symm.trans (ψ.trans ek)
    have hact (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) :
        r (FivePair.action g v) = FivePair.action (φ g) (r v) := by
      have he (g : Sym × Sym) : (j (φ g) : G) = x * (j g : G) * x⁻¹ := by
        change ((ek.symm (ek (ψ (ek.symm g))) : normalClosure ({a} : Set G)) : G) = _
        rw [ek.symm_apply_apply]
        rfl
      have hr (w : FivePair.Core × FivePair.Core) : r w = σ x w := rfl
      rw [hr, hr, ← hactor g v, ← hactor (φ g) (σ x v)]
      change (σ x) ((σ (j g)) v) = (σ (j (φ g))) ((σ x) v)
      rw [he]
      simp only [map_mul, Module.End.mul_apply, σ.inv_self_apply]
    have hmap (A : Subgroup (Sym × Sym)) :
        (A.map φ.toMonoidHom).map ek.symm.toMonoidHom =
          (A.map ek.symm.toMonoidHom).map ψ.toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro g
      change ek.symm (φ g) = ψ (ek.symm g)
      simp [φ]
    apply FivePair.normalizer_wreath r φ hact
    have hcompψ : K.subtype.comp ψ.toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp K.subtype := by
      apply MonoidHom.ext
      intro z
      rfl
    rcases d.permutation x with h | h
    · left
      constructor <;>
        apply Subgroup.map_injective (f := ek.symm.toMonoidHom) ek.symm.injective
      · rw [hmap]
        rw [haxis₁]
        apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
        rw [map_map, hcompψ, ← map_map, map_subgroupOf_eq_of_le hfirst_le]
        exact h.1
      · rw [hmap]
        rw [haxis₂]
        apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
        rw [map_map, hcompψ, ← map_map, map_subgroupOf_eq_of_le hsecond_le]
        exact h.2
    · right
      constructor <;>
        apply Subgroup.map_injective (f := ek.symm.toMonoidHom) ek.symm.injective
      · rw [hmap]
        rw [haxis₁, haxis₂]
        apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
        rw [map_map, hcompψ, ← map_map, map_subgroupOf_eq_of_le hfirst_le,
          map_subgroupOf_eq_of_le hsecond_le]
        exact h.1
      · rw [hmap]
        rw [haxis₂, haxis₁]
        apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
        rw [map_map, hcompψ, ← map_map, map_subgroupOf_eq_of_le hsecond_le,
          map_subgroupOf_eq_of_le hfirst_le]
        exact h.2
  let R : G →* ((FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (FivePair.Core × FivePair.Core)).toMonoidHom.comp σ.asGroupHom
  have hchoose (x : G) :
      FivePair.wreathToLinear (Classical.choose (hexw x)) = R x := by
    exact Classical.choose_spec (hexw x)
  let q : G →* FivePair.Wreath :=
    { toFun := fun x => Classical.choose (hexw x)
      map_one' := by
        apply FivePair.wreathToLinear_injective
        calc
          FivePair.wreathToLinear (Classical.choose (hexw 1)) = R 1 := hchoose 1
          _ = FivePair.wreathToLinear (1 : FivePair.Wreath) := by
            rw [R.map_one, map_one]
      map_mul' := by
        intro x y
        apply FivePair.wreathToLinear_injective
        calc
          FivePair.wreathToLinear (Classical.choose (hexw (x * y))) = R (x * y) := hchoose (x * y)
          _ = R x * R y := R.map_mul x y
          _ = FivePair.wreathToLinear (Classical.choose (hexw x)) *
              FivePair.wreathToLinear (Classical.choose (hexw y)) := by rw [hchoose x, hchoose y]
          _ = FivePair.wreathToLinear (Classical.choose (hexw x) *
              Classical.choose (hexw y)) := by rw [map_mul] }
  have hq (x : G) :
      FivePair.wreathToLinear (q x) =
        LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (FivePair.Core × FivePair.Core) (σ.asGroupHom x) :=
    hchoose x
  have hqinj : Function.Injective q := by
    intro x y hxy
    have hL : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (FivePair.Core × FivePair.Core)) (σ.asGroupHom x) =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (FivePair.Core × FivePair.Core)) (σ.asGroupHom y) := by
      rw [← hq x, hxy, hq y]
    have hσgrp : σ.asGroupHom x = σ.asGroupHom y := by
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (FivePair.Core × FivePair.Core)).injective
      exact hL
    have hσlin : σ x = σ y := congrArg Units.val hσgrp
    have hρlin : ρ x = ρ y := by
      apply c.conjRingEquiv.injective
      change c.conjRingEquiv (ρ x) = c.conjRingEquiv (ρ y) at hσlin
      exact hσlin
    exact hf hρlin
  have hbase : ∀ z : Sym × Sym, ∃ x : G, q x = FivePair.base z := by
    intro z
    refine ⟨j z, ?_⟩
    apply FivePair.wreathToLinear_injective
    apply LinearEquiv.ext
    intro v
    rw [hq]
    change σ (j z) v = _
    rw [hactor]
    exact (FivePair.wreathToLinear_base z v).symm
  have hinter (g : G) (v : V) :
      c (ρ g v) = FivePair.wreathRepresentation (q g) (c v) := by
    have hs := hσ g (c v)
    simp only [LinearEquiv.symm_apply_apply] at hs
    rw [← hs]
    change (σ g) (c v) = FivePair.wreathToLinear (q g) (c v)
    rw [hq g]
    rfl
  obtain ⟨t, htne, _, _, htmap⟩ := d.extension
  have hU : U₁.map (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) V (ρ.asGroupHom t)).toLinearMap = U₂ := by
    change U₁.map (ρ t) = U₂
    rw [moved_map_conjugate, htmap]
  have htex : (q t).right ≠ 1 := by
    intro hright
    have hUeq (u : U₁) : c (ρ t (u : V)) =
        (BinaryPermutation.coreRepresentation (Fin 5)
          ((q t).left 1) (F₁ u), 0) := by
      rw [hinter]
      rw [hc₁]
      simp [FivePair.wreathRepresentation_apply, hright]
    have hU1ne : U₁ ≠ ⊥ := by
      intro h
      have hd : Module.finrank (ZMod 2) U₁ =
          Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 5)) := E₁.finrank_eq
      rw [h, finrank_bot, BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)] at hd
      norm_num at hd
    let _ : Nontrivial U₁ := Submodule.nontrivial_iff_ne_bot.mpr hU1ne
    obtain ⟨u, hu⟩ := exists_ne (0 : U₁)
    have huV : (u : V) ≠ 0 := by
      intro hz
      exact hu (Subtype.ext hz)
    have hut : ρ t (u : V) ∈ U₂ := by
      rw [← hU]
      exact ⟨u, u.property, rfl⟩
    have hcU2 := hc₂ ⟨ρ t (u : V), hut⟩
    have hz := hUeq u
    rw [show c (ρ t (u : V)) = c (⟨ρ t (u : V), hut⟩ : U₂) by rfl,
      hcU2] at hz
    have hfirst := congrArg Prod.fst hz
    have hF : F₁ u = 0 := by
      apply (FivePair.coreActionEquiv ((q t).left 1)).injective
      simpa [FivePair.coreActionEquiv] using hfirst.symm
    have hu0 : u = 0 := F₁.injective (by simpa using hF)
    exact hu (Subtype.ext (congrArg Subtype.val hu0))
  have hqsurj : Function.Surjective q :=
    FivePair.range_eq_top_of_base_and_exchange q hbase ⟨t, htex⟩
  let e : G ≃* FivePair.Wreath := MulEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  refine ⟨c, q, e, hqinj, hqsurj, hbase, ?_⟩
  intro g v
  change c (ρ g v) = FivePair.wreathToLinear (q g) (c v)
  have hs := hσ g (c v)
  simp only [LinearEquiv.symm_apply_apply] at hs
  rw [← hs, hq g]
  rfl
end CFSG.Quasithin.ChapterG.Section06
