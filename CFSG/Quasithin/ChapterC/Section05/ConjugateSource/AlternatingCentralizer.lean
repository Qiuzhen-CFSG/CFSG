module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCore
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.FirstCohomologyProjective
public import Theory.Representation.FirstCohomologyAutomorphism
/-!
# Splitting the full module centralizer in the alternating-five case

The marked natural module is projective, so its first cohomology vanishes.
The actual automorphism displacement on K/U is therefore principal. Every
module fixer in N_G(K) is a product of a module element and a centralizer
of K. The proved equality N_R(U)=N_R(K) gives C_R(U)=U C_R(K), including
when R interchanges the two original blocks.

Source: Aschbacher–Smith, C.1.13(c) and C.5.6(7), printed pp.125 and159.
-/

public section
open Subgroup BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
private theorem automorphism_quotient_fixed (N : Subgroup K) (α : MulAut K)
    (hfix : ∀ n ∈ N, α n = n) (hNn : N.Normal) (hC : centralizer (N : Set K) = N)
    (f : K →* alternatingGroup (Fin 5)) (hk : f.ker = N) : ∀ g, f (α g) = f g := by
  intro g
  have hd : (α g)⁻¹ * g ∈ centralizer (N : Set K) := by
    intro n hn
    have hconj := hfix (g*n*g⁻¹) (hNn.conj_mem n hn g)
    rw [map_mul,map_mul,map_inv,hfix n hn] at hconj
    calc
      n * ((α g)⁻¹ * g) = (α g)⁻¹ * (α g * n * (α g)⁻¹) * g := by group
      _ = (α g)⁻¹ * (g * n * g⁻¹) * g := by rw [hconj]
      _ = ((α g)⁻¹ * g) * n := by group
  have hd' : f ((α g)⁻¹ * g) = 1 := by
    change (α g)⁻¹ * g ∈ f.ker
    rw [hk,← hC]
    exact hd
  rw [map_mul,map_inv,inv_mul_eq_one] at hd'
  exact hd'

theorem AlternatingPairSetup.automorphism_fixing_module_inner
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (α : MulAut K) (hfix : ∀ u ∈ blockU K, α u = u) :
    ∃ u : blockU K, ∀ k, α k = (u : K)⁻¹ * k * u := by
  let N := K ⊔ ChapterB.baumann R
  let a := h.action.comp (inclusion (show K ≤ N from le_sup_left))
  have hrange : a.range = alternatingGroup (Fin 5) := by
    calc
      a.range = (K.subgroupOf N).map h.action := by
        ext p
        constructor
        · rintro ⟨k,rfl⟩
          exact ⟨inclusion le_sup_left k,k.property,rfl⟩
        · rintro ⟨n,hn,rfl⟩
          exact ⟨⟨n,hn⟩,rfl⟩
      _ = alternatingGroup (Fin 5) := h.block_image
  let f : K →* alternatingGroup (Fin 5) := a.codRestrict _ (fun k => hrange ▸ show a k ∈ a.range from ⟨k,rfl⟩)
  have hf : Function.Surjective f := by
    intro p
    have hp : (p : Equiv.Perm (Fin 5)) ∈ a.range := hrange.symm ▸ p.property
    obtain ⟨k,hk⟩ := hp
    exact ⟨k,Subtype.ext hk⟩
  have hk : f.ker = blockU K := by
    rw [← h.block_core_eq_module x hx hnc,← h.block.2.1.centralizer_blockU]
    ext k
    change f k = 1 ↔ k ∈ centralizer (blockU K : Set K)
    rw [Subtype.ext_iff]
    change h.action (inclusion le_sup_left k) = 1 ↔ k ∈ centralizer (blockU K : Set K)
    change inclusion le_sup_left k ∈ h.action.ker ↔ _
    rw [h.action_kernel]
    constructor
    · intro hc u hu
      apply Subtype.ext
      exact hc u (mem_map_of_mem K.subtype hu)
    · intro hc u hu
      obtain ⟨v,hv,rfl⟩ := hu
      exact congrArg Subtype.val (hc v hv)
  let e : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans h.coordinates
  have heval (w : Multiplicative (BinaryPermutation.core (Fin 5))) :
      ((e.symm w : blockU K) : K) = (⟨(h.coordinates.symm w : G),
        (map_subtype_le (blockU K)) (h.coordinates.symm w).property⟩ : K) := by
    have hh : (blockU K).equivMapOfInjective K.subtype K.subtype_injective (e.symm w) =
        h.coordinates.symm w := h.coordinates.injective
      ((e.apply_symm_apply w).trans (h.coordinates.apply_symm_apply w).symm)
    exact Subtype.ext (congrArg (fun n : sourceModule K => (n : G)) hh)
  let ρ := alternatingCoreRepresentation (Fin 5)
  have he (k : K) (v : BinaryPermutation.core (Fin 5)) :
      (e.symm (Multiplicative.ofAdd (ρ (f k) v)) : K) =
        k * (e.symm (Multiplicative.ofAdd v) : K) * k⁻¹ := by
    apply Subtype.ext
    have heq := h.equivariant (inclusion le_sup_left k) (h.coordinates.symm (Multiplicative.ofAdd v))
    rw [heval,heval]
    rw [MulEquiv.apply_symm_apply] at heq
    exact heq

  let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5))) ρ.asModule :=
    alternatingFive_core_projective
  let : Subsingleton (Representation.OneCohomology.H1 ρ) :=
    Representation.OneCohomology.subsingleton_H1_of_projective ρ
  have hC : centralizer (blockU K : Set K) = blockU K :=
    h.block.2.1.centralizer_blockU.trans (h.block_core_eq_module x hx hnc)
  exact Representation.OneCohomology.automorphism_inner_of_H1_zero (blockU K) f hf hk e ρ he α
    (automorphism_quotient_fixed (blockU K) α hfix inferInstance hC f hk) hfix

theorem AlternatingPairSetup.module_fixer_eq_module_centralizer
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    normalizer (K : Set G) ⊓ centralizer (sourceModule K : Set G) =
      sourceModule K ⊔ centralizer (K : Set G) := by
  have hUK : sourceModule K ≤ K := map_subtype_le _
  let : IsElementaryAbelian 2 (sourceModule K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  apply le_antisymm
  · rintro g ⟨hgK,hgU⟩
    let α := K.normalizerMonoidHom ⟨g,hgK⟩
    have hfix : ∀ u ∈ blockU K, α u = u := by
      intro u hu
      apply Subtype.ext
      change g * (u : G) * g⁻¹ = (u : G)
      rw [← hgU u (mem_map_of_mem K.subtype hu),mul_inv_cancel_right]
    obtain ⟨u,hu⟩ := h.automorphism_fixing_module_inner x hx hnc α hfix
    let n : G := (u : K)
    have hn : n ∈ sourceModule K := mem_map_of_mem K.subtype u.property
    have hng : n * g ∈ centralizer (K : Set G) := by
      intro k hk
      have he := congrArg (fun z : K => (z : G)) (hu ⟨k,hk⟩)
      change g * k * g⁻¹ = n⁻¹ * k * n at he
      calc
        k * (n*g) = n * (n⁻¹ * k * n) * g := by group
        _ = n * (g*k*g⁻¹) * g := by rw [he]
        _ = (n*g) * k := by group
    have hm := (sourceModule K ⊔ centralizer (K : Set G)).mul_mem
      (mem_sup_left ((sourceModule K).inv_mem hn)) (mem_sup_right hng)
    simpa only [inv_mul_cancel_left] using hm
  · apply sup_le
    · exact le_inf (hUK.trans K.le_normalizer) (le_centralizer _)
    · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hUK)

theorem AlternatingPairSetup.centralizer_in_normalizing_subgroup
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (P : Subgroup G) (hUP : sourceModule K ≤ P) (hPK : P ≤ normalizer (K : Set G)) :
    P ⊓ centralizer (sourceModule K : Set G) = sourceModule K ⊔ (P ⊓ centralizer (K : Set G)) := by
  have hUK : sourceModule K ≤ K := map_subtype_le _
  let : IsElementaryAbelian 2 (sourceModule K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  apply le_antisymm
  · rintro g ⟨hgP,hgU⟩
    have hg : g ∈ sourceModule K ⊔ centralizer (K : Set G) :=
      (h.module_fixer_eq_module_centralizer x hx hnc).le ⟨hPK hgP,hgU⟩
    have hm : g ∈ (sourceModule K : Set G) * (centralizer (K : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        ((centralizer_le hUK).trans (Subgroup.centralizer_le_normalizer _))]
      exact hg
    obtain ⟨u,hu,c,hc,rfl⟩ := hm
    have hcP : c ∈ P := by simpa using P.mul_mem (P.inv_mem (hUP hu)) hgP
    exact mul_mem_sup hu ⟨hcP,hc⟩
  · exact sup_le (le_inf hUP (le_centralizer _))
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le hUK)))

theorem AlternatingPairSetup.full_module_centralizer
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    R ⊓ centralizer (sourceModule K : Set G) = sourceModule K ⊔ (R ⊓ centralizer (K : Set G)) := by
  let P := R ⊓ normalizer (K : Set G)
  have hUP : sourceModule K ≤ P :=
    le_inf (h.module_le.trans inf_le_left) ((map_subtype_le _).trans K.le_normalizer)
  have hcP : R ⊓ centralizer (sourceModule K : Set G) ≤ P :=
    (inf_le_inf_left R (Subgroup.centralizer_le_normalizer _)).trans_eq
      h.block_normalizer_eq_module_normalizer.symm
  have hi : P ⊓ centralizer (sourceModule K : Set G) = R ⊓ centralizer (sourceModule K : Set G) :=
    le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf hcP inf_le_right)
  have hj : P ⊓ centralizer (K : Set G) = R ⊓ centralizer (K : Set G) := by
    dsimp only [P]
    rw [inf_assoc,inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)]
  rw [← hi]
  exact (h.centralizer_in_normalizing_subgroup x hx hnc P hUP inf_le_right).trans
    (congrArg (fun C => sourceModule K ⊔ C) hj)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
