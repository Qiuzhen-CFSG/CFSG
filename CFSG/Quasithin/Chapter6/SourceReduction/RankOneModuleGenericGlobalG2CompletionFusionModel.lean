module
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy
import all Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Involution reduction through the actual G₂ local maps

The six-root coordinate reduction uses only unipotent conjugations and the
simple Weyl reflections, with both ends of each step in the common Sylow.
Thus two homomorphisms from the standard parabolics which agree on their
whole overlap carry that reduction into their target group. Split-torus
conjugation normalizes both root parameters to one. Every involution in the
common Sylow image is conjugate in that target to one of the two pinned roots.
No homomorphism from the entire G₂ model is assumed or constructed.

The internal import deliberately reuses the private numerical identities of
the existing involution reduction, while preserving its public boundary.
The new argument retains the local conjugators, which the model's root-class
existence theorem forgets. Its source consumer takes the target to be the
literal join of the original factors and combines this with marked nonfusion.

Source: Aschbacher–Smith F.4.30, F.4.35 and F.4.43, printed pp.290,292,296,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Coordinate identities reuse the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.EvenInvolutionGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionFusion
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem u1 : unipotent (K := F) ≤ parabolic₁ := le_sup_left.trans borel_le_parabolic₁
omit [CharP F 2] in
private theorem u2 : unipotent (K := F) ≤ parabolic₂ := le_sup_left.trans borel_le_parabolic₂
omit [CharP F 2] in
private theorem rootU (a : F) : rootA a ∈ unipotent ∧ rootB a ∈ unipotent ∧
    rootC a ∈ unipotent ∧ rootD a ∈ unipotent ∧ rootE a ∈ unipotent ∧ rootF a ∈ unipotent := by
  repeat' constructor
  all_goals exact subset_closure (by simp)

section Reduction
variable (P : Model F → Prop)
  (hA : ∀ a : F, a ≠ 0 → P (rootA a))
  (hC : ∀ a : F, a ≠ 0 → P (rootC a))
  (hstep : ∀ g : Model F, g ∈ parabolic₁ ∨ g ∈ parabolic₂ →
    ∀ x ∈ unipotent, MulAut.conj g x ∈ unipotent →
      (P (MulAut.conj g x) ↔ P x))
include hstep
omit [CharP F 2] in
private theorem step (g : Model F) (hg : g ∈ parabolic₁ ∨ g ∈ parabolic₂)
    (t u : Fin 6 → F) (he : MulAut.conj g (unipotentProduct t) = unipotentProduct u) :
    P (unipotentProduct u) → P (unipotentProduct t) := by
  have hh := hstep g hg _ (unipotentProduct_mem t) (he.symm ▸ unipotentProduct_mem u)
  rw [he] at hh
  exact hh.mp

include hA hC in
private theorem ABC_reduction (a b c : F)
    (hne : unipotentProduct ![a,b,c,0,0,0] ≠ 1) :
    P (unipotentProduct ![a,b,c,0,0,0]) := by
  by_cases hc : c = 0
  · subst c
    by_cases hb : b = 0
    · subst b
      have ha : a ≠ 0 := by intro ha; subst a; simp [unipotentProduct] at hne
      simpa [unipotentProduct] using hA a ha
    · have he : MulAut.conj (rootE (a/b) * weylR) (rootA b) =
          unipotentProduct ![a,b,0,0,0,0] := by
        rw [map_mul,MulAut.mul_apply,show MulAut.conj weylR (rootA b) = rootB b from weylR_rootA b,
          ShortRootProducts.rootE_conjugate_rootB,div_mul_cancel₀ _ hb]
        simp [unipotentProduct]
      have hg : rootE (a/b)*weylR ∈ parabolic₂ :=
        parabolic₂.mul_mem (u2 (rootU (a/b)).2.2.2.2.1) weylR_mem_parabolic
      have hh := hstep _ (Or.inr hg) _ (rootU b).1 (he.symm ▸ unipotentProduct_mem _)
      exact he ▸ hh.mpr (hA b hb)
  · have he : MulAut.conj (rootF (b/c)*rootD (a/c)) (rootC c) =
          unipotentProduct ![a,b,c,0,0,0] := by
      rw [map_mul,MulAut.mul_apply]
      have hh : rootC c = unipotentProduct ![0,0,c,0,0,0] := by simp [unipotentProduct]
      rw [hh,conjugate_D,conjugate_F]
      simp [mul_div_cancel₀ _ hc]
    have hg : rootF (b/c)*rootD (a/c) ∈ parabolic₁ :=
      u1 (unipotent.mul_mem (rootU (b/c)).2.2.2.2.2 (rootU (a/c)).2.2.2.1)
    have hh := hstep _ (Or.inl hg) _ (rootU c).2.2.1 (he.symm ▸ unipotentProduct_mem _)
    exact he ▸ hh.mpr (hC c hc)

include hA hC in
private theorem nonzero_E_reduction [Finite F] (a b c d e : F) (he : e ≠ 0)
    (hsq : (unipotentProduct ![a,b,c,d,e,0])^2 = 1)
    (hne : unipotentProduct ![a,b,c,d,e,0] ≠ 1) :
    P (unipotentProduct ![a,b,c,d,e,0]) := by
  obtain ⟨z,hz⟩ := isSquare_of_charTwo' (c/e)
  have hz' : e*z^2 = c := by
    rw [pow_two, ← hz, mul_div_cancel₀ _ he]
  let a' := a+d^2*z+d*e*z^2+e^2*z^3
  let b' := b+c*z+d*z^2+e*z^3
  let d' := d+e*z
  have hconj : MulAut.conj (rootF z) (unipotentProduct ![a,b,c,d,e,0]) =
      unipotentProduct ![a',b',0,d',e,0] := by
    rw [conjugate_F, hz', CharTwo.add_self_eq_zero]
  have hsq' : (unipotentProduct ![a',b',0,d',e,0])^2 = 1 := by
    rw [← hconj, ← map_pow, hsq, map_one]
  have hb : b'=0 := by
    have hh := five_relation a' b' 0 d' e hsq'
    simpa using (mul_eq_zero.mp (by simpa using hh : b'*e=0)).resolve_right he
  have hw : MulAut.conj weylS (unipotentProduct ![a',b',0,d',e,0]) =
      unipotentProduct ![a',e,d',0,0,0] := by
    change weylS * _ * weylS⁻¹ = _
    rw [weylS_fiveRoot_conjugate _ rfl]
    simp [hb]
  apply step P hstep (rootF z) (Or.inl (u1 (rootU z).2.2.2.2.2)) _ _ hconj
  apply step P hstep weylS (Or.inl (mem_sup_right (subset_closure (by simp)))) _ _ hw
  apply ABC_reduction P hA hC hstep
  intro hh
  apply hne
  apply (MulAut.conj (rootF z)).injective
  apply (MulAut.conj weylS).injective
  simpa only [hconj, hw, map_one] using hh

include hA hC in
private theorem five_reduction [Finite F] (a b c d e : F)
    (hsq : (unipotentProduct ![a,b,c,d,e,0])^2 = 1)
    (hne : unipotentProduct ![a,b,c,d,e,0] ≠ 1) :
    P (unipotentProduct ![a,b,c,d,e,0]) := by
  by_cases he : e = 0
  · subst e
    have hcd : c*d = 0 := by simpa using five_relation a b c d 0 hsq
    rcases mul_eq_zero.mp hcd with hc | hd
    · subst c
      have hw : MulAut.conj weylS (unipotentProduct ![a,b,0,d,0,0]) =
          unipotentProduct ![a,0,d,0,b,0] := by
        change weylS * _ * weylS⁻¹ = _
        rw [weylS_fiveRoot_conjugate _ rfl]
        simp
      have hsq' : (unipotentProduct ![a,0,d,0,b,0])^2 = 1 := by
        rw [← hw, ← map_pow, hsq, map_one]
      have hne' : unipotentProduct ![a,0,d,0,b,0] ≠ 1 := by
        rw [← hw, MulEquiv.map_ne_one_iff]
        exact hne
      apply step P hstep weylS (Or.inl (mem_sup_right (subset_closure (by simp)))) _ _ hw
      by_cases hb : b=0
      · subst b
        exact ABC_reduction P hA hC hstep a 0 d hne'
      · exact nonzero_E_reduction P hA hC hstep a 0 d 0 b hb hsq' hne'
    · subst d
      exact ABC_reduction P hA hC hstep a b c hne
  · exact nonzero_E_reduction P hA hC hstep a b c d e he hsq hne


include hA hC in
private theorem unipotent_reduction [Finite F] (t : Fin 6 → F)
    (hsq : (unipotentProduct t)^2 = 1) (hne : unipotentProduct t ≠ 1) :
    P (unipotentProduct t) := by
  have ht : t = ![t 0,t 1,t 2,t 3,t 4,t 5] := by ext i; fin_cases i <;> rfl
  by_cases hf : t 5 = 0
  · rw [ht] at hsq hne ⊢
    simp only [hf] at hsq hne ⊢
    exact five_reduction P hA hC hstep _ _ _ _ _ hsq hne
  have hs := square_zero t hsq
  have hef : t 4 * t 5 = 0 := by simpa [square_parameters] using congrFun hs 3
  have he : t 4 = 0 := (mul_eq_zero.mp hef).resolve_right hf
  have hcf : (t 2 + t 3*t 5)*t 5 = 0 := by
    have hh := congrFun hs 1
    simp only [square_parameters, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.zero_apply, he, zero_mul, add_zero] at hh
    linear_combination hh
  have hc : t 2 = t 3*t 5 := by
    have hh := (mul_eq_zero.mp hcf).resolve_right hf
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  have hd : t 5 * (t 3 / t 5) = t 3 := by field_simp
  have hcc : (t 5)^2 * (t 3/t 5) = t 3*t 5 := by
    rw [pow_two, mul_assoc, hd, mul_comm]
  let a := t 0 + t 1*(t 3/t 5) + t 3*(t 5)^2*(t 3/t 5)
  let b := t 1 + (t 5)^3*(t 3/t 5)
  have hE : MulAut.conj (rootE (t 3/t 5)) (unipotentProduct t) =
      unipotentProduct ![a,b,0,0,0,t 5] := by
    rw [show unipotentProduct t = unipotentProduct ![t 0,t 1,t 2,t 3,t 4,t 5] from
      congrArg unipotentProduct ht, conjugate_E]
    simp only [he, zero_mul, add_zero, hd, hcc, hc, CharTwo.add_self_eq_zero]
    rfl
  have hR := conjugate_R_ABF a b (t 5)
  have hsq' : (unipotentProduct ![b,a,0,t 5,0,0])^2 = 1 := by
    rw [← hR, ← hE, ← map_pow, ← map_pow, hsq, map_one, map_one]
  have hne' : unipotentProduct ![b,a,0,t 5,0,0] ≠ 1 := by
    rw [← hR, ← hE, MulEquiv.map_ne_one_iff, MulEquiv.map_ne_one_iff]
    exact hne
  apply step P hstep (rootE (t 3/t 5)) (Or.inl (u1 (rootU _).2.2.2.2.1)) _ _ hE
  apply step P hstep weylR (Or.inr weylR_mem_parabolic) _ _ hR
  exact five_reduction P hA hC hstep _ _ _ _ _ hsq' hne'


end Reduction

/-- The pinned highest long root, in the short parabolic. -/
@[expose] def long (a : F) : parabolic₁ (F := F) := ⟨rootA a,by exact u1 (rootU a).1⟩
/-- The pinned short root used by the source nonfusion argument. -/
@[expose] def short (a : F) : parabolic₁ (F := F) := ⟨rootC a,by exact u1 (rootU a).2.2.1⟩

variable {G : Type*} [Group G]

omit [CharP F 2] in
private theorem map_local_conj (f : parabolic₁ (F := F) →* G)
    (g : Model F) (hg : g ∈ parabolic₁) (x y : Model F)
    (hx : x ∈ parabolic₁) (hy : y ∈ parabolic₁)
    (he : g*x*g⁻¹=y) : IsConj (f ⟨x,hx⟩) (f ⟨y,hy⟩) := by
  apply isConj_iff.mpr
  refine ⟨f ⟨g,hg⟩,?_⟩
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg f (Subtype.ext he)

omit [CharP F 2] in
private theorem long_conj_one (f : parabolic₁ (F := F) →* G)
    (a : F) (ha : a≠0) : IsConj (f (long 1)) (f (long a)) := by
  apply map_local_conj f (torus (Units.mk0 a ha) 1)
    (borel_le_parabolic₁ (mem_sup_right ⟨(Units.mk0 a ha,1),rfl⟩))
  simpa using torus_rootA (Units.mk0 a ha) 1 (1:F)

omit [CharP F 2] in
private theorem short_conj_one (f : parabolic₁ (F := F) →* G)
    (a : F) (ha : a≠0) : IsConj (f (short 1)) (f (short a)) := by
  apply map_local_conj f (torus (Units.mk0 a ha) 1)
    (borel_le_parabolic₁ (mem_sup_right ⟨(Units.mk0 a ha,1),rfl⟩))
  simpa using torus_rootC (Units.mk0 a ha) 1 (1:F)

/-- The two actual local maps, agreeing on the whole overlap, reduce every
involution in their common Sylow image to the pinned long or short root.
No map from the entire model, or recognition of G, is assumed. -/
theorem compatible_involution_classes [Finite F]
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (x : parabolic₁ (F := F)) (hx : x.val ∈ unipotent)
    (hsq : x^2=1) (hne : x≠1) :
    IsConj (f (long 1)) (f x) ∨ IsConj (f (short 1)) (f x) := by
  let P : Model F → Prop := fun z => ∀ hz : z ∈ parabolic₁,
    IsConj (f (long 1)) (f ⟨z,hz⟩) ∨ IsConj (f (short 1)) (f ⟨z,hz⟩)
  have hA : ∀ a : F, a≠0 → P (rootA a) := by
    intro a ha0 _
    exact Or.inl (long_conj_one f a ha0)
  have hC : ∀ a : F, a≠0 → P (rootC a) := by
    intro a ha0 _
    exact Or.inr (short_conj_one f a ha0)
  have hstep : ∀ g : Model F, g ∈ parabolic₁ ∨ g ∈ parabolic₂ →
      ∀ z ∈ unipotent, MulAut.conj g z ∈ unipotent →
        (P (MulAut.conj g z) ↔ P z) := by
    intro g hg z hz hgz
    have hc : IsConj (f ⟨z,u1 hz⟩) (f ⟨MulAut.conj g z,u1 hgz⟩) := by
      rcases hg with hg|hg
      · exact map_local_conj f g hg z _ (u1 hz) (u1 hgz) rfl
      · rw [ha z (u1 hz) (u2 hz),ha _ (u1 hgz) (u2 hgz)]
        apply isConj_iff.mpr
        refine ⟨l ⟨g,hg⟩,?_⟩
        rw [←map_inv,←map_mul,←map_mul]
        rfl
    constructor
    · intro hh _
      exact (hh (u1 hgz)).elim (fun h => Or.inl (h.trans hc.symm))
        (fun h => Or.inr (h.trans hc.symm))
    · intro hh _
      exact (hh (u1 hz)).elim (fun h => Or.inl (h.trans hc))
        (fun h => Or.inr (h.trans hc))
  rw [unipotent_eq_range] at hx
  obtain ⟨t,ht⟩ := hx
  have hs : (unipotentProduct t)^2=1 := by
    rw [ht]
    exact congrArg Subtype.val hsq
  have hn : unipotentProduct t≠1 := by
    rw [ht]
    exact fun hh => hne (Subtype.ext hh)
  have hh := unipotent_reduction P hA hC hstep t hs hn
  rw [ht] at hh
  exact hh x.property

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionFusion
