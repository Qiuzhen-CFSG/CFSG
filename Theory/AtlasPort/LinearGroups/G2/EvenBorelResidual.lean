module

public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus

/-!
# Two-perfectness of the even G₂ Borel

Each positive root character takes every nonzero field value on the split
torus. A nonidentity value makes torus commutators exhaust the root group.
The odd-order torus lies in the two-residual, so all six root groups do too.
Thus the Borel is two-perfect for q > 2, including q = 4.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The root and torus
formulas are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.EvenBorelTorus
open Subgroup
open scoped commutatorElement
variable {F : Type*} [Field F]

private theorem root_mem_normal (N : Subgroup (borel (K := F))) [N.Normal]
    (X : F → Model F) (hadd : ∀ a b, X a * X b = X (a+b))
    (hzero : X 0 = 1) (hmem : ∀ a, X a ∈ borel)
    (d : borel (K := F)) (hd : d ∈ N) (c : F) (hc : c ≠ 1)
    (hconj : ∀ a, d.val * X a * d.val⁻¹ = X (c*a)) (a : F) :
    (⟨X a, hmem a⟩ : borel) ∈ N := by
  let b := a / (c-1)
  let v : borel (K := F) := ⟨X b,hmem b⟩
  have hinv : (X b)⁻¹ = X (-b) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [hadd, neg_add_cancel, hzero]
  have he : ⁅d,v⁆ = ⟨X a,hmem a⟩ := by
    apply Subtype.ext
    change d.val * X b * d.val⁻¹ * (X b)⁻¹ = X a
    rw [hconj, hinv, hadd]
    congr 1
    dsimp [b]
    field_simp
    ring
  rw [← he]
  simpa only [commutatorElement_def, mul_assoc] using
    N.mul_mem hd ((inferInstance : N.Normal).conj_mem _ (N.inv_mem hd) v)

variable [Finite F] [CharP F 2]

/-- The full Borel, not just a selected subgroup, is its two-residual. -/
theorem borel_twoResidual (hq : 2 < Nat.card F) : pResidual 2 (borel (K := F)) = ⊤ := by
  classical
  let := Fintype.ofFinite F
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨t, ht⟩ := exists_ne (1 : Fˣ)
  have ht1 : (t : F) ≠ 1 := by simpa using ht
  have hti : ((t : F)⁻¹) ≠ 1 := by simpa using ht1
  let N := pResidual 2 (borel (K := F))
  have htorus (p : Fˣ × Fˣ) :
      (⟨torusHom p, (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩ : borel) ∈ N := by
    let f := inclusion (show splitTorus (K := F) ≤ borel from le_sup_right)
    have horder : orderOf (f (⟨torusHom p,⟨p,rfl⟩⟩ : splitTorus)) ∣
        Nat.card (splitTorus (K := F)) :=
      (orderOf_map_dvd f _).trans (orderOf_dvd_natCard _)
    exact mem_pResidual_of_orderOf_coprime (card_torus_odd.coprime_two_left.of_dvd_right horder)
  have hroot (X : F → Model F) (hadd : ∀ a b, X a * X b = X (a+b))
      (hzero : X 0 = 1) (hmem : ∀ a, X a ∈ unipotent) (p : Fˣ × Fˣ)
      (c : F) (hc : c ≠ 1)
      (hconj : ∀ a, torusHom p * X a * (torusHom p)⁻¹ = X (c*a)) :
      ∀ a, (⟨X a, (le_sup_left : unipotent ≤ borel) (hmem a)⟩ : borel) ∈ N :=
    root_mem_normal N X hadd hzero (fun a => (le_sup_left : unipotent ≤ borel) (hmem a))
      ⟨torusHom p, (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩ (htorus p) c hc hconj
  have hA := hroot rootA rootA_add rootA_zero (fun a => subset_closure (by simp))
    (t,1) t ht1 (by intro a; simpa [torusHom] using torus_rootA t 1 a)
  have hB := hroot rootB rootB_add rootB_zero (fun a => subset_closure (by simp))
    (1,t) (t : F)⁻¹ hti (by intro a; simpa [torusHom] using torus_rootB 1 t a)
  have hC := hroot rootC rootC_add rootC_zero (fun a => subset_closure (by simp))
    (t,1) t ht1 (by intro a; exact torus_rootC t 1 a)
  have hD := hroot rootD rootD_add rootD_zero (fun a => subset_closure (by simp))
    (1,t) t ht1 (by intro a; exact torus_rootD 1 t a)
  have hE := hroot rootE rootE_add rootE_zero (fun a => subset_closure (by simp))
    (t,1) (t : F)⁻¹ hti (by intro a; simpa [torusHom] using torus_rootE t 1 a)
  have hF := hroot rootF rootF_add rootF_zero (fun a => subset_closure (by simp))
    (t,1) t ht1 (by intro a; simpa [torusHom] using torus_rootF t 1 a)
  have hU : unipotent (K := F) ≤ N.map borel.subtype := by
    apply (closure_le _).mpr
    intro g hg
    rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
    all_goals obtain ⟨a,rfl⟩ := hg
    · exact ⟨_,hA a,rfl⟩
    · exact ⟨_,hB a,rfl⟩
    · exact ⟨_,hC a,rfl⟩
    · exact ⟨_,hD a,rfl⟩
    · exact ⟨_,hE a,rfl⟩
    · exact ⟨_,hF a,rfl⟩
  have hT : splitTorus (K := F) ≤ N.map borel.subtype := by
    rintro g ⟨p,rfl⟩
    exact ⟨_,htorus p,rfl⟩
  apply top_unique
  intro g _
  obtain ⟨x,hx,he⟩ := (sup_le hU hT : borel ≤ N.map borel.subtype) g.property
  exact (Subtype.ext he : x = g) ▸ hx

/-- Two-perfectness is transported to every Sylow normalizer. -/
theorem sylowNormalizer_twoResidual (hq : 2 < Nat.card F) (S : Sylow 2 (Model F)) :
    pResidual 2 (normalizer (S : Set (Model F))) = ⊤ := by
  apply (pResidual_eq_top_iff _ _).mpr
  exact ((pResidual_eq_top_iff _ _).mp (borel_twoResidual hq)).of_surjective
    (sylowNormalizerEquiv S).symm.toMonoidHom (sylowNormalizerEquiv S).symm.surjective

end Atlas.G2.EvenBorelTorus
