module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Action
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Geometry
public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The hyperplane centralizer from the commutator form

The full zero criterion of the genuine commutator form identifies What
with V₂hat-perp. Double orthogonality proves Z(W)=V₂Z(U), and conjugating
the embedded intrinsic center proves Z(X)=V₂Z(U)^g. The marked plane has
image of order two, so orthogonal dimension gives |U:W|=2.

This proves directly in U/Z(U) the centralizer consequence of the source's
extraspecial central-product decomposition. It avoids auxiliary choices
of E₀ and V₀, while preserving all literal subgroup and quotient maps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
12.8.8(2) and the proof of 12.8.11, printed pp.851 and 854.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The literal quotient map, regarded additively. -/
def hatElement (F : InvariantFlag T V n) (u : F.U) : Additive F.Uhat :=
  Additive.ofMul (QuotientGroup.mk' (center F.U) u)

/-- Orthogonality to the literal image of A is exactly commutation with A. -/
theorem hat_orthogonal_iff (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (A : Subgroup G) (hA : A ≤ F.U) (u : F.U) :
    hatElement F u ∈ B.orthogonal (hatSpace F A) ↔
      (u : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hu a ha
    have hv : hatElement F ⟨a,hA ha⟩ ∈ hatSpace F A := ⟨_,ha,rfl⟩
    have hc := (hB ⟨a,hA ha⟩ u).mp (hu _ hv)
    exact congrArg Subtype.val hc.eq
  · intro hu a ha
    obtain ⟨v,hv,he⟩ := (show a.toMul ∈ hatImage F A from ha)
    have he' : a = hatElement F v := (congrArg Additive.ofMul he).symm
    rw [he']
    apply (hB v u).mpr
    exact Subtype.ext (hu v hv)

/-- W has the hyperplane image V₂hat-perp in the genuine commutator space. -/
theorem What_eq_orthogonal (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v) :
    hatSpace F F.W = B.orthogonal (hatSpace F (F.Vi 2)) := by
  ext q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) q.toMul
  have he : q = hatElement F u := (congrArg Additive.ofMul hu).symm
  rw [he, hat_orthogonal_iff F B hB _ ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))]
  constructor
  · rintro ⟨v,hv,hvQ⟩
    have hvc := (hat_orthogonal_iff F B hB (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) v).mpr hv.2
    have heq : hatElement F v = hatElement F u := congrArg Additive.ofMul hvQ
    rw [heq] at hvc
    exact (hat_orthogonal_iff F B hB (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) u).mp hvc
  · intro hu
    exact ⟨u,⟨u.property,hu⟩,rfl⟩

/-- The center of the hyperplane centralizer is the marked plane times Z(U).
This proves the extraspecial centralizer calculation directly from the genuine
nondegenerate commutator form. -/
theorem center_W_eq_plane_sup_ZU (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) (hrefl : B.IsRefl) :
    centerIn F.W = F.Vi 2 ⊔ F.ZU := by
  have hP : F.Vi 2 ≤ F.W := by
    refine le_inf ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) ?_
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,F.le_seed 2 hb⟩ : V) ⟨a,F.le_seed 2 ha⟩)
  have hZ : F.ZU ≤ F.W := by
    refine le_inf (map_subtype_le _) ?_
    rintro z ⟨u, hu, rfl⟩ a ha
    exact congrArg Subtype.val (mem_center_iff.mp hu
      ⟨a, (F.le_seed 2).trans (le_conjugateSpanBy V F.H) ha⟩)
  have ho : B.orthogonal (hatSpace F F.W) = hatSpace F (F.Vi 2) := by
    rw [What_eq_orthogonal F B hB, B.orthogonal_orthogonal hnd hrefl]
  apply le_antisymm
  · rintro a ⟨w, hw, rfl⟩
    let u : F.U := ⟨w,w.property.1⟩
    have hc : (u : G) ∈ centralizer (F.W : Set G) := by
      intro b hb
      exact congrArg Subtype.val (mem_center_iff.mp hw ⟨b,hb⟩)
    have hm := (hat_orthogonal_iff F B hB F.W inf_le_left u).mpr hc
    rw [ho] at hm
    exact (mem_hatImage_mk_iff F (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) u).mp hm
  · intro a ha
    have hau : a ∈ F.U := (sup_le (hP.trans inf_le_left) (hZ.trans inf_le_left)) ha
    let u : F.U := ⟨a,hau⟩
    have hm : hatElement F u ∈ hatSpace F (F.Vi 2) :=
      (mem_hatImage_mk_iff F (F.Vi 2)
        ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) u).mpr ha
    rw [← ho] at hm
    have hc := (hat_orthogonal_iff F B hB F.W inf_le_left u).mp hm
    refine ⟨⟨a, sup_le hP hZ ha⟩, mem_center_iff.mpr ?_, rfl⟩
    intro w
    exact Subtype.ext (hc w w.property)

/-- Conjugation transports the full intrinsic center, including its actual embedding. -/
theorem center_X_eq_plane_sup_conjugate_ZU (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hg : g ∈ F.Gi 2)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) (hrefl : B.IsRefl) :
    centerIn (F.X g) = F.Vi 2 ⊔ conjugate F.ZU g := by
  change (center (F.W.map (MulAut.conj g⁻¹).toMonoidHom)).map
    (F.W.map (MulAut.conj g⁻¹).toMonoidHom).subtype = _
  rw [← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective]
  change (centerIn F.W).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [center_W_eq_plane_sup_ZU F B hB hnd hrefl, Subgroup.map_sup]
  have he : (F.Vi 2).map (MulAut.conj g⁻¹).toMonoidHom = F.Vi 2 :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg)
  rw [he]
  rfl

/-- The hyperplane index is derived from the nondegenerate commutator form
and the four-element marked plane; no rank premise is assumed. -/
theorem W_relIndex_U_eq_two (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hVZ : V ⊓ F.ZU = F.Vi 1)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) : F.W.relIndex F.U = 2 := by
  have hp : Module.finrank (ZMod 2) (hatSpace F (F.Vi 2)) = 1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F (F.Vi 2))
    rw [Nat.card_zmod, card_hatSpace, card_plane_hat F hn hVZ] at hc
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    simpa only [pow_one] using hc.symm
  have hd := B.finrank_add_finrank_orthogonal' (hatSpace F (F.Vi 2))
  rw [hnd.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero,
    ← What_eq_orthogonal F B hB, hp] at hd
  have hc : Nat.card F.Uhat = 2 * Nat.card (hatImage F F.W) := by
    have hu := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    have hw := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F F.W)
    rw [Nat.card_zmod, card_hatSpace] at hw
    rw [Nat.card_zmod, ← hd, pow_add, pow_one, ← hw] at hu
    exact (Nat.card_congr Additive.ofMul).trans hu
  have hZ : F.ZU ≤ F.W := by
    refine le_inf (map_subtype_le _) ?_
    rintro z ⟨u,hu,rfl⟩ a ha
    exact congrArg Subtype.val (mem_center_iff.mp hu
      ⟨a,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) ha⟩)
  have hw := card_hatImage_mul_card_inf F F.W inf_le_left
  rw [inf_eq_right.mpr hZ] at hw
  have hu := (center F.U).index_mul_card
  rw [index_eq_card, hc,
    show Nat.card (center F.U) = Nat.card F.ZU from
      (card_map_of_injective (K := center F.U) F.U.subtype_injective).symm,
    mul_assoc, hw] at hu
  have hi := (F.W.subgroupOf F.U).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.U from inf_le_left)).toEquiv] at hi
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hi.trans hu.symm)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
