module
public import Theory.Representation.G2.NaturalScalarCubic
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The chosen short Cartan factor in G₂(4)

The short coroot torus has parameters (a,a⁻¹). Over the field of order four
this is the long-section centralizing torus (s²,s), with s=a⁻¹. The short
plane determinant identifies the torus part of every element in the short
Borel intersection. Modulo the long-section centralizer this intersection
is a two-group, so every cubic element centralizes the long local quotient.
The natural highest line distinguishes the two local residuals: the short
one moves every nonzero vector fixed by the positive-root Sylow.

Source: Aschbacher–Smith B.4.6(14), printed p.88, used in 9.3.9, p.734.
The source point parabolic P₁ is the code's long parabolic₂; the source plane
parabolic P₂ is the code's short parabolic₁. The forward implication needed
by 9.3.9 is proved here for cubics normalizing the common Sylow.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Atlas.G2.CubicCartan
open LieParabolicSetup Explicit Atlas.SplitOctonion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem unit_cube (hF : Nat.card F = 4) (a : Fˣ) : a ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := a)
  simpa only [Nat.card_units,hF] using h

theorem short_torus_commutators (hF : Nat.card F = 4) (a : Fˣ) :
    ∀ b ∈ local₂ (F := F), ⁅torus a a⁻¹,b⁆ ∈ local₂.pCoreIn 2 := by
  have ha : (a⁻¹) ^ 2 = a := by
    have h := unit_cube hF a⁻¹
    have he : (a⁻¹)^2 * a⁻¹ = 1 := by simpa only [pow_succ,pow_one] using h
    exact (eq_inv_iff_mul_eq_one.mpr he).trans (inv_inv a)
  rw [local₂_pCoreIn]
  simpa only [ha] using NaturalScalarCubic.long_commutators a⁻¹

omit [Finite F] in
private theorem torus_mem_short_iff (l m : Fˣ) :
    torus l m ∈ local₁ (F := F) ↔ m = l⁻¹ := by
  constructor
  · intro ht
    rw [local₁_eq_shortSpecial] at ht
    obtain ⟨g,hg,he⟩ := ht
    have he' : g.val = torus l m := he
    have hg' : (shortRepresentation g).det = 1 := hg
    have hrep : shortRepresentation g = !![(l : F),0;0,(m : F)] := by
      ext i j
      change g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
        (i.castLE (by decide : 2 ≤ 8)) = _
      rw [he']
      fin_cases i <;> fin_cases j <;>
        simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]
    rw [hrep,Matrix.det_fin_two] at hg'
    have heq : l * m = 1 := Units.ext (by simpa using hg')
    exact (eq_inv_iff_mul_eq_one.mpr (by simpa only [mul_comm] using heq))
  · rintro rfl
    exact short_torus_mem_local₁ l

omit [Finite F] in
private theorem short_borel_decomposition {x : Model F}
    (hxS : x ∈ local₁) (hxB : x ∈ borel) :
    ∃ u ∈ unipotent, ∃ a : Fˣ, x = u * torus a a⁻¹ := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := F)).surjective ⟨x,hxB⟩
  have he' : (u : Model F) * (t : Model F) = x := congrArg Subtype.val he
  have htS : (t : Model F) ∈ local₁ := by
    have hh := local₁.mul_mem (local₁.inv_mem (unipotent_le_local₁ u.property)) hxS
    rw [←he',inv_mul_cancel_left] at hh
    exact hh
  obtain ⟨⟨l,m⟩,ht⟩ := t.property
  change torus l m = t.val at ht
  have hm := (torus_mem_short_iff l m).mp (ht ▸ htS)
  refine ⟨u,u.property,l,?_⟩
  rw [←he',←ht,hm]

private theorem cubic_mem_of_two_quotient {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hQ : IsPGroup 2 (G ⧸ N))
    (x : G) (hx : x ^ 3 = 1) : x ∈ N := by
  let q := QuotientGroup.mk' N
  obtain ⟨n,hn⟩ := hQ (q x)
  have h3 : (q x)^3 = 1 := by rw [←map_pow,hx,map_one]
  apply (QuotientGroup.eq_one_iff x).mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left n)
    (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h3)

theorem short_borel_cubic_commutators (hF : Nat.card F = 4) (x : Model F)
    (hxS : x ∈ local₁) (hxB : x ∈ borel) (hx3 : x ^ 3 = 1) :
    x ∈ normalizer (local₂ (F := F) : Set (Model F)) ∧
      ∀ b ∈ (local₂ (F := F)), ⁅x,b⁆ ∈ (local₂ (F := F)).pCoreIn 2 := by
  let C := commutatorPreimage (normalizer (local₂ (F := F) : Set (Model F)))
    local₂ (local₂.pCoreIn 2)
  let J := borel (K := F) ⊓ local₁
  have hNC : normalizer (local₂ (F := F) : Set (Model F)) ≤ normalizer (C : Set (Model F)) := by
    apply commutatorPreimage_normalized
    · exact normalizer_le_normalizer_characteristic_image local₂ (pCore 2 local₂)
    · exact (normalizer (local₂ (F := F) : Set (Model F))).le_normalizer
    · exact le_rfl
    · exact normalizer_le_normalizer_characteristic_image local₂ (pCore 2 local₂)
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_left.trans (borel_le_normalizer_local₂.trans hNC))
  have hUS : unipotent (K := F) ≤ J := le_inf le_sup_left unipotent_le_local₁
  have hgen : unipotent.subgroupOf J ⊔ C.subgroupOf J = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨u,hu,a,hy⟩ := short_borel_decomposition y.property.2 y.property.1
    have haJ : torus a a⁻¹ ∈ J :=
      ⟨mem_sup_right ⟨(a,a⁻¹),rfl⟩,short_torus_mem_local₁ a⟩
    have haC : torus a a⁻¹ ∈ C :=
      (mem_commutatorPreimage_iff _ _ _
        (normalizer_le_normalizer_characteristic_image local₂ (pCore 2 local₂)) _).mpr
        ⟨borel_le_normalizer_local₂ haJ.1,short_torus_commutators hF a⟩
    have hy' : y = (⟨u,hUS hu⟩ : J) * ⟨torus a a⁻¹,haJ⟩ := Subtype.ext hy
    rw [hy']
    exact mul_mem_sup hu haC
  have hquot : IsPGroup 2 (J ⧸ C.subgroupOf J) :=
    quotient_isPGroup_of_sup_eq_top (unipotent.subgroupOf J) (C.subgroupOf J)
      unipotent_isTwoGroup.comap_subtype hgen
  have hxC : x ∈ C := cubic_mem_of_two_quotient (C.subgroupOf J) hquot
    ⟨x,hxB,hxS⟩ (Subtype.ext hx3)
  exact (mem_commutatorPreimage_iff _ _ _
    (normalizer_le_normalizer_characteristic_image local₂ (pCore 2 local₂)) _).mp hxC

end Atlas.G2.CubicCartan

namespace Atlas.G2.CubicCartan
open LieParabolicSetup Restricted.NaturalCoordinates
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem short_normalizer_cubic_commutators (hF : Nat.card F = 4) (x : Model F)
    (hxS : x ∈ local₁) (hxN : x ∈ normalizer (unipotent (K := F) : Set (Model F)))
    (hx3 : x ^ 3 = 1) :
    x ∈ normalizer (local₂ (F := F) : Set (Model F)) ∧
      ∀ b ∈ (local₂ (F := F)), ⁅x,b⁆ ∈ (local₂ (F := F)).pCoreIn 2 := by
  rw [SylowNormalizer.normalizer_unipotent] at hxN
  exact short_borel_cubic_commutators hF x hxS hxN hx3

omit [Finite F] in
theorem short_local_moves_nonzero_unipotent_fixed (v : Space F) (hv : v ≠ 0)
    (hU : ∀ u ∈ unipotent (K := F), action F u v = v) :
    ¬ ∀ b ∈ local₁ (F := F), action F b v = v := by
  obtain ⟨a,rfl⟩ := (fixed_simpleRoots_iff F v).mp
    ⟨hU _ (subset_closure (by simp)),hU _ (subset_closure (by simp))⟩
  have ha : a ≠ 0 := by intro ha; subst a; simp at hv
  intro hfix
  have hs := hfix weylS (mem_sup_right (subset_closure (by simp)))
  have hh := congrFun hs 0
  apply ha
  simpa [action_weylS,highestVector] using hh.symm

omit [Finite F] in
theorem long_local_of_fixes_nonzero_unipotent_fixed
    (B : Subgroup (Model F)) (hB : B = local₁ ∨ B = local₂)
    (v : Space F) (hv : v ≠ 0)
    (hU : ∀ u ∈ unipotent (K := F), action F u v = v)
    (hfix : ∀ b ∈ B, action F b v = v) : B = local₂ := by
  rcases hB with rfl | he
  · exact (short_local_moves_nonzero_unipotent_fixed v hv hU hfix).elim
  · exact he
end Atlas.G2.CubicCartan
