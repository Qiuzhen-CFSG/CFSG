module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Model
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The binary component's inner involution

The literal inner action in Aschbacher–Smith 1.1.5(3)(a) determines a unique
involution z_L in the binary linear component. Centerlessness is proved from
the supplied matrix-model equivalence. Since z is central in S, uniqueness
also shows that N_S(L) centralizes z_L, retaining possible permutation of
components by elements of S outside N_S(L).

Subnormal Sylow restriction identifies S ∩ L as a Sylow subgroup of L.
The projection centralizes this intersection, and its order two forces it
into that Sylow subgroup. Thus the projection is a central involution of
the actual component Sylow subgroup, as required by the matrix calculation.

These are inputs to the intersection calculation in 2.3.9(7)(g), printed
p.525. No maximality of the involution centralizer is asserted here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {n : ℕ} [NeZero n]

theorem exists_unique_projection (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃! t : L, IsConjugationProjection L z t ∧ orderOf t = 2 :=
  h.exists_unique_projection (center_eq_bot e) α hα hinner

theorem projection_centralizes_normalizer (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    {s : G} (hsS : s ∈ (S : Subgroup H).map H.subtype)
    (hsL : s ∈ normalizer (L : Set G)) : s * (t : G) = (t : G) * s := by
  let β := L.normalizerMonoidHom ⟨s, hsL⟩
  have hβ (x : L) : (β x : G) = s * (x : G) * s⁻¹ := rfl
  have hβi (x : L) : (β.symm x : G) = s⁻¹ * (x : G) * s := by
    calc
      (β.symm x : G) = s⁻¹ * (s * (β.symm x : G) * s⁻¹) * s := by group
      _ = s⁻¹ * (x : G) * s := by rw [← hβ, β.apply_symm_apply]
  have hcomm := h.central s hsS
  have ht' : IsConjugationProjection L z (β t) := by
    intro x
    have hh := congrArg (fun u : G => s * u * s⁻¹) (ht (β.symm x))
    simp only [hβi, Subgroup.coe_mul, Subgroup.coe_inv] at hh
    change z * (x : G) * z⁻¹ = (β t : G) * (x : G) * (β t : G)⁻¹
    rw [hβ]
    have hsz : s * z * s⁻¹ = z := by rw [hcomm, mul_inv_cancel_right]
    calc
      z * (x : G) * z⁻¹ =
          s * (z * (s⁻¹ * (x : G) * s) * z⁻¹) * s⁻¹ := by
        calc
          _ = (s * z * s⁻¹) * (x : G) * (s * z * s⁻¹)⁻¹ := by rw [hsz]
          _ = _ := by group
      _ = s * ((t : G) * (s⁻¹ * (x : G) * s) * (t : G)⁻¹) * s⁻¹ := hh
      _ = (s * (t : G) * s⁻¹) * (x : G) * (s * (t : G) * s⁻¹)⁻¹ := by group
  have he : β t = t := by
    apply conj_injective_of_center_eq_bot (center_eq_bot e)
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact (ht' x).symm.trans (ht x)
  have hh := hβ t
  rw [he] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh.symm

omit [NeZero n] in
/-- Component subnormality, relative to H, gives the actual Sylow intersection. -/
theorem exists_component_sylow (h : LocalSetup H L M S z) :
    ∃ T : Sylow 2 L, (T : Subgroup L) =
      ((S : Subgroup H).map H.subtype).subgroupOf L := by
  let := h.finite
  obtain ⟨Q, hQ⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) h.component.1
  let f := subgroupOfEquivOfLe h.component_le
  refine ⟨Q.mapSurjective (f := f.toMonoidHom) f.surjective, ?_⟩
  change (Q : Subgroup _).map f.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    have hey : y = ⟨x, h.component_le x.property⟩ := Subtype.ext he
    subst y
    exact ⟨⟨⟨x, h.component_le x.property⟩, x.property⟩, hy, rfl⟩

/-- The binary projection is central in the component's Sylow subgroup.
Membership follows from its two-power order and Sylow maximality. -/
theorem projection_mem_center_component_sylow (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    (ht2 : orderOf t = 2) (T : Sylow 2 L)
    (hT : (T : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L) :
    t ∈ T ∧ ∀ x : L, x ∈ T → x * t = t * x := by
  have hc : t ∈ centralizer (T : Set L) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hxS : (x : G) ∈ (S : Subgroup H).map H.subtype := by
      change x ∈ (T : Subgroup L) at hx
      rw [hT] at hx
      exact hx
    exact Subtype.ext (projection_centralizes_normalizer h e ht hxS
      (le_normalizer x.property))
  refine ⟨?_, fun x hx => mem_centralizer_iff.mp hc x hx⟩
  have hp : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht2, pow_one]
  have hn : t ∈ normalizer (T : Set L) := centralizer_le_normalizer _ hc
  have hm : t ∈ zpowers t ⊓ normalizer (T : Set L) := ⟨mem_zpowers t, hn⟩
  rw [hp.inf_normalizer_sylow T] at hm
  exact hm.2

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
