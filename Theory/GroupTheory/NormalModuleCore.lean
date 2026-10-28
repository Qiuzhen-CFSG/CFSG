module
public import Theory.GroupTheory.ReducedNormal.SylowSupplement
/-!
# A normal module detects a normal supplement's two-core

If a normal component has precisely its two-core as kernel on a normal module,
and a two-group supplements it, the full module kernel is a two-group. When
the ambient two-core already fixes the module, this identifies that kernel
exactly. The ambient adapter retains the original inclusions and centralizer.

Source application: Aschbacher–Smith 13.7.4(1), printed p.937, where this
identity turns Thompson centralization into normality of the Baumann subgroup.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The kernel of a detected normal actor and a two-group supplement. -/
theorem centralizer_eq_core_of_normal_supplement
    (K U R : Subgroup G) [K.Normal] [U.Normal]
    (hR : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (hc : K ⊓ centralizer (U : Set G) = K.pCoreIn 2)
    (hQ : pCore 2 G ≤ centralizer (U : Set G)) :
    centralizer (U : Set G) = pCore 2 G := by
  let C := centralizer (U : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hk : IsPGroup 2 f.ker := by
    apply (isPGroup_pCoreIn 2 K).comap_subtype.to_le
    intro x hx
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff (x : G)).mp hx
    exact hc.le ⟨hxK,x.property⟩
  have hquot : IsPGroup 2 (G ⧸ K) := isPGroup_quotient_of_sup_eq_top K R hR hgen
  have hC : IsPGroup 2 C := by
    have hp := (hquot.to_subgroup (⊤ : Subgroup (G ⧸ K))).comap_of_ker_isPGroup f hk
    exact hp.of_equiv ((MulEquiv.subgroupCongr (comap_top f)).trans Subgroup.topEquiv)
  exact le_antisymm (le_sSup ⟨inferInstance,hC⟩) hQ

/-- The same kernel identity inside the literal generated ambient subgroup. -/
theorem ambient_centralizer_eq_core_of_normal_supplement
    (K U R : Subgroup G) (hRK : R ≤ normalizer (K : Set G))
    (hUI : U ≤ K ⊔ R) (hI : K ⊔ R ≤ normalizer (U : Set G))
    (hR : IsPGroup 2 R)
    (hc : K ⊓ centralizer (U : Set G) = K.pCoreIn 2)
    (hQ : (K ⊔ R).pCoreIn 2 ≤ centralizer (U : Set G)) :
    (K ⊔ R) ⊓ centralizer (U : Set G) = (K ⊔ R).pCoreIn 2 := by
  let X := K ⊔ R
  let KX := K.subgroupOf X
  let UX := U.subgroupOf X
  let RX := R.subgroupOf X
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hRK)
  let : UX.Normal := normal_subgroupOf_of_le_normalizer hI
  have hgen : KX ⊔ RX = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left) (show R ≤ X from le_sup_right)]
    exact subgroupOf_self _
  have hc' : KX ⊓ centralizer (UX : Set X) = KX.pCoreIn 2 := by
    apply map_injective X.subtype_injective
    rw [map_inf _ _ _ X.subtype_injective, map_centralizer_subtype,
      map_pCoreIn_of_injective 2 KX X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left),
      map_subgroupOf_eq_of_le hUI, ←inf_assoc,
      inf_eq_left.mpr (show K ≤ X from le_sup_left),hc]
  have hQ' : pCore 2 X ≤ centralizer (UX : Set X) := by
    intro x hx y hy
    apply Subtype.ext
    exact hQ (mem_map_of_mem X.subtype hx) y hy
  have he := centralizer_eq_core_of_normal_supplement KX UX RX hR.comap_subtype hgen hc' hQ'
  have hem := congrArg (map X.subtype) he
  rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hUI] at hem
  exact hem
end Theory.GroupTheory
