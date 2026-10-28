module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Placement of the original action kernel in the Sylow subgroup

The genuine A₆ quotient L/O₂(L) and the surjective natural L-action show
that its kernel has the same order as O₂(L), hence is a two-group.
Since LT/L is also a two-group, the whole action kernel is a two-group.
It is normal in LT, so it lies in the specified Sylow subgroup T.
This proves C_G(V) ∩ LT ≤ T without assuming C_LT(V) = O₂(LT).

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(5),(6), p.948, with the original natural-module statement of
13.5.2(3), pp.915–916. The A₆ quotient is the precise allowed output of
the independent parabolic argument; the kernel placement is derived here.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open BinaryPermutation
variable {G : Type*} [Group G]

variable {B : Type*} [Group B]

/-- A surjection onto a group of the same order as L/O₂(L) has a two-group kernel. -/
theorem kernel_isTwoGroup_of_quotientCore [Finite G] (L : Subgroup G)
    (α : L →* B) (hα : Function.Surjective α) (e : (L ⧸ pCore 2 L) ≃* B) :
    IsPGroup 2 α.ker := by
  have hi : α.ker.index = (pCore 2 L).index := by
    change Nat.card (L ⧸ α.ker) = Nat.card (L ⧸ pCore 2 L)
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv).trans
      (Nat.card_congr e.toEquiv).symm
  have hc : Nat.card α.ker = Nat.card (pCore 2 L) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (pCore 2 L).index from Nat.card_pos)
    rw [← hi, α.ker.card_mul_index, hi, (pCore 2 L).card_mul_index]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  exact IsPGroup.of_card (hc.trans hn)

/-- A kernel in LT is a two-group if its restriction to L is a two-group. -/
theorem kernel_isTwoGroup_of_supplement [Finite G] (L : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (f : ↥(L ⊔ (T : Subgroup G)) →* B)
    (hker : IsPGroup 2 (f.comp (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).ker) :
    IsPGroup 2 f.ker := by
  let P := L ⊔ (T : Subgroup G)
  let L' := L.subgroupOf P
  let : L'.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hgen : L' ⊔ (T : Subgroup G).subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ P from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (P ⧸ L') :=
    isPGroup_quotient_of_sup_eq_top L' _ T.isPGroup'.comap_subtype hgen
  intro x
  obtain ⟨n, hn'⟩ := hp (QuotientGroup.mk' L' x.val)
  have hxL : ((x.val : P) ^ (2 ^ n) : P) ∈ L' :=
    (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' L' (x.val ^ (2 ^ n)) = 1
      rwa [map_pow])
  let l : L := ⟨(x.val.val) ^ (2 ^ n), hxL⟩
  have hl : l ∈ (f.comp (inclusion (show L ≤ P from le_sup_left))).ker := by
    change f (x.val ^ (2 ^ n)) = 1
    rw [map_pow, x.property, one_pow]
  obtain ⟨m, hm⟩ := hker ⟨l, hl⟩
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hm' := congrArg (fun y : (f.comp (inclusion (show L ≤ P from le_sup_left))).ker =>
    (y.val : G)) hm
  change (x.val.val ^ (2 ^ n)) ^ (2 ^ m) = 1 at hm'
  simpa [pow_add, pow_mul] using hm'
/-- A normal action kernel with two-group restriction to L lies in T. -/
theorem centralizer_le_sylow_of_natural_action [Finite G]
    (L V : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (f : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6))
    (hker : f.ker = actorKernel (L ⊔ (T : Subgroup G)) V)
    (α : L →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
    (hfL : ∀ l : L, f (inclusion le_sup_left l) = (α l).val)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    centralizer (V : Set G) ⊓ (L ⊔ (T : Subgroup G)) ≤ (T : Subgroup G) := by
  have he : (f.comp (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).ker =
      α.ker := by
    ext l
    change f (inclusion le_sup_left l) = 1 ↔ α l = 1
    rw [hfL]
    change (α l).val = (1 : alternatingGroup (Fin 6)).val ↔ α l = 1
    exact Subtype.val_injective.eq_iff
  have hp : IsPGroup 2 f.ker := kernel_isTwoGroup_of_supplement L T hn f
    (he ▸ kernel_isTwoGroup_of_quotientCore L α hα eL)
  have ht := hp.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)
    from le_sup_right))
  intro g hg
  exact ht (show (⟨g,hg.2⟩ : ↥(L ⊔ (T : Subgroup G))) ∈ f.ker from hker.symm ▸ hg.1)

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking

end
