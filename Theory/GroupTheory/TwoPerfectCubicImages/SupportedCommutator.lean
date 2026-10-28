module
public import Theory.GroupTheory.TwoPerfectCubicImages
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Containment from a supported cubic commutator

In a two-perfect group with cubic quotient by its two-core, a normal
subgroup which is not contained in the two-core is the whole group. Thus,
if an ambient normal subgroup contains the commutators with a normalizing
actor and one such commutator has nontrivial cubic image, it contains the
whole original two-perfect subgroup. The actual map detecting that cubic
is retained; its kernel need not be trivial.

Source application: Aschbacher–Smith, 13.6.15, printed p.930, where a
supported transposition removes the residual action outside the A₅ component.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup

theorem normal_eq_top_of_not_le_twoCore_cubic {H : Type*} [Group H]
    (hp : IsPPerfect 2 H) (hc : Nat.card (H ⧸ pCore 2 H) = 3)
    (N : Subgroup H) [N.Normal] (hne : ¬ N ≤ pCore 2 H) : N=⊤ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsSimpleGroup (H ⧸ pCore 2 H) := isSimpleGroup_of_prime_card hc
  let q := QuotientGroup.mk' (pCore 2 H)
  have hn := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with h|h
  · exact (hne (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp h)).elim
  · have hs : N ⊔ pCore 2 H = ⊤ := by
      have hh := congrArg (comap q) h
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    exact hp N inferInstance (isPGroup_quotient_of_sup_eq_top N (pCore 2 H) pCore_isPGroup hs)

theorem le_normal_of_supported_cubic_commutator {D E : Type*} [Group D] [Group E]
    (H C : Subgroup D) [C.Normal]
    (hp : IsPPerfect 2 H) (hc : Nat.card (H ⧸ pCore 2 H) = 3)
    (r : D →* E) (a : D) (ha : a ∈ normalizer (H : Set D))
    (hcomm : ∀ h ∈ H, ⁅h,a⁆ ∈ C)
    (b : H) (hb : r ⁅b.val,a⁆ ^ 3 = 1) (hne : r ⁅b.val,a⁆ ≠ 1) : H ≤ C := by
  have hcH : ⁅b.val,a⁆ ∈ H := by
    have hx := (ha b.val⁻¹).mp (H.inv_mem b.property)
    have hh := H.mul_mem b.property hx
    simpa only [commutatorElement_def,mul_assoc] using hh
  let c : H := ⟨⁅b.val,a⁆,hcH⟩
  have hcn : ¬ C.subgroupOf H ≤ pCore 2 H := by
    intro hle
    have hc2 : c ∈ pCore 2 H := hle (hcomm b.val b.property)
    let f := r.comp H.subtype
    let Q := (pCore 2 H).map f
    have hQ : IsPGroup 2 Q := pCore_isPGroup.map f
    let x : Q := ⟨r ⁅b.val,a⁆,mem_map.mpr ⟨c,hc2,rfl⟩⟩
    have hx : x^3=1 := Subtype.ext hb
    have he : x=1 := (hQ.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
      simpa only [IsPGroup.powEquiv_apply,one_pow] using hx)
    exact hne (congrArg Subtype.val he)
  have ht := normal_eq_top_of_not_le_twoCore_cubic hp hc (C.subgroupOf H) hcn
  intro h hh
  exact (show (⟨h,hh⟩ : H) ∈ C.subgroupOf H from ht.symm ▸ mem_top _)
end Subgroup
