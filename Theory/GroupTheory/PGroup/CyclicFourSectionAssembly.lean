module

public import Theory.GroupTheory.PGroup.CyclicFourSectionDerived

/-!
# Assembling a cyclic-four section from a central supplement

An abelian supplement containing an involution normalizes its fixed core.
If the fixed core contains the core's derived subgroup, the core also
normalizes it. A fixed elementary four is therefore the unique normal
four, and it generates the involution centralizer with the supplement.

A supplement whose intersection with the core is ambient central inherits
the cyclic order-four quotient of the ambient group. Its quotient kernel
is retained as an explicit normal subgroup of the supplement.

These are the formal assembly steps in Janko–Thompson (1970), §4, case (a),
printed p.391, after the normalized quaternion-action calculation.
-/

open Subgroup
namespace Subgroup

/-- An abelian supplement containing the involution identifies the fixed
core with the unique normal four and generates its full centralizer. -/
public theorem fixed_core_eq_unique_four_of_central_supplement
    {P : Type*} [Group P] [Finite P]
    (H W K : Subgroup P) [H.Normal]
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hKH : K ⊔ H = ⊤) [IsMulCommutative K]
    (t : P) (htK : t ∈ K)
    (hfixed : IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P))
    (hcard : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4)
    (hcenter : ⁅H,H⁆ ≤ H ⊓ centralizer ({t} : Set P)) :
    H ⊓ centralizer ({t} : Set P) = W ∧
      K ⊔ W = centralizer ({t} : Set P) := by
  let F := H ⊓ centralizer ({t} : Set P)
  have hKF : K ≤ normalizer (F : Set P) := by
    apply le_normalizer_iff.mpr
    intro k hk x hx
    refine ⟨(inferInstance : H.Normal).conj_mem x hx.1 k, ?_⟩
    have hkt : k * t = t * k :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := K)).comm ⟨k,hk⟩ ⟨t,htK⟩)
    have hxt := mem_centralizer_singleton_iff.mp hx.2
    apply mem_centralizer_singleton_iff.mpr
    calc
      (k * x * k⁻¹) * t = k * x * (k⁻¹ * t) := by group
      _ = k * x * (t * k⁻¹) := by rw [(show Commute k t from hkt).inv_left.eq]
      _ = k * (x*t) * k⁻¹ := by group
      _ = k * (t*x) * k⁻¹ := by rw [hxt]
      _ = (k*t) * x * k⁻¹ := by group
      _ = t * (k*x*k⁻¹) := by rw [hkt]; group
  have hHF : H ≤ normalizer (F : Set P) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl inf_le_left).trans hcenter)
  have hFn : F.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hKH]
    exact sup_le hKF hHF))
  have hFW : F = W := hunique F hFn hfixed hcard
  refine ⟨hFW, ?_⟩
  have hKC : K ≤ centralizer ({t} : Set P) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((IsMulCommutative.is_comm (M := K)).comm ⟨k,hk⟩ ⟨t,htK⟩))
  apply le_antisymm (sup_le hKC (hFW ▸ inf_le_right))
  intro x hx
  have hxKH : x ∈ K ⊔ H := by rw [hKH]; trivial
  obtain ⟨k,hk,h,hh,rfl⟩ := mem_sup_of_normal_right.mp hxKH
  have hhC : h ∈ centralizer ({t} : Set P) := by
    have hc := (centralizer ({t} : Set P)).mul_mem
      ((centralizer ({t} : Set P)).inv_mem (hKC hk)) hx
    simpa only [inv_mul_cancel_left] using hc
  exact (K ⊔ W).mul_mem (mem_sup_left hk) (mem_sup_right (hFW ▸ ⟨hh,hhC⟩))

end Subgroup

namespace Subgroup
/-- A central-intersection supplement inherits the cyclic-four quotient. -/
public theorem cyclic_quotient_section_of_supplement
    {P : Type*} [Group P] [Finite P]
    (H K : Subgroup P) [H.Normal] [IsCyclic (P ⧸ H)]
    (hindex : H.index = 4) (hsup : K ⊔ H = ⊤)
    (hcentral : K ⊓ H ≤ center P) :
    ∃ Z : Subgroup K, ∃ hZ : Z.Normal, letI := hZ;
      IsCyclic (K ⧸ Z) ∧
      Nat.card (K ⧸ Z) = 4 ∧ Z ≤ (center P).comap K.subtype := by
  let f := (QuotientGroup.mk' H).comp K.subtype
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective H a
    have hx : x ∈ K ⊔ H := by rw [hsup]; trivial
    obtain ⟨k,hk,h,hh,rfl⟩ := mem_sup_of_normal_right.mp hx
    refine ⟨⟨k,hk⟩, ?_⟩
    change QuotientGroup.mk' H k = QuotientGroup.mk' H (k*h)
    have hhq : QuotientGroup.mk' H h = 1 := (QuotientGroup.eq_one_iff (N := H) h).mpr hh
    rw [map_mul, hhq, mul_one]
  let e := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  refine ⟨f.ker, inferInstance, isCyclic_of_surjective e.symm e.symm.surjective, ?_, ?_⟩
  · exact (Nat.card_congr e.toEquiv).trans hindex
  · intro k hk
    exact hcentral ⟨k.property, (QuotientGroup.eq_one_iff (N := H) (k : P)).mp hk⟩
end Subgroup

namespace Subgroup
/-- A central supplement and an elementary fixed four assemble the full
cyclic-four centralizer section with its explicit central kernel. -/
public theorem cyclic_four_centralizer_section_of_supplement
    {P : Type*} [Group P] [Finite P]
    (H W K : Subgroup P) [H.Normal] [IsCyclic (P ⧸ H)]
    (hindex : H.index = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hsup : K ⊔ H = ⊤) (hcentral : K ⊓ H ≤ center P)
    (hclass : ⁅H,H⁆ ≤ center P) (t : P) (htK : t ∈ K)
    (hfixed : IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P))
    (hcard : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4) :
    ∃ Z : Subgroup K, ∃ hZ : Z.Normal, letI := hZ;
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center P).comap K.subtype ∧
      H ⊓ centralizer ({t} : Set P) = W ∧ K ⊔ W = centralizer ({t} : Set P) := by
  obtain ⟨Z, hZ, hcyclic, hquot, hZc⟩ :=
    cyclic_quotient_section_of_supplement H K hindex hsup hcentral
  let := hZ
  let := hcyclic
  let : IsMulCommutative K :=
    (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center (by
      rw [QuotientGroup.ker_mk']
      intro a ha
      exact mem_center_iff.mpr (fun k => Subtype.ext (mem_center_iff.mp (hZc ha) k)))
  have hcenter : ⁅H,H⁆ ≤ H ⊓ centralizer ({t} : Set P) :=
    le_inf (commutator_le_left H H) (hclass.trans (center_le_centralizer _))
  obtain ⟨hFW,hgen⟩ := fixed_core_eq_unique_four_of_central_supplement
    H W K hunique hsup t htK hfixed hcard hcenter
  exact ⟨Z, hZ, hcyclic, hquot, hZc, hFW, hgen⟩
end Subgroup
