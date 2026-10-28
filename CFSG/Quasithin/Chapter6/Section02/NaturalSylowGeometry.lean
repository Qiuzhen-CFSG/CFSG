module
public import CFSG.Quasithin.Chapter6.Section01.SourceCentralLine
public import Theory.Representation.SpecialLinearNatural.SylowFixedLine
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.ElementaryAbelian.Injective

/-!
# The actual natural Sylow plane in the Chapter 6 source

Map a Sylow subgroup through the literal quotient L → L/O₂(L) and the
natural-module marking. The fixed field-line pulls back to C_V(S), and
all its elements occur as displacements. Consequently [V,S] = C_V(S),
with order equal to the field order. Restricting the ambient Sylow to a
normalized L gives the precise subgroup C_V(T ∩ L).

For the genuine Hypothesis 6.1.1, the natural layer output of 6.1.27
therefore supplies the elementary four-group Z_S used in the M₂₂
centralizer construction. The earlier natural-model selection remains
an explicit source input; no global recognition conclusion is assumed.
Source: Aschbacher–Smith, combined manuscript, §6.2, printed pp.680–681.
-/

public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} {n : ℕ}

/-- Fixed points and commutators for the actual embedded Sylow action. -/
theorem IsNaturalModule.sylow_fixed_geometry (h : IsNaturalModule L V n)
    (S : Sylow 2 L) :
    Nat.card (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) : Subgroup G) = 2 ^ n ∧
      ⁅V, (S : Subgroup L).map L.subtype⁆ =
        V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := h
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  obtain ⟨W, hWcard, hWfix, hWdisp, hWonto⟩ :=
    Representation.SpecialLinearTwo.sylow_fixed_line_displacements 2 P
  let j : Multiplicative (Fin 2 → F) →* G := V.subtype.comp f.symm.toMonoidHom
  have hj : Function.Injective j := V.subtype_injective.comp f.symm.injective
  have hconj (s : L) (v : V) :
      j (Multiplicative.ofAdd (toLin' (q s) (f v).toAdd)) =
        (s : G) * (v : G) * (s : G)⁻¹ := hf s v
  have hfix (v : V) : (f v).toAdd ∈ W ↔
      (v : G) ∈ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
    rw [hWfix]
    constructor
    · intro hv
      apply mem_centralizer_iff.mpr
      rintro _ ⟨s, hs, rfl⟩
      have hh := hconj s v
      rw [hv (q s) (mem_map.mpr ⟨s, hs, rfl⟩)] at hh
      change (f.symm (f v) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    · intro hv g hg
      obtain ⟨s, hs, rfl⟩ := hg
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      change (s : G) * (v : G) * (s : G)⁻¹ = (f.symm (f v) : G)
      rw [f.symm_apply_apply, mem_centralizer_iff.mp hv (s : G)
        (mem_map.mpr ⟨s, hs, rfl⟩), mul_inv_cancel_right]
  let Wm : Subgroup (Multiplicative (Fin 2 → F)) := W.toAddSubgroup.toSubgroup'
  have hmap : Wm.map j =
      V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(f.symm w).property, (hfix (f.symm w)).mp ?_⟩
      change w.toAdd ∈ W at hw
      simpa only [MulEquiv.apply_symm_apply] using hw
    · intro hx
      exact ⟨f ⟨x, hx.1⟩, (hfix ⟨x, hx.1⟩).mpr hx.2,
        congrArg (fun v : V => (v : G)) (f.symm_apply_apply ⟨x, hx.1⟩)⟩
  have hc : Nat.card (Wm.map j) = Nat.card F := by
    rw [card_map_of_injective hj]
    exact hWcard
  have hdisp (s : L) (v : V) :
      j (Multiplicative.ofAdd (toLin' (q s) (f v).toAdd - (f v).toAdd)) =
        ⁅(s : G), (v : G)⁆ := by
    rw [ofAdd_sub, map_div, ofAdd_toAdd, hconj, div_eq_mul_inv]
    change _ * (f.symm (f v) : G)⁻¹ = _
    rw [f.symm_apply_apply]
    rfl
  refine ⟨by rw [← hmap]; exact hc.trans hF, ?_⟩
  rw [commutator_comm V, ← hmap]
  apply le_antisymm
  · apply commutator_le.mpr
    rintro _ ⟨s, hs, rfl⟩ v hv
    have hh := mem_map_of_mem j (show Multiplicative.ofAdd
      (toLin' (q s) (f ⟨v, hv⟩).toAdd - (f ⟨v, hv⟩).toAdd) ∈ Wm from
      hWdisp (q s) (mem_map.mpr ⟨s, hs, rfl⟩) _)
    rw [hdisp] at hh
    exact hh
  · have hWne : W ≠ ⊤ := by
      intro he
      have hcard := hWcard
      rw [he, Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule F (Fin 2 → F)) ≃ₗ[F] (Fin 2 → F)).toEquiv, Nat.card_fun, Nat.card_fin] at hcard
      have hpos : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top W hWne
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨g, hg, hgw⟩ := hWonto v hv w.toAdd hw
    obtain ⟨s, hs, rfl⟩ := hg
    have hh := hdisp s (f.symm (Multiplicative.ofAdd v))
    rw [f.apply_symm_apply, toAdd_ofAdd, hgw, ofAdd_toAdd] at hh
    rw [hh]
    exact commutator_mem_commutator (mem_map.mpr ⟨s, hs, rfl⟩) (f.symm _).property

/-- The Sylow actor is the actual intersection with the original L. -/
theorem IsNaturalModule.sylow_intersection_geometry (h : IsNaturalModule L V n)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nat.card (V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) : Subgroup G) = 2 ^ n ∧
      ⁅V, (T : Subgroup G) ⊓ L⁆ = V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) := by
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hh := h.sylow_fixed_geometry S
  rwa [hS, subgroupOf_map_subtype] at hh

namespace Hypothesis611
variable {κ : GroupClass} {T : Sylow 2 G} {M V₀ : Subgroup G}

/-- The natural-module conclusion of 6.1.27 constructs the marked plane,
including its order and its equality with the Sylow commutator subgroup. -/
theorem natural_ZS_geometry (h : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n) :
    IsElementaryAbelian 2 (ZS (T : Subgroup G) L V₀) ∧
      Nat.card (ZS (T : Subgroup G) L V₀) = 4 ∧
      ⁅layer L V₀, (T : Subgroup G) ⊓ L⁆ = ZS (T : Subgroup G) L V₀ := by
  obtain ⟨hc, he⟩ := h6127.2.1.sylow_intersection_geometry T h.sylow_normalizes_L
  exact ⟨h.ZS_elementary, hc, he⟩

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
