module

public import CFSG.Quasithin.Chapter16.Defs
public import Theory.GroupTheory.SylowCentralizerIndexTransfer
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Local deductions for the normality theorem

The Sylow intersection T ∩ L is Sylow in L by subnormality alone. The
implication from 16.1.8 to 16.2.3 uses the centralizer-index transfer, with
no assumption of the normality that 16.2.4 must establish. Once relative
normality is proved, the chosen ambient Sylow subgroup normalizes L.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Notation 16.2.2 and Lemma 16.2.3, pp.1173–1174.
`component_of_small_index_of_transfer` is conditional on 16.1.8; this module
does not assert 16.1.8 or Theorem 16.2.4.
-/

public section

namespace CFSG.Quasithin.Chapter16

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The component is quasisimple as a subgroup of the original ambient group. -/
theorem IsCentralizerComponent.quasisimple (hL : IsCentralizerComponent z L) :
    IsQuasisimple L := by
  let := hL.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)

/-- The Sylow intersection in Notation 16.2.2 needs only component subnormality. -/
theorem CentralComponentSetup.exists_component_sylow [Finite G]
    (h : CentralComponentSetup T z L) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let C := involutionCentralizer z
  obtain ⟨S, hS⟩ := (T.subtype h.sylow_centralizes).exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf C) h.component.2.1
  let e := subgroupOfEquivOfLe h.component.1
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup _).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, h.component.1 x.property⟩, x.property⟩, hx, rfl⟩

/-- Relative normality in C_G(z) makes the chosen ambient Sylow subgroup
normalize L. The normality premise is exactly the missing 16.2.4 conclusion. -/
theorem CentralComponentSetup.sylow_le_normalizer_of_normal
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  h.sylow_centralizes.trans ((normal_subgroupOf_iff_le_normalizer h.component.1).mp hn)

/-- The genuine index comparison in 16.2.3, assembling its conclusion from
an independently proved 16.1.8. The section owner must discharge `transfer`. -/
theorem CentralComponentSetup.component_of_small_index_of_transfer
    [Finite G] (h : CentralComponentSetup T z L) (transfer : SmallCentralizerIndexTransfer G)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ commutingSylow T L)
    (hindex : (involutionCentralizer t).relIndex (T : Subgroup G) ≤ 2) :
    IsCentralizerComponent t L := by
  obtain ⟨S, _, hS⟩ := T.exists_centralizer_sylow_with_index_le t z h.sylow_centralizes
  have hz : z ∈ involutionCentralizer t :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (h.sylow_centralizes htC.1)).symm
  have hLC : L ≤ involutionCentralizer t := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC.2 x hx)
  have hjoin : zpowers z ⊔ L ≤ involutionCentralizer t :=
    sup_le (zpowers_le.mpr hz) hLC
  exact transfer z t L h.involution ht h.component
    (mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hjoin hx))
    S (hS.trans hindex)

end CFSG.Quasithin.Chapter16
