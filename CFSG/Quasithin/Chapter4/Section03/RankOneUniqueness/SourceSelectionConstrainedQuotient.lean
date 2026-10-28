module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionContaining
public import Theory.GroupTheory.CComponent.FittingNormalizerQuotient
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity

/-!
# The actual containing-component two-core quotient

C.2.11 puts the Fitting preimage of H/O₂(H) inside H ∩ N_G(L).
Normality of K carries its own Fitting preimage into that of H, so it
normalizes the original L inside K. The Fitting-normalizer criterion then
makes K/O₂(K) quasisimple. Both quotient transports use the original
inclusions; no full-module or block-module identification is required.

This discharges the constrained quotient premise in the aligned constructor.
In fact the argument does not require the constrained hypothesis. The
ordinary full-normalizer identification remains with this source assembly.

Source: Aschbacher–Smith C.2.11, p.148, and 4.2.12/4.3.2, pp.610–613.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The same normal containing C-component has quasisimple two-core quotient. -/
theorem OutsideChoice.component_quotient_of_normal
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (c : OutsideChoice T L) (K : Subgroup c.H) (hK : K.IsCComponent)
    (hLK : L ≤ K.map c.H.subtype) (hKN : K.Normal) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := hKN
  let B := L.subgroupOf c.H
  have hBK : B ≤ K := by
    apply (map_le_map_iff_of_injective c.H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le c.contains]
    exact hLK
  let A := B.subgroupOf K
  let e : A ≃* L := (subgroupOfEquivOfLe hBK).trans (subgroupOfEquivOfLe c.contains)
  have hA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := h.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
  apply quasisimple_quotient_of_fitting_normalizes htop A hA
  rw [← subgroupOf_normalizer_eq hBK, ← subgroupOf_normalizer_eq c.contains]
  intro x hx
  exact ((c.c28 D h).fitting_preimage_le
    (twoFittingCore_map_subtype_le_of_normal K (mem_map_of_mem K.subtype hx))).2

/-- The constrained quotient premise is discharged in the original aligned selection. -/
theorem exists_sourceConfiguration_of_ordinary_normalizer
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hordinary : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_component_branches D h hpsl hordinary ?_ hnot
  intro c K hK hLK _ hKN _
  exact c.component_quotient_of_normal D h K hK hLK hKN

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
