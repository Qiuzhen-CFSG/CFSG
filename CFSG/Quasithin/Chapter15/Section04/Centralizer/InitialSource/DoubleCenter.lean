module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.AlphaGeometry.FromInput
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.Coordinates

/-!
# Central hyperplanes from the actual double-factor action

The source input constructs the two residual factors. Their Baumann fixed
subgroups have order two by the proved Thompson decomposition, and the
original Sylow swap induces a literal binary quotient of the Thompson center.
Restricting to the central omega subgroup gives its fixed hyperplane. Two
distinct unique local overgroups then give the order-four center and its
nontrivial fixed lines, once the earlier small-center case is excluded.

Source: Aschbacher--Smith, 15.4.12(6) and 15.4.14, pp.1160--1161.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
open TwoFactors
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

/-- Construct the binary quotient, including its literal kernel and Sylow
coordinate swap, on the same source-produced pair. -/
theorem Pair.source_swappedBinaryQuotient (p : Pair T M X) (h : Input κ T M X 2) :
    Nonempty (SwappedBinaryQuotient (ChapterB.thompsonAlpha (T : Subgroup G))
      (T : Subgroup G) X) := by
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let S := ChapterB.baumann (T : Subgroup G)
  let C := E ⊓ centralizer (X : Set G)
  let V := p.quotient.moduleFactor
  let : IsElementaryAbelian 2 E := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hg := source_thompsonGeometry h
  have ha := p.factor_actions_thompson h hg (show S ≤ T from inf_le_left) (p.baumann false)
  dsimp only at ha
  rw [p.quotient.factor_generate h] at ha
  obtain ⟨hVS, hnV, hVne, hcomm, hdis, hCdis, hdecomp, hindex, _, hfree⟩ := ha
  have hcards := fixed_lines_of_index_four (T.isPGroup'.to_le (show S ≤ T from inf_le_left))
    (hVS false) (hVS true) (hnV false) (hnV true) (hVne false) (hVne true)
    hcomm hdis hCdis hdecomp hindex
  have hEC : E ≤ centralizer (S : Set G) := le_centralizer_iff.mp (show S ≤ centralizer (E : Set G) from inf_le_right)
  have hCW : C ≤ centralizer ((V false ⊔ V true : Subgroup G) : Set G) :=
    inf_le_left.trans (hEC.trans (centralizer_le (sup_le (hVS false) (hVS true))))
  obtain ⟨t, ht, hs₁, hs₂, _⟩ := p.quotient.interchange
  change (p.quotient.factor false).map (MulAut.conj t).toMonoidHom = p.quotient.factor true at hs₁
  change (p.quotient.factor true).map (MulAut.conj t).toMonoidHom = p.quotient.factor false at hs₂
  have hnE : t ∈ normalizer (E : Set G) :=
    normalizer_le_normalizer_thompsonAlpha _ ((T : Subgroup G).le_normalizer ht)
  have hnS : t ∈ normalizer (S : Set G) :=
    Stellmacher.normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht)
  have hnC : t ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hnE,
      normalizer_le_normalizer_centralizer X (YFamily.invariant h.member ht)⟩
  have hv : (localV T M).map (MulAut.conj t).toMonoidHom = localV T M :=
    mem_normalizer_iff_map_conj_eq.mp (localV_normalized _ _ (h.sylow_le ht))
  have hsw₁ : (V false).map (MulAut.conj t).toMonoidHom = V true := by
    change (⁅localV T M, p.quotient.factor false⁆).map _ = ⁅localV T M, p.quotient.factor true⁆
    rw [map_commutator, hv, hs₁]
  have hsw₂ : (V true).map (MulAut.conj t).toMonoidHom = V false := by
    change (⁅localV T M, p.quotient.factor true⁆).map _ = ⁅localV T M, p.quotient.factor false⁆
    rw [map_commutator, hv, hs₂]
  exact (swappedBinaryQuotient_of_module_factors hdecomp hCdis hdis hCW hcomm
    (show C ≤ centralizer (X : Set G) from inf_le_right) hfree
    (hnV false) (hnV true) hcards.1 hcards.2 t ht hnE hnC hnS hsw₁ hsw₂).2

/-- The original double-module input supplies the coordinate witness. -/
theorem source_swappedBinaryQuotient (h : Input κ T M X 2) :
    Nonempty (SwappedBinaryQuotient (ChapterB.thompsonAlpha (T : Subgroup G))
      (T : Subgroup G) X) :=
  (exists_pair h).elim fun p => p.source_swappedBinaryQuotient h

/-- The fixed subgroup in the actual central omega subgroup is a hyperplane;
no coordinate or central nontriviality premise is required. -/
theorem source_double_hyperplane (h : Input κ T M X 2) :
    (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  obtain ⟨d⟩ := source_swappedBinaryQuotient h
  apply centralizer_index_two_of_swapped_quotient d (centralOmega_le_thompsonAlpha _)
  · intro t ht z hz
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  · intro hc
    have hXT : X ≤ (T : Subgroup G) := (le_centralizer_iff.mp hc).trans_eq h.center_centralizer
    have hp : IsPGroup 2 X := T.isPGroup'.of_injective (inclusion hXT) (inclusion_injective hXT)
    exact member_core_ne_top _ h.member (top_unique (le_sSup ⟨inferInstance,
      hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm⟩))

/-- Source 15.4.14 for the actual double pair. The separate earlier
small-center exclusion is retained as the sole cardinality input. -/
theorem source_double_center_geometry {M₁ M₂ Y : Subgroup G}
    (hX : Input κ T M₁ X 2) (hY : Input κ T M₂ Y 2)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hlarge : 2 < Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
    Nat.card Z = 4 ∧ Group.rank Z = 2 ∧ primeRank 2 Z = 2 ∧
      (Nat.card (Z ⊓ centralizer (X : Set G) : Subgroup G) = 2 ∧ Z ⊓ centralizer (X : Set G) ≠ ⊥) ∧
      (Nat.card (Z ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ∧ Z ⊓ centralizer (Y : Set G) ≠ ⊥) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hc := card_eq_four_of_unique_hyperplanes hTZ huniqueX huniqueY hne
    (source_double_hyperplane hX) (source_double_hyperplane hY) hlarge
  obtain ⟨hr, hp⟩ := rank_eq_two_of_card_four Z hc
  exact ⟨hc, hr, hp, centralizer_card_two_of_hyperplane hc (source_double_hyperplane hX),
    centralizer_card_two_of_hyperplane hc (source_double_hyperplane hY)⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
