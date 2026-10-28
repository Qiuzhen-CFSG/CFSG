module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Section
public import Theory.GroupTheory.CComponent.CentralizerMovement

/-!
# The point residual inside the omega-center normalizer

Control of the whole fixed center gives C_G(Z₁) ≤ N_G(L).
The preceding fixed-line action makes L₁ centralize Z₁ and normal in
C_G(Z₁). Its intrinsic C-component property therefore persists in N_G(Z₁).
The genuine two-component orbit bound, together with the original Sylow
subgroup T, makes L₁ normal in N_G(Z₁), hence normalized by Y=N_G(R₁).

This proves the component step in the exceptional GO argument without
assuming uniqueness over L. The retained rank-one quotient and fixed-line
identities belong to qt-d-1222-natural-flag-cartan; the normalizer-source
parent owns their final discharge. The last consumer removes L₁ normalization
from the Sp₄ terminal contradiction. Its V₃ action and the remaining
centralizer and block arguments stay with qt-d-1222-natural-point-fixed-summand.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766, using 1.2.1(3).
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Centralizer control for the whole omega center only needs the whole
fixed center, whose normalizer is already controlled by uniqueness over LT. -/
theorem omegaCenter_centralizer_le
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    centralizer (radicalOmegaCenter (f.Ri 0) : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_le (show radicalFixedCenter (f.Ri 0) L ≤ radicalOmegaCenter (f.Ri 0)
    from inf_le_left)).trans ((Subgroup.centralizer_le_normalizer _).trans
      (chosen_fixed_normalizer_le D S f hne))

/-- The point residual centralizes both summands in the corrected center identity. -/
theorem first_centralizes_omegaCenter
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    f.Li 0 ≤ centralizer (radicalOmegaCenter (f.Ri 0) : Set G) := by
  apply le_centralizer_iff.mpr
  rw [hcenter]
  exact sup_le (le_centralizer_iff.mp hfix)
    (inf_le_right.trans (centralizer_le ((localResidual_le _).trans inf_le_left)))

/-- The actual residual is a component of the omega-center normalizer. -/
theorem first_component_in_omegaCenter_normalizer
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    Source.ComponentIn (normalizer (radicalOmegaCenter (f.Ri 0) : Set G)) (f.Li 0) := by
  let C := centralizer (radicalOmegaCenter (f.Ri 0) : Set G)
  let A := f.Li 0
  have hAC : A ≤ C := first_centralizes_omegaCenter D S f hfix hcenter
  have hCline : C ≤ normalizer (f.Vi 0 : Set G) :=
    (centralizer_le (show f.Vi 0 ≤ radicalOmegaCenter (f.Ri 0) from
      hcenter ▸ le_sup_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hCA : C ≤ normalizer (A : Set G) :=
    ((le_inf (omegaCenter_centralizer_le D S f hne)
      (hCline.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hlocal := Components.flag_mem_local_of_model D S f 0 hm
  have htop : (⊤ : Subgroup A).IsCComponent := by
    have hh := hlocal.1.subgroupOf_of_le (K := A) le_rfl le_sup_left
    change (A.subgroupOf A).IsCComponent at hh
    simpa only [subgroupOf_self] using hh
  have hACcomp : (A.subgroupOf C).IsCComponent := by
    let e : A ≃* A.subgroupOf C := (subgroupOfEquivOfLe hAC).symm
    have ht : (⊤ : Subgroup (A.subgroupOf C)).IsCComponent := by
      have he : (⊤ : Subgroup A).map e.toMonoidHom = ⊤ :=
        (MonoidHom.range_eq_map e.toMonoidHom).symm.trans
          (MonoidHom.range_eq_top.mpr e.surjective)
      exact he ▸ htop.map_equiv e
    have hn : (A.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hAC).mpr hCA
    simpa only [← MonoidHom.range_eq_map, range_subtype] using ht.map_subtype hn.isSubnormal
  exact ⟨hAC.trans (Subgroup.centralizer_le_normalizer _),
    hACcomp.in_normalizer_of_centralizes hAC le_rfl⟩

/-- T-invariance eliminates the two-component orbit in the actual omega-center normalizer. -/
theorem omegaCenter_normalizer_normalizes_first
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (radicalOmegaCenter (f.Ri 0) : Set G) ≤ normalizer (f.Li 0 : Set G) := by
  let Z := radicalOmegaCenter (f.Ri 0)
  let Y := normalizer (Z : Set G)
  let A := (f.Li 0).subgroupOf Y
  have hTZ : (T : Subgroup G) ≤ Y :=
    (sylow_normalizes_Ri f 0).trans (normalizes_omegaCenter _)
  let P : Sylow 2 Y := T.subtype hTZ
  have hZne : Z ≠ ⊥ := by
    intro hz
    change radicalOmegaCenter (f.Ri 0) = ⊥ at hz
    exact hne (bot_unique (inf_le_left.trans_eq hz))
  have htwo : IsTwoLocal Y := ⟨Z, hZne,
    IsElementaryAbelian.isPGroup 2 Z, rfl⟩
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (S.source.simpleQTKE.twoLocal_sqtk htwo) (pCore 2 Y) pCore_isPGroup
  have hA := first_component_in_omegaCenter_normalizer D S f hm hfix hcenter hne
  have hPA : (P : Subgroup Y) ≤ normalizer (A : Set Y) := by
    rw [← subgroupOf_normalizer_eq hA.1]
    exact comap_mono (f.sylow_normalizes_Li 0)
  have hn : A.Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hA.2 with hn | hi
    · exact hn
    · change (normalizer (A : Set Y)).index = 2 at hi
      exact (P.not_dvd_index (by simpa only [hi] using index_dvd_of_le hPA)).elim
  exact (normal_subgroupOf_iff_le_normalizer hA.1).mp hn

/-- The point-radical normalizer preserves the original first residual. -/
theorem radical_normalizer_normalizes_first
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Li 0 : Set G) :=
  (normalizes_omegaCenter _).trans
    (omegaCenter_normalizer_normalizes_first D S f hm hfix hcenter hne)

/-- The exceptional GO action supplies nontriviality of the fixed center.
Thus the actual Y normalizes L₁, without uniqueness over L or a new
centralizer-control premise. -/
theorem chosen_exceptional_normalizes_first
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Li 0 : Set G) := by
  apply radical_normalizer_normalizes_first D S f hm hfix hcenter
  intro hz
  have hc := (chosen_exceptional_parameters D S f X hcenter hfixed he).2.2
  rw [hz, card_bot] at hc
  omega

/-- The Sp₄ terminal contradiction now needs only preservation of the
literal third subspace: normalization of L₁ is proved here. The remaining
block action is retained by this task, and source 11.1.4 by the normalizer
assembly owner. -/
theorem chosen_exceptional_escape_of_third_invariance
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcontrol : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)))
    (hthird : normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Vi 2 : Set G)) : False :=
  exceptional_escape_contradiction D S f hescape hcontrol
    (Or.inr (le_inf hthird
      (chosen_exceptional_normalizes_first D S f hm hfix X hcenter hfixed he)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
