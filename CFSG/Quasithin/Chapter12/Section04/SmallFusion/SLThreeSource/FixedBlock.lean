module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockInputs
public import Theory.Frattini.CentralElementarySupplement

/-!
# Frattini elimination in the fixed-residual branch

The block identities give C_R(L₁)=E C_T(L). Since E is central elementary
in R, the Frattini subgroups of these two centralizers have the same
ambient image. The escaping normalizer preserves that image; L and T
also normalize it. The original uniqueness theorem therefore forces it
to vanish.

Now C_T(L) is elementary and central in C_T(V)=V C_T(L). The already
proved omega-center identity places it in V, yielding C_T(V)=V and
C_T(L)=C_V(L). This avoids an additional Sylow product calculation.
The two block identities remain explicit source inputs.

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The fixed-residual normalizer forces Φ(C_T(L))=1 from the actual
block centralizer identity. Normality in G is never assumed. -/
theorem fixedBlock_frattini
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hcentralizer : d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    frattini ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) = ⊥ := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := d.R ⊓ centralizer (d.L₁ : Set G)
  let F := (frattini C).map C.subtype
  have hTN := (structural G T L h).1
  have hLN : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mpr (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTN.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLTF : L ⊔ (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (sup_le hLN hTC).trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hNB : normalizer (d.R : Set G) ≤ normalizer (B : Set G) :=
    (le_inf le_rfl (hline.trans (normalizer_le_normalizer_centralizer d.L₁))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨_, _, hE, _, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hEB : d.E ≤ centralizer (B : Set G) := by
    rw [hE]
    intro x hx
    exact centralizer_le (show B ≤ d.R from inf_le_left)
      ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  let _ := D.elementary
  have hEp : IsElementaryAbelian 2 d.E := IsElementaryAbelian.of_le d.le_module
  have hBp : IsPGroup 2 B := T.isPGroup'.of_injective
    (inclusion (show B ≤ T from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hphi : (frattini B).map B.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement B C d.E hBp hEp hEB hcentralizer
  have hNF : normalizer (d.R : Set G) ≤ normalizer (F : Set G) := by
    rw [← hphi]
    exact hNB.trans (normalizer_le_normalizer_characteristic_image B (frattini B))
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTN
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [horbit] using hu.normalizer_unique N hN hLN
  have hFp : IsPGroup 2 F := T.isPGroup'.of_injective
    (inclusion ((map_subtype_le (frattini C)).trans inf_le_left)) (inclusion_injective _)
  have hF : F = ⊥ := by
    by_contra hF
    exact hescape (hNF.trans (normalizer_le_of_unique_maximalTwoLocal
      hunique hFp hF hLTF))
  exact ((frattini C).map_eq_bot_iff_of_injective C.subtype_injective).mp hF

/-- Apply Frattini elimination and the omega supplement to the source
product: the original V is self-centralizing in T. -/
theorem fixedBlock_selfCentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hproduct : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hcentralizer : d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = fixedSubgroup L V := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hphi := fixedBlock_frattini h structural marked hmodel hne d hescape hline hcentralizer
  let _ : Fact (IsPGroup 2 C) := ⟨T.isPGroup'.of_injective
    (inclusion (show C ≤ T from inf_le_left)) (inclusion_injective _)⟩
  let _ : IsElementaryAbelian 2 C := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hprod : Q = V ⊔ C := hproduct
  have hCQ : C ≤ Q := by
    rw [hprod]
    exact le_sup_right
  have hCQc : C ≤ centralizer (Q : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hprod]
    exact sup_le (le_centralizer_iff.mp (hCQ.trans inf_le_right)) C.le_centralizer
  have hCo : C ≤ omegaCenterIn Q := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hCQ hx, hCQc hx, elemPow_eq_one_of_isElementaryAbelian x hx⟩
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have ho : omegaCenterIn Q = V := by
    change omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) = V
    rw [d.fixed_supplement, hZ, inf_eq_left.mpr
      (show fixedSubgroup L V ≤ centralizer (L : Set G) from inf_le_right),
      sup_eq_right.mpr (show fixedSubgroup L V ≤ V from inf_le_left)]
  have hCV : C ≤ V := ho ▸ hCo
  refine ⟨hproduct.trans (sup_eq_left.mpr hCV), le_antisymm (le_inf hCV inf_le_right) ?_⟩
  exact le_inf (inf_le_left.trans D.le_sylow) inf_le_right

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
