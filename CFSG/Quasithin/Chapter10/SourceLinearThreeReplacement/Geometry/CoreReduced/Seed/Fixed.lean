module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Inputs
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl

/-!+# The diagonal centralizer fixes both original coordinates

The two-residual L₀ normalizes L, hence preserves its moved factor V₁.
Conjugating by the specified exchange gives the same assertion for V₂.
Since V₁ ∩ V₂ = 1, an element of L₀ fixing ab fixes a and b separately.
Thus the whole C_{L₀}(ab), and in particular its two-residual X, centralizes E.

Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- The original orbit preserves the first moved factor. -/
theorem orbit_normalizes_moved (s : SourceLinearThreeSurvivor T D) :
    localOrbit T L ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule ((localOrbit T L).le_normalizer hg)),
    mem_normalizer_iff_map_conj_eq.mp
      (source_nonnormal_orbit_le_normalizer D (survivor_nonnormal s) hg)]

/-- Conjugating the orbit invariance gives invariance of the partner. -/
theorem orbit_normalizes_partner (s : SourceLinearThreeSurvivor T D) :
    localOrbit T L ≤ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  have he : (localOrbit T L).map (MulAut.conj s.exchange).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T s.exchange_mem)
  rw [← he]
  exact (map_mono (orbit_normalizes_moved s)).trans
    ((⁅D.fullModule,L⁆ : Subgroup G).le_normalizer_map (MulAut.conj s.exchange).toMonoidHom)

/-- Fixing the product in the two disjoint original factors fixes each coordinate. -/
theorem centralizer_fixes (c : Configuration s a b) :
    localOrbit T L ⊓ centralizer ({a*b} : Set G) ≤
      centralizer ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  have hd : Disjoint A B := survivor_pair_disjoint s c.fixed
  intro g hg
  have ha : (MulAut.conj g) a ∈ A :=
    (mem_normalizer_iff.mp (orbit_normalizes_moved s hg.1) a).mp c.first_mem
  have hb : (MulAut.conj g) b ∈ B :=
    (mem_normalizer_iff.mp (orbit_normalizes_partner s hg.1) b).mp c.second_mem
  have he : (MulAut.conj g) a * (MulAut.conj g) b = a*b := by
    rw [← map_mul]
    change g*(a*b)*g⁻¹ = a*b
    rw [mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
  have hp : ((⟨(MulAut.conj g) a,ha⟩ : A), (⟨(MulAut.conj g) b,hb⟩ : B)) =
      (⟨a,c.first_mem⟩,⟨b,c.second_mem⟩) := mul_injective_of_disjoint hd he
  have hga : g*a*g⁻¹ = a := congrArg (fun p : A × B => (p.1 : G)) hp
  have hgb : g*b*g⁻¹ = b := congrArg (fun p : A × B => (p.2 : G)) hp
  have hE : zpowers a ⊔ zpowers b ≤ centralizer ({g} : Set G) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hga).symm
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgb).symm
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hE hx))

/-- The fourth SeedAnalysis field, with no additional local-model premise. -/
theorem fixes (c : Configuration s a b) :
    centralizerSeed T L (a*b) ≤
      centralizer ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) :=
  (map_subtype_le _).trans (centralizer_fixes c)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
