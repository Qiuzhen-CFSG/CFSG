module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.NormalizedRootCentralizers

/-!
# The full highest-root centralizer in even G₂

The image of root-A minus the identity is the standard null plane. Its
centralizer therefore preserves that plane and belongs to the first
parabolic. In the local-times-Borel decomposition, centralizing a nonzero
root parameter forces the torus character to be one. That torus already
belongs to the first local group, giving the full centralizer equality.

Source: the local structure used in Aschbacher–Smith 14.7.68(2), p.1071,
and F.1.11–12, pp.262–264. The octonion coordinates and parabolic normal
forms come from the licensed ATLAS port (LICENSES/ATLAS.txt;
LICENSES/ATLAS-CITATION.cff).
-/

public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Subgroup
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem preserves_shortPlane_of_commute_rootA {a : F} (ha : a ≠ 0)
    (g : Model F) (hg : Commute g (rootA a)) (x : Carrier F) (hx : x ∈ shortPlane) :
    g.val x ∈ shortPlane := by
  let y : Carrier F := ![0,0,0,0,0,0,-(x 0 / a), x 1 / a]
  have hy : (rootA a).val y - y = x := by
    rw [shortPlane_coordinates hx]
    funext i
    fin_cases i <;> simp [y, rootA, rootAEquiv, rootALinear, rootAApply] <;> field_simp
  have he : g.val ((rootA a).val y) = (rootA a).val (g.val y) :=
    congrArg (fun h : Model F => h.val y) hg.eq
  rw [← hy, map_sub, he]
  intro i hi
  fin_cases i <;> simp_all [rootA, rootAEquiv, rootALinear, rootAApply]

theorem centralizer_rootA_eq_local₁ {a : F} (ha : a ≠ 0) :
    centralizer ({rootA a} : Set (Model F)) = local₁ := by
  apply le_antisymm ?_ (local₁_le_centralizer_rootA a)
  intro g hg
  have hc : Commute g (rootA a) := mem_centralizer_singleton_iff.mp hg
  have hp : g ∈ parabolic₁ := by
    rw [parabolic₁_eq_shortPlaneStabilizer]
    exact ⟨preserves_shortPlane_of_commute_rootA ha g hc,
      preserves_shortPlane_of_commute_rootA ha g⁻¹ hc.inv_left⟩
  change g ∈ (parabolic₁ (F := F) : Set (Model F)) at hp
  rw [parabolic₁_eq_local₁_mul_borel] at hp
  obtain ⟨l, hl, b, hb, he⟩ := hp
  change l * b = g at he
  obtain ⟨⟨u,t⟩, ht⟩ := borelProductEquiv.surjective ⟨b,hb⟩
  have hut : (u : Model F) * t = b := congrArg Subtype.val ht
  obtain ⟨⟨v,w⟩,hw⟩ := t.property
  change torus v w = (t : Model F) at hw
  have hlt : (l * u) * torus v w = g := by
    rw [hw, mul_assoc, hut, he]
  have hlu : l * u ∈ local₁ (F := F) := local₁.mul_mem hl (unipotent_le_local₁ u.property)
  have hluC : Commute (l * u) (rootA a) :=
    mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a hlu)
  have htC : Commute (torus v w) (rootA a) := by
    rw [← hlt] at hc
    simpa only [inv_mul_cancel_left] using hluC.inv_left.mul_left hc
  have hvw := (NormalizedRootCentralizers.torus_commute_rootA_iff v w ha).mp htC
  have hw' : w = v⁻¹ := eq_inv_of_mul_eq_one_right (Units.ext hvw)
  rw [← hlt, hw']
  exact local₁.mul_mem hlu (short_torus_mem_local₁ v)
end Atlas.G2.LieParabolicSetup
