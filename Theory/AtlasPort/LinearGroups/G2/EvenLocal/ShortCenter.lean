module
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.NormalizedRootCentralizers

/-!
# The full short G₂ parabolic has trivial center

A central element lies in the self-centralizing five-root radical and
therefore in its highest-root center. The full split torus acts on that
root parameter by the character `(l,m) ↦ l*m`. Over a field with more than
two elements this character has a nonidentity value, forcing a central
parameter to vanish.

Source: the full-parabolic structure in Aschbacher--Smith F.1.12(I)(3),
printed pp.262--264. The imported root-coordinate calculations retain their
ATLAS attribution; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Atlas.G2.LieParabolicSetup
namespace Atlas.G2.EvenLocal
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full short parabolic has trivial center over every nonbinary finite
field of characteristic two. -/
theorem parabolic₁_center_eq_bot (hq : 2 < Nat.card F) :
    center (parabolic₁ (F := F)) = ⊥ := by
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨c,hc⟩ := exists_ne (1 : Fˣ)
  apply bot_unique
  intro z hz
  have hR : radical₁ (F := F) ≤ parabolic₁ :=
    (fiveRootSubgroup_le_unipotent _ _).trans
      ((show unipotent ≤ borel from le_sup_left).trans borel_le_parabolic₁)
  have hzR : z.val ∈ radical₁ (F := F) :=
    short_radical_selfCentralizing (center_le_centralizer _ hz)
  have hzA : z.val ∈ highestRoot (F := F) := by
    rw [←center_map_eq_highestRoot (radical₁ (F := F)) le_rfl
      (fiveRootSubgroup_le_unipotent _ _)]
    refine ⟨⟨z.val,hzR⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
    apply Subtype.ext
    exact congrArg (fun g : parabolic₁ (F := F) => g.val)
      (mem_center_iff.mp hz ⟨r.val,hR r.property⟩)
  obtain ⟨a,ha⟩ := hzA
  have ha0 : a.toAdd = 0 := by
    by_contra hne
    have ht : torus c 1 ∈ parabolic₁ (F := F) :=
      borel_le_parabolic₁ (mem_sup_right ⟨(c,1),rfl⟩)
    have hcomm : Commute (torus c 1) (rootA a.toAdd) := by
      change rootA a.toAdd = z.val at ha
      rw [ha]
      exact congrArg (fun g : parabolic₁ (F := F) => g.val)
        (mem_center_iff.mp hz ⟨torus c 1,ht⟩)
    have he := (NormalizedRootCentralizers.torus_commute_rootA_iff c 1 hne).mp hcomm
    apply hc
    apply Units.ext
    simpa only [Units.val_one,mul_one] using he
  apply mem_bot.mpr
  apply Subtype.ext
  change rootA a.toAdd = z.val at ha
  rw [←ha,ha0,rootA_zero]
  rfl

end Atlas.G2.EvenLocal
