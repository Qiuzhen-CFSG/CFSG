module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Model

/-!
# Two explicit planes in the G₂ point-residual orbit

The point residual preserves the marked line and third space. The standard
plane and its image under the long Weyl generator meet in that line and span
that third space. These calculations use the literal six-dimensional
quotient of trace-zero octonions and feed the ambient incidence transport.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765.
The octonion and root APIs are from the attributed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS source is copied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
open Atlas.G2.Restricted.NaturalCoordinates
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem coord_act (g : Model F) (x : Natural.Space F) :
    coord F (Natural.action F g x) = Restricted.NaturalCoordinates.action F g (coord F x) :=
  LinearMap.congr_fun ((repEquiv F).isIntertwining' g) x

/-- The source point residual preserves the literal third space. -/
theorem local₂_three_invariant : local₂ (F := F) ≤ stabilizer F (naturalThreeSpace F) := by
  apply sup_le
  · apply le_subspaceStabilizer
    intro g hg x hx
    change Natural.action F g x ∈ naturalThreeSpace F
    have hd := naturalPlane_le_naturalThreeSpace F
      (unipotent_displacement_mem_plane F g hg x hx)
    simpa only [sub_add_cancel] using (naturalThreeSpace F).add_mem hd hx
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    have he : g = weylR := Set.mem_singleton_iff.mp hg
    subst g
    change ∀ x, Natural.action F weylR x ∈ naturalThreeSpace F ↔
      x ∈ naturalThreeSpace F
    intro x
    rw [mem_naturalThreeSpace, mem_naturalThreeSpace, coord_act, action_weylR]
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨hb,ha,hc⟩

/-- Every point-residual translate of the plane lies in the source interval. -/
theorem local₂_plane_interval (g : Model F) (hg : g ∈ local₂) :
    N1 F ≤ (naturalPlane F).map (Natural.action F g) ∧
      (naturalPlane F).map (Natural.action F g) ≤ naturalThreeSpace F := by
  constructor
  · intro x hx
    have hle : local₂ (F := F) ≤ parabolic₂ :=
      (show local₂ (F := F) ≤ local₂ ⊔ borel from le_sup_left).trans_eq local₂_sup_borel
    have hi : g⁻¹ ∈ stabilizer F (N1 F) :=
      (point_stabilizer F).symm ▸ hle (inv_mem hg)
    refine ⟨Natural.action F g⁻¹ x, N1_le_naturalPlane F ((hi x).mpr hx), ?_⟩
    exact (Natural.action F).self_inv_apply g x
  · rintro _ ⟨x,hx,rfl⟩
    exact ((local₂_three_invariant F hg) x).mpr
      (naturalPlane_le_naturalThreeSpace F hx)

omit [Algebra (ZMod 2) F] in
/-- The Weyl-conjugate plane meets the standard plane in the marked line. -/
theorem plane_inf_weylR : naturalPlane F ⊓
    (naturalPlane F).map (Natural.action F weylR) = N1 F := by
  apply le_antisymm
  · rintro x ⟨hx,hy⟩
    obtain ⟨a,b,he⟩ := (mem_naturalPlane F x).mp hx
    obtain ⟨y,hy,rfl⟩ := hy
    obtain ⟨c,d,hc⟩ := (mem_naturalPlane F y).mp hy
    have hd : b = 0 := by
      have hh := congrFun he 1
      rw [coord_act, action_weylR, hc] at hh
      exact hh.symm
    apply (mem_N1 F _).mpr
    exact ⟨a, by simpa [hd] using he⟩
  · intro x hx
    refine ⟨N1_le_naturalPlane F hx, ?_⟩
    obtain ⟨a,ha⟩ := (mem_N1 F x).mp hx
    refine ⟨x,N1_le_naturalPlane F hx,?_⟩
    apply (coord F).injective
    rw [coord_act, action_weylR, ha]
    rfl

omit [Algebra (ZMod 2) F] in
/-- The two explicit planes span the literal third space. -/
theorem plane_sup_weylR : naturalPlane F ⊔
    (naturalPlane F).map (Natural.action F weylR) = naturalThreeSpace F := by
  apply le_antisymm
  · apply sup_le (naturalPlane_le_naturalThreeSpace F)
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,b,ha⟩ := (mem_naturalPlane F x).mp hx
    rw [mem_naturalThreeSpace, coord_act, action_weylR, ha]
    exact ⟨rfl,rfl,rfl⟩
  · intro x hx
    obtain ⟨h3,h4,h5⟩ := hx
    let y := (coord F).symm ![coord F x 0,coord F x 1,0,0,0,0]
    let z := (coord F).symm ![0,coord F x 2,0,0,0,0]
    have hy : y ∈ naturalPlane F :=
      (mem_naturalPlane F y).mpr ⟨_,_,(coord F).apply_symm_apply _⟩
    have hz : z ∈ naturalPlane F :=
      (mem_naturalPlane F z).mpr ⟨_,_,(coord F).apply_symm_apply _⟩
    have he : x = y + Natural.action F weylR z := by
      apply (coord F).injective
      rw [map_add, coord_act, action_weylR]
      simp only [y,z,LinearEquiv.apply_symm_apply]
      ext i
      fin_cases i <;> simp [h3,h4,h5]
    rw [he]
    exact (naturalPlane F ⊔ (naturalPlane F).map (Natural.action F weylR)).add_mem
      ((show naturalPlane F ≤ naturalPlane F ⊔ (naturalPlane F).map (Natural.action F weylR) from le_sup_left) hy)
      ((show (naturalPlane F).map (Natural.action F weylR) ≤ naturalPlane F ⊔ (naturalPlane F).map (Natural.action F weylR) from le_sup_right) (Submodule.mem_map.mpr ⟨z,hz,rfl⟩))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
