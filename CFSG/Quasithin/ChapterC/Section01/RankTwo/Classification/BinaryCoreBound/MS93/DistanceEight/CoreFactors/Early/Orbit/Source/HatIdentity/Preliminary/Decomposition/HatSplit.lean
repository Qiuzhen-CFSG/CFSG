module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.HatSplit.FixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.HatSplit.NaturalIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.SourceWindows

/-!
# The source first-hat decomposition

The natural subgroup and natural quotient give fixed index at least 64 in
Vcirc. The actual hat action gives fixed index at most 64, after lifting
through its central H-kernel. Equality of indices makes Vcirc supplement
the fixed subgroup of the hat itself. The original four critical-path
windows instantiate every action bound.

This is the smaller-seed product used in the source rechoice argument.
It does not assert that the full radius splits, or that its full fixed
subgroup lies in a hat.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem hat_eq_moving_sup_fixed_of_actionBounds
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t)
    (bounds : ActionBounds common earlier w) :
    hatV R b a = Vcirc R b ⊔
      (hatV R b a ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R))) := by
  let G := stabilizer R b
  let := finite_stabilizer R b
  let A := localHat b a
  let V₀ := (V R b).subgroupOf G
  let K := pResidual 2 G
  let W := ⁅V₀,K⁆
  let C := A ⊓ centralizer (K : Set G)
  let : C.Normal := by dsimp only [C,K,A]; infer_instance
  have hVG : V R b ≤ G := (PathCentrality.V_le_Q R w.color_b common.large_distance).trans
    (fun _ hx => hx.1)
  have hwmap : W.map G.subtype = Vcirc R b := by
    rw [map_commutator,map_subgroupOf_eq_of_le hVG]; rfl
  have hWA : W ≤ A := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [hwmap,map_subgroupOf_eq_of_le (hat_le_local earlier w)]
    exact moving_le_hatV source earlier w.color_b w.moving
  have hcW : C.relIndex W = (centralizer (K : Set G)).relIndex W := by
    rw [← inf_relIndex_right C W]
    have he : C ⊓ W = centralizer (K : Set G) ⊓ W := by
      change (A ⊓ centralizer (K : Set G)) ⊓ W = _
      rw [inf_right_comm,inf_of_le_right hWA,inf_comm]
    rw [he,inf_relIndex_right]
  have hlow : 64 ≤ C.relIndex W := by
    rw [hcW]
    exact moving_fixed_index_ge64 common earlier w.color_b
  have hupp : C.relIndex A ≤ 64 := by
    change (A ⊓ centralizer (K : Set G)).relIndex A ≤ 64
    rw [inf_relIndex_left]
    exact hat_fixed_index_le64 common earlier w bounds
  have he : W ⊔ C = A := sup_eq_of_fixed_indices A W C hWA inf_le_left 64 hlow hupp
  have hCmap : C.map G.subtype =
      hatV R b a ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R)) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨hy.1,?_⟩
      rintro _ ⟨l,hl,rfl⟩
      exact congrArg Subtype.val (hy.2 l hl)
    · intro hx
      refine ⟨⟨x,hat_le_local earlier w hx.1⟩,⟨hx.1,?_⟩,rfl⟩
      intro l hl
      exact Subtype.ext (hx.2 l (mem_map_of_mem G.subtype hl))
  have hh := congrArg (Subgroup.map G.subtype) he
  rw [Subgroup.map_sup,hwmap,hCmap,map_subgroupOf_eq_of_le (hat_le_local earlier w)] at hh
  exact hh.symm

/-- The source hat is the product of its smaller moving seed and its own
residual-fixed subgroup. No full-radius fixed-part containment is asserted. -/
theorem hat_eq_moving_mul_fixed_of_actionBounds
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t)
    (bounds : ActionBounds common earlier w) :
    (hatV R b a : Set (FreeAmalgam R)) = (Vcirc R b : Set (FreeAmalgam R)) *
      (hatV R b a ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let C := hatV R b a ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R))
  let : IsElementaryAbelian 2 (hatV R b a) :=
    PathCentrality.localZSpan_elementary R w.color_b
      (by rw [SimpleGraph.dist_comm,w.moving.1]) (by rw [earlier.distance]; decide)
  have hmov := moving_le_hatV source earlier w.color_b w.moving
  have hn : Vcirc R b ≤ normalizer (C : Set (FreeAmalgam R)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : hatV R b a) ⟨x,hmov hx⟩)
  change (hatV R b a : Set (FreeAmalgam R)) = (Vcirc R b : Set (FreeAmalgam R)) * (C : Set (FreeAmalgam R))
  rw [← coe_mul_of_left_le_normalizer_right (Vcirc R b) C hn]
  exact congrArg (fun A : Subgroup (FreeAmalgam R) => (A : Set (FreeAmalgam R)))
    (hat_eq_moving_sup_fixed_of_actionBounds common earlier w bounds)
/-- The two forward first-hat products on the original source path. -/
theorem hat_split_forward
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    (hatV R (p.walk.getVert (i-2)) (p.walk.getVert i) : Set (FreeAmalgam R)) =
      (Vcirc R (p.walk.getVert (i-2)) : Set (FreeAmalgam R)) *
      (hatV R (p.walk.getVert (i-2)) (p.walk.getVert i) ⊓
        centralizer (Ltilde R (p.walk.getVert (i-2)) : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
  hat_eq_moving_mul_fixed_of_actionBounds common earlier
    (forwardWindow common earlier p hi hi4 hi6)
    (actionBounds_forward common earlier p hi hi4 hi6)

/-- The two backward first-hat products on the original source path. -/
theorem hat_split_backward
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    (hatV R (p.walk.getVert (i+2)) (p.walk.getVert i) : Set (FreeAmalgam R)) =
      (Vcirc R (p.walk.getVert (i+2)) : Set (FreeAmalgam R)) *
      (hatV R (p.walk.getVert (i+2)) (p.walk.getVert i) ⊓
        centralizer (Ltilde R (p.walk.getVert (i+2)) : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
  hat_eq_moving_mul_fixed_of_actionBounds common earlier
    (backwardWindow common earlier p hi hi8 hi10)
    (actionBounds_backward common earlier p hi hi8 hi10)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
