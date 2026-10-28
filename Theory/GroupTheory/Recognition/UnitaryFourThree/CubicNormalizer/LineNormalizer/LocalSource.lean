module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.LocalCentralizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Source

/-!
# Original-source reflected-line local geometry

The original root pair supplies the positioned reflection marking, including
its actual quaternion-factor interchange.  The fixed-core and local-normalizer
calculations therefore apply without extra hypotheses.  The original plane,
Sylow image, both reflections, and all subgroup maps are retained for the
independent A₆-plane calculation and the global U-line normalizer argument.

Source: Aschbacher, *Sporadic Groups* (1994),45.7(1),(3),printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A genuine positioned cubic line with its local centralizer and normalizer. -/
theorem exists_reflected_line_local_geometry (R : RootPair z) (h : IsType z)
    (P : Sylow 3 (centralizer z)) :
    let X := (P : Subgroup (centralizer z)).map (centralizer z).subtype
    ∃ m : CubicNormalizer.ReflectedMarking z X, ∃ A : Subgroup G,
      (A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) ∧
      m.t∈A ∧ m.t∈R.cubicSylow X ∧ m.s∈R.cubicSylow X ∧
      R.cubicSylow X≤normalizer (A:Set G) ∧
      core z ⊓ Subgroup.centralizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G) : Subgroup G):Set G)=zpowers z ∧
      centralizer z ⊓ Subgroup.centralizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G) : Subgroup G):Set G)≤normalizer (X:Set G) ∧
      centralizer z ⊓ normalizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G) : Subgroup G):Set G)=
          centralizer z ⊓ normalizer (X:Set G) ∧
      Nat.card (centralizer z ⊓ normalizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G) : Subgroup G):Set G) : Subgroup G)=72 := by
  dsimp only
  obtain ⟨m,A,hA,htA,ht,hs,hTN,htB,htC⟩ := R.exists_positioned_reflected_marking h
    ((P : Subgroup (centralizer z)).map (centralizer z).subtype)
    (h.cubic_sylow_image_card P) (map_subtype_le _)
  exact ⟨m,A,hA,htA,ht,hs,hTN,h.reflected_line_core_centralizer P m htB htC,
    h.reflected_line_centralizer_le P m htB htC,
    h.reflected_line_normalizer_eq P m htB htC,
    h.reflected_line_local_normalizer_card P m htB htC⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
