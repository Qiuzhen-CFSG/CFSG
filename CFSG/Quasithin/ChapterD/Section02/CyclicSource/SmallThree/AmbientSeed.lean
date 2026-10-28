module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportNormal
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.SeededInverter
public import Theory.Representation.BinaryOffender.NormalProjectedSeed

/-!
# The ambient generating seed in the small-three fixed complement

For a normal subgroup H of the original acting group G, the canonical cubic
support group of H is normal in G after its literal inclusion. Coprime
projection of G's Sylow-fixed orbit-generating seed excludes the two-core of
the ambient fixed-complement image. Normality passes this to the image of H.
The residual cubic mover then proves D.2.25's fixed-complement conclusion for
H without requiring the seed to span under H or prior full Fitting movement.

Source: Aschbacher--Smith D.2.25, printed p.190, as used for the original Jhat
in 15.1.2, printed pp.1084--1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]

omit [Group.IsSolvable G] [FiniteDimensional (ZMod 2) V] in
theorem CoreHypotheses.smallThree_residual_twoCore_of_ambient_seed
    (h : CoreHypotheses (ρ.comp H.subtype))
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤) :
    letI := BinaryGroupAction.action (ρ.comp H.subtype)
    let Y := smallSupportGroup H (Multiplicative V) 1
    pCore 2 (subspaceActionImage (ρ.comp H.subtype)
      (fixedSpace (ρ.comp H.subtype) Y))=⊥ := by
  let := BinaryGroupAction.action ρ
  let σ := ρ.comp H.subtype
  let Y := smallSupportGroup H (Multiplicative V) 1
  let B := Y.map H.subtype
  let : B.Normal := smallSupportGroup_map_normal H 1
  have hodd : Odd (Nat.card Y) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore).of_dvd_nat
      (Subgroup.card_dvd_of_le (smallSupportGroup_le_fitting H (Multiplicative V) 1))
  have hBodd : Odd (Nat.card B) := by
    rw [card_map_of_injective H.subtype_injective]
    exact hodd
  have hc := normalOddFixed_subgroupImage_twoCore ρ H B hBodd S Z hfix hspan
  change pCore 2 (subspaceActionImage σ (fixedSpace σ Y))=⊥
  rw [fixedSpace_comp_map]
  exact hc

theorem CoreHypotheses.fixed_smallThree_complement_of_ambient_seed
    (h : CoreHypotheses (ρ.comp H.subtype))
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤)
    (hfive : ∀ A∈QhatStar (ρ.comp H.subtype),⁅pCore 5 H,A⁆=⊥)
    (hq : cubicRatio (ρ.comp H.subtype)=2) {t : H}
    (ht : t∈smallSupportInvolutions (ρ.comp H.subtype)) :
    letI := BinaryGroupAction.action (ρ.comp H.subtype)
    let Y := smallSupportGroup H (Multiplicative V) 1
    t∉centralizer (Y:Set H) → fixedSpace (ρ.comp H.subtype) Y ≤
      fixedSpace (ρ.comp H.subtype) (zpowers t) := by
  exact h.fixed_smallThree_complement_of_residual_twoCore
    (ρ.comp H.subtype) hfive hq ht
    (h.smallThree_residual_twoCore_of_ambient_seed ρ H S Z hfix hspan)
end CFSG.Quasithin.ChapterD.CyclicSource
