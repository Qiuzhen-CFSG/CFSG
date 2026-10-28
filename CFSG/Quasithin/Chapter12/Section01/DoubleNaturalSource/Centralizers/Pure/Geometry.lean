module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionImage
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceAssembly

/-!
# The three vector classes on the original doubled orbit

The natural and dual subgroups below are the supplied coordinate summands,
embedded in G. The H.9 orbit theorem is transported through the actual
normalizer action quotient, retaining the ambient conjugating element.
The pure fixed-line Sylow calculation is also lifted to its full preimage;
it asserts Sylow control in the normalizer, not yet in G.

Source: Aschbacher--Smith H.9.1 and 12.1.4--6, printed pp.390,790--792.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

def naturalSummand : Subgroup G :=
  B.naturalSpace.toAddSubgroup.toSubgroup'.map (componentOrbit V (T : Subgroup G)).subtype

def dualSummand : Subgroup G :=
  B.dualSpace.toAddSubgroup.toSubgroup'.map (componentOrbit V (T : Subgroup G)).subtype

theorem naturalSummand_le : B.naturalSummand ≤ componentOrbit V (T : Subgroup G) :=
  map_subtype_le _

theorem dualSummand_le : B.dualSummand ≤ componentOrbit V (T : Subgroup G) :=
  map_subtype_le _

@[simp] theorem mem_naturalSummand (w : componentOrbit V (T : Subgroup G)) :
    (w : G) ∈ B.naturalSummand ↔ (B.coordinates w).toAdd.2 = 0 := by
  change (w : G) ∈ B.naturalSpace.toAddSubgroup.toSubgroup'.map
    (componentOrbit V (T : Subgroup G)).subtype ↔ _
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = w := Subtype.ext he
    subst u
    exact hu
  · intro hp
    exact ⟨w, hp, rfl⟩

@[simp] theorem mem_dualSummand (w : componentOrbit V (T : Subgroup G)) :
    (w : G) ∈ B.dualSummand ↔ (B.coordinates w).toAdd.1 = 0 := by
  change (w : G) ∈ B.dualSpace.toAddSubgroup.toSubgroup'.map
    (componentOrbit V (T : Subgroup G)).subtype ↔ _
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = w := Subtype.ext he
    subst u
    exact hu
  · intro hp
    exact ⟨w, hp, rfl⟩

/-- O₁ consists of the two punctured summands. -/
def IsPureVector (w : componentOrbit V (T : Subgroup G)) : Prop :=
  w ≠ 1 ∧ ((B.coordinates w).toAdd.2 = 0 ∨ (B.coordinates w).toAdd.1 = 0)

/-- O₂ consists of the singular vectors with both components nonzero. -/
def IsSingularDiagonal (w : componentOrbit V (T : Subgroup G)) : Prop :=
  (B.coordinates w).toAdd.2 ≠ 0 ∧ (B.coordinates w).toAdd.1 ≠ 0 ∧
    B.quadratic (Additive.ofMul w) = 0

theorem naturalSummand_inf_dualSummand : B.naturalSummand ⊓ B.dualSummand = ⊥ := by
  apply bot_unique
  intro x hx
  let w : componentOrbit V (T : Subgroup G) := ⟨x, B.naturalSummand_le hx.1⟩
  have hn := (B.mem_naturalSummand w).mp hx.1
  have hd := (B.mem_dualSummand w).mp hx.2
  have hw : w = 1 := by
    apply B.coordinates.injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd (Prod.ext hd hn)
  exact congrArg Subtype.val hw

theorem point_inf_dualSummand (w : componentOrbit V (T : Subgroup G))
    (hp : (B.coordinates w).toAdd.2 = 0) :
    zpowers (w : G) ⊓ B.dualSummand = ⊥ := by
  apply bot_unique
  exact (inf_le_inf_right _ (zpowers_le.mpr ((B.mem_naturalSummand w).mpr hp))).trans
    B.naturalSummand_inf_dualSummand.le

namespace SourceModel
variable {B} (S : B.SourceModel)
include S

theorem pure_iff (w : componentOrbit V (T : Subgroup G)) :
    BinaryNaturalDual.ModelOrbits.MarkedGeometry.Pure S.setup.natural S.setup.dual
      (Additive.ofMul w) ↔ B.IsPureVector w := by
  change (Additive.ofMul w ≠ 0 ∧ (_ ∨ _)) ↔ _
  rw [S.natural_marking, S.dual_marking]
  rfl

theorem singularDiagonal_iff (w : componentOrbit V (T : Subgroup G)) :
    BinaryNaturalDual.ModelOrbits.MarkedGeometry.SingularDiagonal
      S.setup.natural S.setup.dual S.setup.quadratic (Additive.ofMul w) ↔
      B.IsSingularDiagonal w := by
  change (¬ _ ∧ ¬ _ ∧ _) ↔ _
  rw [S.natural_marking, S.dual_marking, S.quadratic_eq]
  rfl

/-- The three H.9 classes, with conjugators in the original N_G(L). -/
theorem ambient_orbit_iff (w u : componentOrbit V (T : Subgroup G))
    (hw : w ≠ 1) (hu : u ≠ 1) :
    (∃ m ∈ normalizer (L : Set G), (MulAut.conj m) (w : G) = (u : G)) ↔
      (B.IsPureVector w ∧ B.IsPureVector u) ∨
      (B.IsSingularDiagonal w ∧ B.IsSingularDiagonal u) ∨
      (B.quadratic (Additive.ofMul w) = 1 ∧ B.quadratic (Additive.ofMul u) = 1) := by
  rw [← S.pure_iff w, ← S.pure_iff u,
    ← S.singularDiagonal_iff w, ← S.singularDiagonal_iff u, ← S.quadratic_eq,
    ← S.setup.orbit_iff (show Additive.ofMul w ≠ 0 from hw)
      (show Additive.ofMul u ≠ 0 from hu)]
  constructor
  · rintro ⟨m, hm, he⟩
    refine ⟨B.actionProjection ⟨m, hm⟩, ?_⟩
    rw [S.representation_eq]
    exact congrArg Additive.ofMul (Subtype.ext he)
  · rintro ⟨a, ha⟩
    obtain ⟨m, rfl⟩ := B.actionProjection_surjective a
    refine ⟨m, m.property, ?_⟩
    rw [S.representation_eq] at ha
    exact congrArg (fun v => (v.toMul : G)) ha

/-- H.9's pure Sylow statement lifts through the literal action kernel. -/
theorem pure_sylow_preimage [Finite G] (P : Sylow 2 (normalizer (L : Set G)))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hfix : (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
      S.setup.naturalFixed (S.setup.naturalSylowNormalizer
        (P.mapSurjective B.actionProjection_surjective))) :
    ∃ Q : Sylow 2 ((centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G))),
      (Q : Subgroup _).map
        ((centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G))).subtype =
        (P : Subgroup _) ⊓
          (centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G)) := by
  obtain ⟨he, Q, hQ⟩ := S.setup.pure_sylow
    (P.mapSurjective B.actionProjection_surjective)
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw hfix
  have hpre := exists_sylow_preimage_inf_of_image P B.actionProjection
    B.actionProjection_surjective (S.setup.stabilizer (Additive.ofMul w)) Q
    (hQ.trans he.symm)
  rwa [S.stabilizer_comap] at hpre

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
