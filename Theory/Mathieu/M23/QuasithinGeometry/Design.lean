module

public import Theory.Mathieu.M23.Basic
public import Theory.Combinatorics.PairGraphLocalGeometry
public import Mathlib.Data.Fin.VecNotation

/-!
# Heptads and pair-derived lines in the concrete Witt design

The verified S(4,7,23) design supplies unique heptad extension of four-sets.
Consequently their setwise stabilizers preserve the containing heptad. Deleting
any fixed pair from the heptads through it gives five-point lines, with a unique
line through two points of the complement. The pair stabilizer preserves these
lines. The first certified heptad supplies compatible labels for the configuration.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.2,
Lemma 5.2.18 and the notation preceding it, printed pp.655--656.
The group identifications and coordinatization over F4 are separate results.
-/

@[expose] public section

namespace Sporadic.Mathieu.M23Geometry

open scoped Pointwise

/-- A four-set has a unique containing heptad, in existential form. -/
theorem exists_unique_heptad (S : Finset (Fin 23)) (hS : S.card = 4) :
    ∃! B, B ∈ m23Blocks ∧ S ⊆ B := by
  obtain ⟨B, hB⟩ := Finset.card_eq_one.mp (m23Blocks_unique_block S hS)
  have hmem (C : Finset (Fin 23)) :
      C ∈ m23Blocks ∧ S ⊆ C ↔ C = B := by
    rw [← Finset.mem_filter, hB, Finset.mem_singleton]
  exact ⟨B, (hmem B).mpr rfl, fun C hC => (hmem C).mp hC⟩

/-- Two heptads containing the same four-set coincide. -/
theorem heptad_eq_of_four_subset {S B C : Finset (Fin 23)} (hS : S.card = 4)
    (hB : B ∈ m23Blocks) (hC : C ∈ m23Blocks) (hSB : S ⊆ B) (hSC : S ⊆ C) :
    B = C :=
  (exists_unique_heptad S hS).unique ⟨hB, hSB⟩ ⟨hC, hSC⟩

/-- The natural action of M23 preserves the certified heptad set. -/
theorem smul_heptad (g : M23) {B : Finset (Fin 23)} (hB : B ∈ m23Blocks) :
    g • B ∈ m23Blocks := by
  have hg := (mem_M23_iff g.val).mp g.property
  change g.val • B ∈ (m23Blocks : Set (Finset (Fin 23)))
  rw [← hg]
  exact Set.smul_mem_smul_set hB

/-- Lemma 5.2.18(3), for any four-subset of any heptad. -/
theorem four_stabilizer_le_heptad_stabilizer {S B : Finset (Fin 23)}
    (hS : S.card = 4) (hB : B ∈ m23Blocks) (hSB : S ⊆ B) :
    MulAction.stabilizer M23 S ≤ MulAction.stabilizer M23 B := by
  intro g hg
  apply MulAction.mem_stabilizer_iff.mpr
  apply heptad_eq_of_four_subset hS (smul_heptad g hB) hB _ hSB
  have h := Finset.smul_finset_subset_smul_finset (a := g) hSB
  rwa [MulAction.mem_stabilizer_iff.mp hg] at h

/-- The stabilizer computed inside the heptad stabilizer maps onto the global
four-set stabilizer. -/
theorem four_stabilizer_map {S B : Finset (Fin 23)}
    (hS : S.card = 4) (hB : B ∈ m23Blocks) (hSB : S ⊆ B) :
    (MulAction.stabilizer (MulAction.stabilizer M23 B) S).map
      (MulAction.stabilizer M23 B).subtype = MulAction.stabilizer M23 S := by
  exact Subgroup.map_subgroupOf_eq_of_le
    (four_stabilizer_le_heptad_stabilizer hS hB hSB)

/-- The actual compatible isomorphism between the internal and global
four-set stabilizers; its underlying map is inclusion. -/
noncomputable def fourStabilizerEquiv {S B : Finset (Fin 23)}
    (hS : S.card = 4) (hB : B ∈ m23Blocks) (hSB : S ⊆ B) :
    MulAction.stabilizer (MulAction.stabilizer M23 B) S ≃*
      MulAction.stabilizer M23 S :=
  Subgroup.subgroupOfEquivOfLe (four_stabilizer_le_heptad_stabilizer hS hB hSB)

@[simp] theorem fourStabilizerEquiv_apply {S B : Finset (Fin 23)}
    (hS : S.card = 4) (hB : B ∈ m23Blocks) (hSB : S ⊆ B)
    (g : MulAction.stabilizer (MulAction.stabilizer M23 B) S) :
    (fourStabilizerEquiv hS hB hSB g : M23) = (g : MulAction.stabilizer M23 B) := rfl

/-- Restriction of the natural action to a finite set fixed setwise. -/
noncomputable def setAction (S : Finset (Fin 23)) :
    MulAction.stabilizer M23 S →* Equiv.Perm S where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

@[simp] theorem setAction_apply (S : Finset (Fin 23))
    (g : MulAction.stabilizer M23 S) (a : S) :
    (setAction S g a).val = (g : M23) • a.val := rfl

/-- The kernel of restriction consists exactly of the pointwise fixers. -/
theorem mem_setAction_ker (S : Finset (Fin 23)) (g : MulAction.stabilizer M23 S) :
    g ∈ (setAction S).ker ↔ ∀ a ∈ S, (g : M23) • a = a := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨a, ha⟩)
  · intro h
    apply Equiv.ext
    intro a
    exact Subtype.ext (h a.val a.property)

/-- Source labels 1,...,7, indexed here by Fin 7. They lie in an actual heptad. -/
def label : Fin 7 ↪ Fin 23 where
  toFun := ![1, 2, 3, 4, 5, 11, 17]
  inj' := by decide +kernel

/-- The first certified heptad. -/
def omega : Finset (Fin 23) := {1, 2, 3, 4, 5, 11, 17}

theorem omega_eq_block : omega = m23BlockAt 0 := by decide +kernel

theorem omega_mem : omega ∈ m23Blocks := by
  rw [omega_eq_block, m23Blocks]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem omega_card : omega.card = 7 := m23Blocks_card omega omega_mem

theorem label_image : Finset.univ.image label = omega := by decide +kernel

/-- The source four-set {4,5,6,7}, with compatible concrete labels. -/
def lambda : Finset (Fin 23) := {label 3, label 4, label 5, label 6}

/-- The source vertices x={6,7} and y={5,6}. -/
def x : Theory.Combinatorics.PairGraph.Vertex (Fin 23) :=
  ⟨{label 5, label 6}, by decide +kernel⟩

def y : Theory.Combinatorics.PairGraph.Vertex (Fin 23) :=
  ⟨{label 4, label 5}, by decide +kernel⟩

theorem lambda_card : lambda.card = 4 := by decide +kernel

theorem lambda_subset_omega : lambda ⊆ omega := by decide +kernel

theorem x_subset_lambda : x.val ⊆ lambda := by decide +kernel

theorem y_subset_lambda : y.val ⊆ lambda := by decide +kernel

theorem x_adj_y : (Theory.Combinatorics.PairGraph.graph (Fin 23)).Adj x y := by
  apply Theory.Combinatorics.PairGraph.adj_iff_card_inter x y |>.mpr
  decide +kernel

noncomputable abbrev heptadStabilizer := MulAction.stabilizer M23 omega
noncomputable abbrev fourStabilizer := MulAction.stabilizer M23 lambda
noncomputable abbrev pairStabilizer := MulAction.stabilizer M23 x.val

theorem fourStabilizer_le : fourStabilizer ≤ heptadStabilizer :=
  four_stabilizer_le_heptad_stabilizer lambda_card omega_mem lambda_subset_omega

/-- Complement of the pair, as a finite point set. -/
def pairComplement (P : Finset (Fin 23)) : Finset (Fin 23) := Finset.univ \ P

/-- Lines on the pair complement, retaining their concrete ambient point sets. -/
noncomputable def pairLines (P : Finset (Fin 23)) : Finset (Finset (Fin 23)) :=
  (m23Blocks.filter (P ⊆ ·)).image (· \ P)

theorem mem_pairLines {P L : Finset (Fin 23)} :
    L ∈ pairLines P ↔ ∃ B ∈ m23Blocks, P ⊆ B ∧ B \ P = L := by
  simp only [pairLines, Finset.mem_image, Finset.mem_filter]
  aesop

theorem pairComplement_card {P : Finset (Fin 23)} (hP : P.card = 2) :
    (pairComplement P).card = 21 := by
  rw [pairComplement, Finset.card_sdiff_of_subset (Finset.subset_univ P)]
  simp [hP]

theorem line_subset_complement {P L : Finset (Fin 23)} (hL : L ∈ pairLines P) :
    L ⊆ pairComplement P := by
  obtain ⟨B, _, _, rfl⟩ := mem_pairLines.mp hL
  exact Finset.sdiff_subset_sdiff (Finset.subset_univ B) (Finset.Subset.refl P)

theorem line_card {P L : Finset (Fin 23)} (hP : P.card = 2)
    (hL : L ∈ pairLines P) : L.card = 5 := by
  obtain ⟨B, hB, hPB, rfl⟩ := mem_pairLines.mp hL
  rw [Finset.card_sdiff_of_subset hPB, m23Blocks_card B hB, hP]

/-- Deletion of the pair loses no information about its containing heptad. -/
theorem heptad_recover {P B : Finset (Fin 23)} (hPB : P ⊆ B) :
    P ∪ (B \ P) = B := Finset.union_sdiff_of_subset hPB

/-- The derived design has exactly one line through each two-subset of its
21-point complement. -/
theorem exists_unique_line {P S : Finset (Fin 23)} (hP : P.card = 2)
    (hS : S.card = 2) (hSP : S ⊆ pairComplement P) :
    ∃! L, L ∈ pairLines P ∧ S ⊆ L := by
  have hd : Disjoint P S := by
    apply Finset.disjoint_left.mpr
    intro a haP haS
    exact (Finset.mem_sdiff.mp (hSP haS)).2 haP
  have hPS : (P ∪ S).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, hP, hS]
  obtain ⟨B, ⟨hB, hPSB⟩, huniq⟩ := exists_unique_heptad (P ∪ S) hPS
  have hPB : P ⊆ B := Finset.Subset.trans Finset.subset_union_left hPSB
  have hSL : S ⊆ B \ P := by
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨hPSB (Finset.mem_union_right _ ha),
      (Finset.mem_sdiff.mp (hSP ha)).2⟩
  refine ⟨B \ P, ⟨mem_pairLines.mpr ⟨B, hB, hPB, rfl⟩, hSL⟩, ?_⟩
  rintro L ⟨hL, hSL'⟩
  obtain ⟨C, hC, hPC, rfl⟩ := mem_pairLines.mp hL
  have hCB : C = B := huniq C ⟨hC, Finset.union_subset hPC
    (fun a ha => (Finset.mem_sdiff.mp (hSL' ha)).1)⟩
  rw [hCB]

/-- The pair stabilizer acts on the derived lines by its natural point action. -/
theorem smul_line {P L : Finset (Fin 23)} (g : MulAction.stabilizer M23 P)
    (hL : L ∈ pairLines P) : (g : M23) • L ∈ pairLines P := by
  obtain ⟨B, hB, hPB, rfl⟩ := mem_pairLines.mp hL
  have hg : (g : M23) • P = P := MulAction.mem_stabilizer_iff.mp g.property
  refine mem_pairLines.mpr ⟨(g : M23) • B, smul_heptad g.val hB, ?_, ?_⟩
  · have h := Finset.smul_finset_subset_smul_finset (a := (g : M23)) hPB
    rwa [hg] at h
  · rw [Finset.smul_finset_sdiff, hg]

/-- The natural action of the pair stabilizer on the complementary points. -/
noncomputable def complementAction (P : Finset (Fin 23)) :
    MulAction.stabilizer M23 P →* Equiv.Perm (pairComplement P) where
  toFun g := g.val.val.subtypePerm (by
    intro a
    simp only [pairComplement, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact not_congr (MulAction.mem_stabilizer_finset.mp g.property a))
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

@[simp] theorem complementAction_apply (P : Finset (Fin 23))
    (g : MulAction.stabilizer M23 P) (a : pairComplement P) :
    (complementAction P g a).val = (g : M23) • a.val := rfl

/-- The natural action of the pair stabilizer on the derived lines. -/
noncomputable def lineAction (P : Finset (Fin 23)) :
    MulAction.stabilizer M23 P →* Equiv.Perm (pairLines P) where
  toFun g := (MulAction.toPerm (β := Finset (Fin 23)) g.val).subtypePerm (by
    intro L
    constructor
    · intro h
      have hi := smul_line g⁻¹ h
      simpa using hi
    · exact smul_line g)
  map_one' := by
    apply Equiv.ext
    intro L
    apply Subtype.ext
    exact one_smul M23 L.val
  map_mul' g h := by
    apply Equiv.ext
    intro L
    apply Subtype.ext
    exact mul_smul g.val h.val L.val

@[simp] theorem lineAction_apply (P : Finset (Fin 23))
    (g : MulAction.stabilizer M23 P) (L : pairLines P) :
    (lineAction P g L).val = (g : M23) • L.val := rfl

/-- The two restriction maps preserve incidence in both directions. -/
theorem action_preserves_incidence (P : Finset (Fin 23))
    (g : MulAction.stabilizer M23 P) (a : pairComplement P) (L : pairLines P) :
    (complementAction P g a).val ∈ (lineAction P g L).val ↔ a.val ∈ L.val := by
  change (g : M23) • a.val ∈ (g : M23) • L.val ↔ a.val ∈ L.val
  simp

end Sporadic.Mathieu.M23Geometry
