module

public import Stellmacher.Recognition.FongWreathedCartan

/-!
# Fong's local centralizers and principal-block columns

One actual height-two wreathed presentation supplies the representatives
`F = s*z`, `E = s`, `X = s²`, and `J = (s*t)²`. We choose its orientation
using the ambient fusion theorem. Its centralizer quotients and genuine
local principal-block decomposition data then give Cartan matrices `(8)`
at F and F³, `(16)` at XF², and `[[16,8],[8,12]]` at F² and J.

Local column orthogonality identifies the ambient principal-block column
sum with the corresponding local sum of squared ordinary degrees. Thus the
five column sums are 8, 8, 16, 96, and 96. The local data use the ambient
modular place throughout; the matrices are conclusions about actual
irreducible modular characters and their decomposition multiplicities.
The final existence theorem discharges the fusion, centralizer, and Cartan
premises together, with a presentation independent of the ambient datum.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), pp. 69–71, equations (4)–(7).
-/

public section
noncomputable section

namespace Stellmacher.Recognition.FongWreathedIntrinsic

open scoped BigOperators
open ABG ModularBlock PrincipalBlockConstruction

variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

/-- Equation (6), evaluated on the actual representatives in the ambient
principal two-block. Each sum is a sum of squared absolute character values. -/
structure LocalPrincipalColumnNormData (d : PrincipalCongruenceBlockData G) : Prop where
  F_column :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk ((F P : S) : G)) *
      star (d.chi i (ConjClasses.mk ((F P : S) : G))) = (8 : ℂ)
  F_cube_column :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk ((F P ^ 3 : S) : G)) *
      star (d.chi i (ConjClasses.mk ((F P ^ 3 : S) : G))) = (8 : ℂ)
  XF_sq_column :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk ((X P * F P ^ 2 : S) : G)) *
      star (d.chi i (ConjClasses.mk ((X P * F P ^ 2 : S) : G))) = (16 : ℂ)
  F_sq_column :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk ((F P ^ 2 : S) : G)) *
      star (d.chi i (ConjClasses.mk ((F P ^ 2 : S) : G))) = (96 : ℂ)
  J_column :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk ((J P : S) : G)) *
      star (d.chi i (ConjClasses.mk ((J P : S) : G))) = (96 : ℂ)

/-- The genuine local Cartan computations imply all five ambient columns by
principal-block local column orthogonality. -/
theorem localPrincipalColumnNormData_of_cartan
    (d : PrincipalCongruenceBlockData G) (h : LocalPrincipalCartanData S P d) :
    LocalPrincipalColumnNormData S P d := by
  obtain ⟨aF, _, _, hF⟩ := h.F_computation
  obtain ⟨aF3, _, _, hF3⟩ := h.F_cube_computation
  obtain ⟨aXF2, _, _, hXF2⟩ := h.XF_sq_computation
  obtain ⟨aF2, _, _, _, _, _, _, hF2⟩ := h.F_sq_computation
  obtain ⟨aJ, _, _, _, _, _, _, hJ⟩ := h.J_computation
  exact
    { F_column := (sylow_principalBlock_local_column_norm S d (F P)).trans hF
      F_cube_column := (sylow_principalBlock_local_column_norm S d (F P ^ 3)).trans hF3
      XF_sq_column :=
        (sylow_principalBlock_local_column_norm S d (X P * F P ^ 2)).trans hXF2
      F_sq_column := (sylow_principalBlock_local_column_norm S d (F P ^ 2)).trans hF2
      J_column := (sylow_principalBlock_local_column_norm S d (J P)).trans hJ }

variable [IsSimpleGroup G]

/-- Fong's simultaneous local data: oriented fusion, actual centralizer
quotients, genuine local decomposition and Cartan data, and ambient columns. -/
structure LocalBlockData (d : PrincipalCongruenceBlockData G) : Prop
    extends LocalCentralizerData S P, LocalPrincipalCartanData S P d,
      LocalPrincipalColumnNormData S P d

/-- Assemble the block data at a prescribed presentation; the final existence
theorem below constructs and discharges the centralizer-data premise. -/
theorem localBlockData_of_localCentralizerData
    (h : LocalCentralizerData S P)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (d : PrincipalCongruenceBlockData G) : LocalBlockData S P d := by
  have hc := localPrincipalCartanData S P x hx d
  exact
    { toLocalCentralizerData := h
      toLocalPrincipalCartanData := hc
      toLocalPrincipalColumnNormData := localPrincipalColumnNormData_of_cartan S P d hc }

/-- A single compatible choice of actual representatives satisfies (4)–(7)
for every ambient principal-block datum. Only the original group-theoretic
hypotheses are required to choose this presentation. -/
theorem exists_localBlockData_forall
    (hS : IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ P : Wreathed.Presentation S 2,
      ∀ d : PrincipalCongruenceBlockData G, LocalBlockData S P d := by
  obtain ⟨P, hc⟩ := exists_localCentralizerData S hS x hx
  exact ⟨P, fun d => localBlockData_of_localCentralizerData S P hc x hx d⟩

/-- Fong's local centralizer and principal-block data at any prescribed
ambient datum, with no replacement assumptions on matrices or column sums. -/
theorem exists_localBlockData
    (hS : IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (d : PrincipalCongruenceBlockData G) :
    ∃ P : Wreathed.Presentation S 2, LocalBlockData S P d := by
  obtain ⟨P, hP⟩ := exists_localBlockData_forall S hS x hx
  exact ⟨P, hP d⟩

end Stellmacher.Recognition.FongWreathedIntrinsic
