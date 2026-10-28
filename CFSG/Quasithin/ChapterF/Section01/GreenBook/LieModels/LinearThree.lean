module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification
public import Theory.GroupTheory.Amalgam.RankTwoQuotientTransport
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.BinaryLinear
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.Blocks
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.OuterExtensions

/-!
# The degree-three projective flag amalgam

The actual stabilizers of e₀ ⊂ {v | v₂ = 0} in PSL₃(F), their whole
intersection, and their inclusion maps form a rank-two amalgam. Its matrix
model consists of the three SL₃(F) stabilizers quotiented by their common
scalar kernel. The quotient is essential: for some even fields the projection
SL₃(F) → PSL₃(F) is not injective. Both compatibility squares use this same
projection. At F = F₂ these constructions agree with the existing binary model.

The separate local factors give the literal product decompositions Pᵢ = LᵢB.
The source triple is compatibly isomorphic to the flag amalgam, and its
unipotent Sylow subgroup lies in both local factors. For |F| > 2 the factors
are natural L₂-blocks and equal their solvable residuals; over every field of
order two they have actual S₄ identifications through the faithful binary
four-point actions. The full Borel is the Sylow normalizer, retaining its
torus when |F| > 2.

The imported outer-extension calculations identify the actual diagram kernel
with the faithful semilinear model, compare embedded local two-cores, and
deduce inner quotient action from relative normality in SBⱼ. The binary
diagram kernel is inner. Recognition of an arbitrary source amalgam and
elimination of its outer extension remain with the parent F.1.12 assembly.

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
The block interface was compared with C.1.7 and C.1.12, printed pp.123–124:
`IsL2EvenBlock` requires all short-group conditions and the actual quotient
conjugation module, not just the isomorphism type of a Levi factor.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree

open Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups

variable (F : Type*) [Field F] [Finite F]

/-- Scalar matrices lie in the whole overlap, so passage to PSL preserves it. -/
theorem parabolic_intersection : pointParabolic F ⊓ lineParabolic F = borel F :=
  (RankTwoAmalgam.map_overlap_of_ker_le (projection F)
    (pointParabolicSL F) (lineParabolicSL F)
    ((projection_ker_le_borelSL F).trans inf_le_right)).symm

omit [Finite F] in
theorem borel_le_point : borel F ≤ pointParabolic F := Subgroup.map_mono inf_le_left

omit [Finite F] in
theorem borel_le_line : borel F ≤ lineParabolic F := Subgroup.map_mono inf_le_right

/-- The actual projective flag amalgam. -/
def amalgam : RankTwoAmalgam (pointParabolic F) (borel F) (lineParabolic F) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_point F) (borel_le_line F)

/-- The matrix flag amalgam before taking the common scalar quotient. -/
def matrixAmalgam : RankTwoAmalgam (pointParabolicSL F) (borelSL F) (lineParabolicSL F) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Quotient each matrix subgroup by its intersection with the projection kernel. -/
def matrixQuotientAmalgam :=
  RankTwoAmalgam.ofSubgroupQuotients (projection F)
    (pointParabolicSL F) (borelSL F) (lineParabolicSL F) inf_le_left inf_le_right

/-- Compatible matrix/projective identifications, with the scalar quotient retained. -/
noncomputable def projectIso : RankTwoAmalgam.Iso (matrixQuotientAmalgam F) (amalgam F) :=
  RankTwoAmalgam.ofSubgroupQuotientsMapIso (projection F)
    (pointParabolicSL F) (borelSL F) (lineParabolicSL F) inf_le_left inf_le_right

omit [Finite F] in
theorem left_injective : Function.Injective (amalgam F).left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ _ _

omit [Finite F] in
theorem right_injective : Function.Injective (amalgam F).right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ _ _

/-- The binary case is definitionally the previously constructed concrete amalgam. -/
def binaryIso : RankTwoAmalgam.Iso (amalgam (ZMod 2)) BinaryLinear.amalgam :=
  RankTwoAmalgam.Iso.refl _

/-- In the binary case the raw SL amalgam admits the injective transport. -/
noncomputable def binaryMatrixProjectIso :
    RankTwoAmalgam.Iso (matrixAmalgam (ZMod 2)) (amalgam (ZMod 2)) :=
  BinaryLinear.projectIso

theorem binary_overlap_eq_sylow :
    borel (ZMod 2) = (Matrix.PSL3Two.borelSylow : Subgroup PSL(3, ZMod 2)) := rfl

/-- Over F₂ a parabolic cannot scale the distinguished vector nontrivially. -/
theorem binary_pointLocalSL_eq : pointLocalSL (ZMod 2) = pointParabolicSL (ZMod 2) := by
  apply le_antisymm (pointLocalSL_le _) _
  intro g hg
  have h := (mem_pointParabolicSL_iff _ g).mp hg
  have hn : g.val 0 0 ≠ 0 := by
    intro hz
    have hi := congrArg (fun a : SL(3, ZMod 2) => a.val 0 0) (inv_mul_cancel g)
    change (g⁻¹.val * g.val) 0 0 = 1 at hi
    simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
  have binary_unit : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact (mem_pointLocalSL_iff _ g).mpr ⟨binary_unit _ hn, h⟩

/-- Over F₂ a parabolic acts trivially on the one-dimensional plane quotient. -/
theorem binary_lineLocalSL_eq : lineLocalSL (ZMod 2) = lineParabolicSL (ZMod 2) := by
  apply le_antisymm (lineLocalSL_le _) _
  intro g hg
  have h := (mem_lineParabolicSL_iff _ g).mp hg
  have hn : g.val 2 2 ≠ 0 := by
    intro hz
    have hi := congrArg (fun a : SL(3, ZMod 2) => a.val 2 2) (mul_inv_cancel g)
    change (g.val * g⁻¹.val) 2 2 = 1 at hi
    simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
  have binary_unit : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact (mem_lineLocalSL_iff _ g).mpr ⟨h.1, h.2, binary_unit _ hn⟩

theorem binary_pointLocal_eq : pointLocal (ZMod 2) = Matrix.PSL3Two.pointParabolic := by
  change (pointLocalSL (ZMod 2)).map _ = (pointParabolicSL (ZMod 2)).map _
  rw [binary_pointLocalSL_eq]
  rfl

theorem binary_lineLocal_eq : lineLocal (ZMod 2) = Matrix.PSL3Two.lineParabolic := by
  change (lineLocalSL (ZMod 2)).map _ = (lineParabolicSL (ZMod 2)).map _
  rw [binary_lineLocalSL_eq]
  rfl

theorem binary_unipotent_eq_sylow :
    unipotent (ZMod 2) = (Matrix.PSL3Two.borelSylow : Subgroup PSL(3, ZMod 2)) := by
  unfold unipotent unipotentSL
  rw [binary_pointLocalSL_eq, binary_lineLocalSL_eq]
  rfl

/-- The nonbinary local-block and L = L∞ clauses for the actual projective
flag locals in F.1.12(I)(1),(II). -/
theorem nonbinary_local_structure {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ChapterC.IsL2EvenBlock (pointLocal F) n ∧
    ChapterC.IsL2EvenBlock (lineLocal F) n ∧
    Subgroup.solvableResidual (pointLocal F) = ⊤ ∧
    Subgroup.solvableResidual (lineLocal F) = ⊤ := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)
  exact ⟨pointLocal_isL2EvenBlock F hF hn, lineLocal_isL2EvenBlock F hF hn,
    pointLocal_solvableResidual_eq_top F hcard, lineLocal_solvableResidual_eq_top F hcard⟩

/-- The source triple (L₁B, B, L₂B), using the distinct local factors. -/
def localAmalgam : RankTwoAmalgam
    (pointLocal F ⊔ borel F : Subgroup PSL(3,F)) (borel F)
    (lineLocal F ⊔ borel F : Subgroup PSL(3,F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ le_sup_right le_sup_right

/-- The identifications with the flag vertices commute with both overlap maps. -/
def localAmalgamIso : RankTwoAmalgam.Iso (localAmalgam F) (amalgam F) where
  left := MulEquiv.subgroupCongr (pointParabolic_eq_sup F).symm
  middle := MulEquiv.refl _
  right := MulEquiv.subgroupCongr (lineParabolic_eq_sup F).symm
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

omit [Finite F] in
/-- The two overlap maps use the same ambient projective element. -/
theorem overlap_compatible (b : borel F) :
    (pointParabolic F).subtype ((amalgam F).left b) =
      (lineParabolic F).subtype ((amalgam F).right b) := rfl

/-- The binary point local is identified by its actual four-point action. -/
noncomputable def binaryPointLocalEquivS4 :
    pointLocal (ZMod 2) ≃* Equiv.Perm (Fin 4) :=
  (MulEquiv.subgroupCongr binary_pointLocal_eq).trans
    Matrix.PSL3Two.pointParabolicEquivS4

/-- The binary line local is identified by its actual four-point action. -/
noncomputable def binaryLineLocalEquivS4 :
    lineLocal (ZMod 2) ≃* Equiv.Perm (Fin 4) :=
  (MulEquiv.subgroupCongr binary_lineLocal_eq).trans
    Matrix.PSL3Two.lineParabolicEquivS4

theorem binaryPointLocalEquivS4_project (g : pointLocalSL (ZMod 2)) :
    binaryPointLocalEquivS4 (pointLocalProjectEquiv (ZMod 2) g) =
      Matrix.PSL3Two.MarkedAutomorphisms.pointEquivSymmetric
        ⟨g.val, (pointLocalSL_le (ZMod 2)) g.property⟩ :=
  Matrix.PSL3Two.pointParabolicEquivS4_project
    ⟨g.val, (pointLocalSL_le (ZMod 2)) g.property⟩

theorem binaryLineLocalEquivS4_project (g : lineLocalSL (ZMod 2)) :
    binaryLineLocalEquivS4 (lineLocalProjectEquiv (ZMod 2) g) =
      Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric
        ⟨g.val, (lineLocalSL_le (ZMod 2)) g.property⟩ :=
  Matrix.PSL3Two.lineParabolicEquivS4_project
    ⟨g.val, (lineLocalSL_le (ZMod 2)) g.property⟩

/-- The binary conclusion for the actual point local over any field of order two. -/
noncomputable def pointLocalEquivS4 (hF : Nat.card F = 2) :
    pointLocal F ≃* Equiv.Perm (Fin 4) := by
  let _ := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [← Nat.card_eq_fintype_card])).symm
  exact (pointLocalFieldEquiv e).trans binaryPointLocalEquivS4

/-- The binary conclusion for the actual line local over any field of order two. -/
noncomputable def lineLocalEquivS4 (hF : Nat.card F = 2) :
    lineLocal F ≃* Equiv.Perm (Fin 4) := by
  let _ := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [← Nat.card_eq_fintype_card])).symm
  exact (lineLocalFieldEquiv e).trans binaryLineLocalEquivS4

section Sylow
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)

/-- The Sylow subgroup is contained in both distinct local factors. -/
theorem sylow_le_localFactors :
    (unipotentSylow F hn hF : Subgroup PSL(3,F)) ≤ pointLocal F ∧
      (unipotentSylow F hn hF : Subgroup PSL(3,F)) ≤ lineLocal F :=
  ⟨unipotent_le_pointLocal F, unipotent_le_lineLocal F⟩

/-- At the prime field the general Sylow is the original binary Sylow. -/
theorem binary_unipotentSylow_eq :
    unipotentSylow (ZMod 2) (n := 1) (by decide) (by simp) =
      Matrix.PSL3Two.borelSylow := by
  apply Sylow.ext
  exact binary_unipotent_eq_sylow

/-- The whole overlap, its Sylow normalizer, and the source vertices are
identified in one ambient group. The vertices generate that group. -/
theorem flag_structure :
    pointParabolic F ⊓ lineParabolic F = borel F ∧
    Subgroup.normalizer (unipotentSylow F hn hF : Set PSL(3,F)) = borel F ∧
    pointParabolic F = pointLocal F ⊔ borel F ∧
    lineParabolic F = lineLocal F ⊔ borel F ∧
    pointParabolic F ⊔ lineParabolic F = ⊤ ∧
    (unipotentSylow F hn hF : Subgroup PSL(3,F)) ≤ pointLocal F ∧
    (unipotentSylow F hn hF : Subgroup PSL(3,F)) ≤ lineLocal F :=
  ⟨parabolic_intersection F, normalizer_unipotent F hn hF,
    pointParabolic_eq_sup F, lineParabolic_eq_sup F, parabolics_sup_eq_top F,
    sylow_le_localFactors F hn hF⟩

/-- The source Bᵢ = N_{Lᵢ}(S ∩ Lᵢ) are the restrictions of the full Borel. -/
theorem local_sylow_normalizers :
    Subgroup.normalizer ((unipotentSylow F hn hF : Subgroup PSL(3,F)).subgroupOf
      (pointLocal F) : Set (pointLocal F)) = (borel F).subgroupOf (pointLocal F) ∧
    Subgroup.normalizer ((unipotentSylow F hn hF : Subgroup PSL(3,F)).subgroupOf
      (lineLocal F) : Set (lineLocal F)) = (borel F).subgroupOf (lineLocal F) :=
  ⟨normalizer_pointLocalSylow F hn hF, normalizer_lineLocalSylow F hn hF⟩

end Sylow

section SourceClauses
variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- The precise local alternative in F.1.12(I)(1) for the concrete flag model.
Neither a block certificate nor a symmetric-group identification is an input. -/
theorem local_alternative (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    (ChapterC.IsL2EvenBlock (pointLocal F) n ∧
      ChapterC.IsL2EvenBlock (lineLocal F) n) ∨
    (Nat.card F = 2 ∧ Nonempty (pointLocal F ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (lineLocal F ≃* Equiv.Perm (Fin 4))) := by
  by_cases h : n = 1
  · have htwo : Nat.card F = 2 := by simpa only [h, pow_one] using hF
    exact Or.inr ⟨htwo, ⟨pointLocalEquivS4 F htwo⟩, ⟨lineLocalEquivS4 F htwo⟩⟩
  · have hn' : 1 < n := by omega
    exact Or.inl ⟨pointLocal_isL2EvenBlock F hF hn', lineLocal_isL2EvenBlock F hF hn'⟩

/-- F.1.12(II)(i) in the nonbinary concrete model, with residual images
compared in PSL₃ and the same chosen Sylow subgroup on both sides. -/
theorem nonbinary_residuals (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (Subgroup.solvableResidual (pointLocal F)).map (pointLocal F).subtype = pointLocal F ∧
    (Subgroup.solvableResidual (lineLocal F)).map (lineLocal F).subtype = lineLocal F ∧
    (unipotentSylow F (lt_trans Nat.zero_lt_one hn) hF : Subgroup PSL(3,F)) ≤ pointLocal F ∧
    (unipotentSylow F (lt_trans Nat.zero_lt_one hn) hF : Subgroup PSL(3,F)) ≤ lineLocal F :=
  ⟨(pointLocal_block_structure F hF hn).2.2.2,
    (lineLocal_block_structure F hF hn).2.2.2,
    sylow_le_localFactors F (lt_trans Nat.zero_lt_one hn) hF⟩

/-- The concrete linear-three case, including the source's binary exception
and the residual/Sylow alternative in (II). Its maps are `amalgam F`, with
compatible source-triple and matrix-quotient models `localAmalgamIso F` and
`projectIso F`. -/
theorem concrete_case (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    ∃ S : Sylow 2 PSL(3,F),
      (S : Subgroup PSL(3,F)) = unipotent F ∧
      pointParabolic F ⊓ lineParabolic F = borel F ∧
      Subgroup.normalizer (S : Set PSL(3,F)) = borel F ∧
      pointParabolic F = pointLocal F ⊔ borel F ∧
      lineParabolic F = lineLocal F ⊔ borel F ∧
      ((ChapterC.IsL2EvenBlock (pointLocal F) n ∧
          ChapterC.IsL2EvenBlock (lineLocal F) n) ∨
        (Nat.card F = 2 ∧ Nonempty (pointLocal F ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (lineLocal F ≃* Equiv.Perm (Fin 4)))) ∧
      (((Subgroup.solvableResidual (pointLocal F)).map (pointLocal F).subtype =
          pointLocal F ∧
        (Subgroup.solvableResidual (lineLocal F)).map (lineLocal F).subtype =
          lineLocal F ∧
        (S : Subgroup PSL(3,F)) ≤ pointLocal F ∧
        (S : Subgroup PSL(3,F)) ≤ lineLocal F) ∨ Nat.card F = 2) := by
  refine ⟨unipotentSylow F hn hF, rfl, parabolic_intersection F,
    normalizer_unipotent F hn hF, pointParabolic_eq_sup F, lineParabolic_eq_sup F,
    local_alternative hF hn, ?_⟩
  by_cases h : n = 1
  · exact Or.inr (by simpa only [h, pow_one] using hF)
  · exact Or.inl (nonbinary_residuals hF (by omega))

end SourceClauses

section Extension
open Matrix.PSL3.LinearThree.OuterExtensions
open Theory.GroupTheory.AutomorphismExtensionBorel
variable {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
variable (E : Subgroup (MulAut PSL(3,F))) (hE : MulAut.innerSubgroup PSL(3,F) ≤ E)
include hF hn

/-- Lᵢ = Lᵢ∞ also holds for the literal copies in the chosen automorphism extension. -/
theorem extension_local_residual (point : Bool) :
    (Subgroup.solvableResidual (localIn F E hE point)).map
      (localIn F E hE point).subtype = localIn F E hE point := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)
  have hr : Subgroup.solvableResidual (localFactor F point) = ⊤ := by
    cases point
    · exact lineLocal_solvableResidual_eq_top F hcard
    · exact pointLocal_solvableResidual_eq_top F hcard
  have hi : Subgroup.solvableResidual (localIn F E hE point) = ⊤ := by
    rw [← Subgroup.map_solvableResidual_eq (localEquiv F E hE point).toMonoidHom
      (localEquiv F E hE point).surjective, hr]
    exact Subgroup.map_top_of_surjective _ (localEquiv F E hE point).surjective
  rw [hi, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The three family-specific deductions on p.264 in one actual ambient extension.
Characteristic two and both residual identities are derived from the field size;
the remaining premises are the source's diagram condition and relative normality. -/
theorem extension_local_calculations (hdiagram : E ≤ diagramTrivial F)
    (S : Sylow 2 E)
    (hSL : ∀ point, (S : Subgroup E) ≤
      Subgroup.normalizer (localIn F E hE point : Set E))
    (j : Bool) (hnormal : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hE S j)).Normal) :
    (∃ e : E.comap (semilinearAction F) ≃* E,
      ∀ x, (e x).val = semilinearAction F x.val) ∧
    (∀ point, (Subgroup.solvableResidual (localIn F E hE point)).map
      (localIn F E hE point).subtype = localIn F E hE point) ∧
    (∀ point, (pCore 2 (localIn F E hE point ⊔ (S : Subgroup E) : Subgroup E)).map
      (localIn F E hE point ⊔ (S : Subgroup E)).subtype =
      (pCore 2 (localIn F E hE point)).map (localIn F E hE point).subtype) ∧
    ((localQuotientAction F E hE j).comp (Subgroup.inclusion (hSL j))).range ≤
      MulAut.innerSubgroup (localIn F E hE j ⧸ pCore 2 (localIn F E hE j)) := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨hmodel, hcores, hinner⟩ :=
    OuterExtensions.nonbinary_extension_calculations F E hE hn hF hdiagram S hSL j hnormal
  exact ⟨hmodel, extension_local_residual F hF hn E hE, hcores, hinner⟩

end Extension
end CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree
