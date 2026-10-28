module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryConstituents
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents

/-!
# Completing the literal local-core section

The aligned projection has precisely the original star kernel. The earlier
comparison S=I∩O₂(LT) identifies its restriction kernel with S∩L₁.
The binary local core then maps onto the translation radical, retaining
its original denominator and the same cubic plane action as V/V₁.
The terminal quotient has no two-chief factors. The larger-field radical
calculation is connected to the same literal source denominator.

Source: Aschbacher–Smith, G.2.5(1–8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.CoreAssembly
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h} (a : PointAlignment d)

/-- The alignment does not change the original star kernel. -/
theorem projection_kernel : a.projection.ker = (D.LT.pCoreIn 2).subgroupOf D.L := by
  rw [PointAlignment.projection, MonoidHom.ker_comp_of_injective _ _
    (MulAut.conj a.basis⁻¹).injective, modelProjection,
    MonoidHom.ker_comp_of_injective _ _ d.model.injective]
  ext l
  change starProjection D l = 1 ↔ (l : G) ∈ (pCore 2 D.LT).map D.LT.subtype
  constructor
  · intro hl
    refine ⟨inclusion (show D.L ≤ D.LT from le_sup_left) l, ?_, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hl)
  · rintro ⟨x,hx,he⟩
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    have hh : inclusion (show D.L ≤ D.LT from le_sup_left) l = x := Subtype.ext he.symm
    exact hh ▸ hx

/-- The intrinsic S-kernel comparison identifies exactly the local star kernel. -/
theorem rawProjection_kernel (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2) :
    (ScalarConstituents.rawProjection a).ker = (S D g h).subgroupOf D.L₁ := by
  rw [ScalarConstituents.rawProjection, ← MonoidHom.comap_ker, projection_kernel]
  ext x
  change (x : G) ∈ D.LT.pCoreIn 2 ↔ (x : G) ∈ S D g h
  rw [hcore]
  exact ⟨fun hx => ⟨hLI (((map_subtype_le _).trans inf_le_left) x.property),hx⟩,
    fun hx => hx.2⟩

omit [Finite G] in
/-- Normality of the literal source-kernel intersection is relative to L₁. -/
theorem sourceKernel_normal (hLI : D.L ≤ I D g h) : ((S D g h).subgroupOf D.L₁).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((map_subtype_le _).trans inf_le_left).trans (hLI.trans (I_normalizes_core D g h)))

include a in
/-- The source-kernel stratum lies in the actual local two-core. -/
theorem sourceKernel_le_core (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2) :
    (S D g h).subgroupOf D.L₁ ≤ pCore 2 D.L₁ := by
  rw [← rawProjection_kernel a hLI hcore]
  have hp : IsPGroup 2 (ScalarConstituents.rawProjection a).ker := by
    rw [ScalarConstituents.rawProjection, ← MonoidHom.comap_ker]
    exact a.projection_kernel_twoGroup.comap_of_injective _ (inclusion_injective _)
  exact le_sSup ⟨inferInstance,hp⟩

namespace Larger
/-- Source S∩L₁ is precisely the kernel of the larger-field local projection. -/
theorem localProjection_kernel (hn : 1 < n) (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2) :
    (ScalarConstituents.localProjection a hn).ker = (S D g h).subgroupOf D.L₁ := by
  rw [ScalarConstituents.localProjection, MonoidHom.ker_codRestrict]
  exact rawProjection_kernel a hLI hcore

/-- Literal source intersections supply the denominator of the radical section. -/
noncomputable def radicalSectionEquiv (hn : 1 < n) (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2)
    [(((S D g h).subgroupOf D.L₁).subgroupOf (pCore 2 D.L₁)).Normal] :
    (pCore 2 D.L₁ ⧸ ((S D g h).subgroupOf D.L₁).subgroupOf (pCore 2 D.L₁)) ≃*
      Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun N : Subgroup D.L₁ => N.subgroupOf (pCore 2 D.L₁))
      (localProjection_kernel a hn hLI hcore)).symm).trans
    (ScalarConstituents.sourceRadicalQuotientEquiv a hn)
end Larger

namespace Binary
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
variable {db : Hypothesis D (ZMod 2) 1 g h} (b : PointAlignment db)

/-- Source S∩L₁ is precisely the binary local projection kernel. -/
theorem localProjection_kernel (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2) :
    (ResidualRestriction.Binary.localProjection b).ker = (S D g h).subgroupOf D.L₁ := by
  rw [ResidualRestriction.Binary.localProjection, MonoidHom.ker_codRestrict]
  exact rawProjection_kernel b hLI hcore

/-- Membership in the actual local core is detected by the marked translation group. -/
theorem core_mem_iff (x : D.L₁) :
    x ∈ pCore 2 D.L₁ ↔ (ResidualRestriction.Binary.localProjection b x).val ∈ pointV := by
  rw [← ResidualRestriction.Binary.local_core_preimage b, ← point_core]
  change ResidualRestriction.Binary.localProjection b x ∈ pCore 2 pointA ↔
    pointA.subtype (ResidualRestriction.Binary.localProjection b x) ∈
      (pCore 2 pointA).map pointA.subtype
  exact (mem_map_iff_mem pointA.subtype_injective).symm

/-- The local core maps to the literal geometric translation radical. -/
def radicalProjection : pCore 2 D.L₁ →* pointV :=
  ((pointA.subtype.comp (ResidualRestriction.Binary.localProjection b)).comp
    (pCore 2 D.L₁).subtype).codRestrict pointV
      (fun y => (core_mem_iff b y.val).mp y.property)

theorem radicalProjection_surjective : Function.Surjective (radicalProjection b) := by
  intro t
  obtain ⟨x,hx⟩ := ResidualRestriction.Binary.localProjection_surjective b
    ⟨t.val,pointV_le t.property⟩
  have hc : x ∈ pCore 2 D.L₁ := (core_mem_iff b x).mpr (by rw [hx]; exact t.property)
  exact ⟨⟨x,hc⟩,Subtype.ext (congrArg (fun z : pointA => z.val) hx)⟩

theorem radicalProjection_kernel :
    (radicalProjection b).ker =
      (ResidualRestriction.Binary.localProjection b).ker.subgroupOf (pCore 2 D.L₁) := by
  ext x
  change radicalProjection b x = 1 ↔ ResidualRestriction.Binary.localProjection b x.val = 1
  constructor <;> intro h
  · exact Subtype.ext (congrArg (fun z : pointV => z.val) h)
  · exact Subtype.ext (congrArg (fun z : pointA => z.val) h)

/-- The source radical quotient has the same coordinates as all other binary planes. -/
noncomputable def radicalSectionEquiv :
    (pCore 2 D.L₁ ⧸ (ResidualRestriction.Binary.localProjection b).ker.subgroupOf (pCore 2 D.L₁)) ≃*
      Multiplicative BinaryConstituents.Two :=
  (QuotientGroup.quotientMulEquivOfEq (radicalProjection_kernel b).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ (radicalProjection_surjective b)).trans radicalEquiv)

@[simp] theorem radicalSectionEquiv_mk (y : pCore 2 D.L₁) :
    radicalSectionEquiv b (QuotientGroup.mk'
      ((ResidualRestriction.Binary.localProjection b).ker.subgroupOf (pCore 2 D.L₁)) y) =
      radicalEquiv (radicalProjection b y) := rfl

/-- This is the literal conjugation action of L₁ on its own local core. -/
theorem radicalProjection_conjugate (l : D.L₁) (y : pCore 2 D.L₁) :
    radicalProjection b (MulAut.conjNormal l y) =
      radicalConj (ResidualRestriction.Binary.localProjection b l) (radicalProjection b y) := by
  apply Subtype.ext
  change (ResidualRestriction.Binary.localProjection b (l * y.val * l⁻¹)).val = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The radical section uses the identical irreducible C₃ action as V/V₁. -/
theorem radicalSectionEquiv_conjugate (l : D.L₁) (y : pCore 2 D.L₁) :
    (radicalSectionEquiv b (QuotientGroup.mk'
      ((ResidualRestriction.Binary.localProjection b).ker.subgroupOf (pCore 2 D.L₁))
      (MulAut.conjNormal l y))).toAdd =
      BinaryConstituents.localConstituent b l
        (radicalSectionEquiv b (QuotientGroup.mk'
          ((ResidualRestriction.Binary.localProjection b).ker.subgroupOf (pCore 2 D.L₁)) y)).toAdd := by
  simp only [radicalSectionEquiv_mk, radicalProjection_conjugate, radical_equivariant]
  rfl

/-- The denominator is exactly S∩L₁ inside the local two-core. -/
noncomputable def sourceRadicalSectionEquiv (hLI : D.L ≤ I D g h)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2)
    [(((S D g h).subgroupOf D.L₁).subgroupOf (pCore 2 D.L₁)).Normal] :
    (pCore 2 D.L₁ ⧸ ((S D g h).subgroupOf D.L₁).subgroupOf (pCore 2 D.L₁)) ≃*
      Multiplicative BinaryConstituents.Two :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun N : Subgroup D.L₁ => N.subgroupOf (pCore 2 D.L₁))
      (localProjection_kernel b hLI hcore)).symm).trans (radicalSectionEquiv b)

include b in
/-- The cubic terminal quotient supplies the exact chief-refinement exclusion. -/
theorem terminal_hasNoTwoChiefFactors :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) := by
  intro A B hAB hp
  have hs := ResidualRestriction.Binary.terminal_two_section_trivial b A.val B.val hp
  have hle : B.val ≤ A.val := subgroupOf_eq_top.mp (QuotientGroup.subsingleton_iff.mp hs)
  exact hAB.lt.not_ge hle
end Binary
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.CoreAssembly
