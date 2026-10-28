module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow
public import Theory.GroupTheory.SolvableResidualAbelianKernel
public import Theory.SpecificGroups.AlternatingSix.M10.SolvableResidual
public import Theory.Representation.HexacodeAction.CoverRecognition

/-!
# The actual triple cover and cubic fusion in J.2.7

Restrict the literal Aut(A₆) marking to C_G(B), then its perfect residual,
to construct the map L_B → A₆. In the M₁₀ quotient every cubic lies in the
perfect inner A₆. Since the central kernel B is abelian, the commutator of
the constructed extraspecial Sylow lies in L_B. That commutator is exactly
B, so the covering map has kernel of order three, with its original ambient
image. The multiplier comparison identifies L_B with the concrete even
hexacode group over the marked A₆ quotient.

The Sylow construction also gives exponent three and the single ambient
class of order-three elements with actual conjugators. Only the earlier
Sylow placement and the intervening normalizer marking/transposition fusion
from J.2.7(3),(7) remain explicit; their discharge belongs to the parent.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448), with the
triple-cover convention in A.3.5, printed p.43 (PDF p.54).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.ChapterJ CFSG.Quasithin.ChapterJ.Centralizers
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
noncomputable section
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
variable (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)

include hM in
private theorem markedCentralizer_range :
    ((CubicSylow.markedMap c e).comp (inclusion c.GB_le_NB)).range =
      AlternatingSix.M10.extension := by
  rw [MonoidHom.range_comp]
  have hi : (inclusion c.GB_le_NB).range = c.GB.subgroupOf c.NB := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hi, CubicSylow.markedMap, ← map_map]
  exact hM

def markedCentralizer : c.GB →* AlternatingSix.M10.extension :=
  ((CubicSylow.markedMap c e).comp (inclusion c.GB_le_NB)).codRestrict _
    (by
      intro x
      exact markedCentralizer_range c e hM ▸ ⟨x, rfl⟩)

theorem markedCentralizer_surjective : Function.Surjective (c.markedCentralizer e hM) := by
  intro y
  have hy : (y : MulAut (alternatingGroup (Fin 6))) ∈
      ((CubicSylow.markedMap c e).comp (inclusion c.GB_le_NB)).range :=
    (markedCentralizer_range c e hM).symm ▸ y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem markedCentralizer_ker : (c.markedCentralizer e hM).ker = c.cubicKernel := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change ((CubicSylow.markedMap c e) (inclusion c.GB_le_NB x) = 1) ↔ (x : G) ∈ c.B
  change (inclusion c.GB_le_NB x) ∈ (CubicSylow.markedMap c e).ker ↔ _
  rw [CubicSylow.markedMap_ker]
  rfl

include e hM in
/-- The cubic subgroup's commutator lies in the literal perfect residual. -/
theorem B_le_LB_of_cubic_subgroup (R : Subgroup G) (hR : R ≤ c.GB)
    (hcube : ∀ x : R, x ^ 3 = 1)
    (hcomm : (_root_.commutator R).map R.subtype = c.B) : c.B ≤ c.LB := by
  let f := c.markedCentralizer e hM
  let : IsMulCommutative f.ker := by
    rw [markedCentralizer_ker]
    exact le_centralizer_iff_isMulCommutative.mp
      (c.cubicKernel_le_center.trans (center_le_centralizer _))
  have him : (R.subgroupOf c.GB).map f ≤ solvableResidual AlternatingSix.M10.extension := by
    rw [AlternatingSix.M10.residual_eq_inner]
    rintro _ ⟨x, hx, rfl⟩
    apply AlternatingSix.M10.cube_mem_inner
    rw [← map_pow]
    have hx3 : x ^ 3 = 1 := Subtype.ext (congrArg (fun r : R => (r : G)) (hcube ⟨x, hx⟩))
    rw [hx3, map_one]
  have h := commutator_le_solvableResidual_of_image_le f (c.markedCentralizer_surjective e hM)
    (R.subgroupOf c.GB) him
  have hm := map_mono (f := c.GB.subtype) h
  rw [map_commutator, map_subgroupOf_eq_of_le hR] at hm
  rw [← map_subtype_commutator, hcomm] at hm
  exact hm

theorem LB_le_GB : c.LB ≤ c.GB := map_subtype_le _

private theorem LBInGB_le_residual : c.LB.subgroupOf c.GB ≤ solvableResidual c.GB := by
  rintro x ⟨y, hy, he⟩
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

private theorem LB_image_mem_inner (x : c.LB) :
    (c.markedCentralizer e hM) (inclusion c.LB_le_GB x) ∈
      AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension := by
  rw [← AlternatingSix.M10.residual_eq_inner,
    ← map_solvableResidual_eq (c.markedCentralizer e hM) (c.markedCentralizer_surjective e hM)]
  exact ⟨inclusion c.LB_le_GB x, c.LBInGB_le_residual x.property, rfl⟩

/-- The actual normalizer marking restricted to the perfect residual. -/
def residualA6Map : c.LB →* alternatingGroup (Fin 6) :=
  AlternatingSix.M10.innerInExtensionEquiv.toMonoidHom.comp
    (((c.markedCentralizer e hM).comp (inclusion c.LB_le_GB)).codRestrict _
      (by exact c.LB_image_mem_inner e hM))

/-- The map to A₆ retains the original normalizer marking pointwise. -/
theorem residualA6Map_marking (x : c.LB) :
    ((AlternatingSix.M10.innerInExtensionEquiv.symm (c.residualA6Map e hM x) :
      AlternatingSix.M10.extension) : MulAut (alternatingGroup (Fin 6))) =
      CubicSylow.markedMap c e ⟨x, c.GB_le_NB (c.LB_le_GB x.property)⟩ := by
  change ((AlternatingSix.M10.innerInExtensionEquiv.symm
    (AlternatingSix.M10.innerInExtensionEquiv _) : AlternatingSix.M10.extension) :
      MulAut (alternatingGroup (Fin 6))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The residual maps onto the entire marked alternating group. -/
theorem residualA6Map_surjective : Function.Surjective (c.residualA6Map e hM) := by
  intro y
  let a := AlternatingSix.M10.innerInExtensionEquiv.symm y
  have ha : (a : AlternatingSix.M10.extension) ∈
      (solvableResidual c.GB).map (c.markedCentralizer e hM) := by
    rw [map_solvableResidual_eq _ (c.markedCentralizer_surjective e hM),
      AlternatingSix.M10.residual_eq_inner]
    exact a.property
  obtain ⟨x, hx, he⟩ := ha
  let l : c.LB := ⟨x, mem_map_of_mem c.GB.subtype hx⟩
  refine ⟨l, ?_⟩
  change AlternatingSix.M10.innerInExtensionEquiv _ = y
  rw [← AlternatingSix.M10.innerInExtensionEquiv.apply_symm_apply y]
  apply congrArg AlternatingSix.M10.innerInExtensionEquiv
  apply Subtype.ext
  exact he

theorem residualA6Map_ker : (c.residualA6Map e hM).ker = c.B.subgroupOf c.LB := by
  ext x
  rw [MonoidHom.mem_ker]
  change AlternatingSix.M10.innerInExtensionEquiv _ = 1 ↔ _
  rw [map_eq_one_iff _ AlternatingSix.M10.innerInExtensionEquiv.injective]
  rw [Subtype.ext_iff]
  change (inclusion c.LB_le_GB x) ∈ (c.markedCentralizer e hM).ker ↔ _
  rw [c.markedCentralizer_ker]
  rfl

/-- The kernel's image in G is the original chosen B. -/
theorem residualA6Map_ker_image (hBL : c.B ≤ c.LB) :
    (c.residualA6Map e hM).ker.map c.LB.subtype = c.B := by
  rw [c.residualA6Map_ker]
  exact map_subgroupOf_eq_of_le hBL

/-- The covering kernel has order three once the nonsplitting step puts B in L_B. -/
theorem residualA6Map_ker_card (hB : Nat.card c.B = 3) (hBL : c.B ≤ c.LB) :
    Nat.card (c.residualA6Map e hM).ker = 3 := by
  rw [c.residualA6Map_ker, Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv, hB]

/-- The kernel is central in the literal perfect residual. -/
theorem residualA6Map_ker_central : (c.residualA6Map e hM).ker ≤ center c.LB := by
  rw [c.residualA6Map_ker]
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext ((c.LB_le_GB y.property) x hx).symm

end
end CFSG.Quasithin.ChapterJ.Centralizers.Choices

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
noncomputable section
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Conditional J.2.7(1),(11), retaining the original cubic kernel and its
marking in the concrete hexacode cover. The supplied marking and fusion
are the intervening clauses (3),(7), not any triple-cover conclusion. -/
theorem triple_cover_and_order_three_fusion (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (h7 : CubicSylow.TranspositionFusion c e) :
    c.B ≤ c.LB ∧
    (∃ a : c.LB ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp a.toMonoidHom = c.residualA6Map e hM ∧
      (c.B.subgroupOf c.LB).map a.toMonoidHom = Atlas.Codes.hexEvenCoordinate.ker) ∧
    ∃ S : Sylow 3 G, Nat.card S = 27 ∧ IsExtraspecial 3 S ∧ Monoid.exponent S = 3 ∧
      (center S).map (S : Subgroup G).subtype = c.B ∧
      (_root_.commutator S).map (S : Subgroup G).subtype = c.B ∧
      ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨D, S, hS, hcard, hextra, hexp, hcube, hcenter, hcomm, hfusion⟩ :=
    CubicSylow.exists_extraspecial_sylow_data c hB P hP hz e hM h7
  have hSle : (S : Subgroup G) ≤ c.GB := by
    rw [hS]
    exact CubicSylow.ambient_le_GB c hB e hM D.R
  have hBL := c.B_le_LB_of_cubic_subgroup e hM S hSle hcube hcomm
  have hk := c.residualA6Map_ker_card e hM hB hBL
  let : Group.IsPerfect c.LB := Group.IsPerfect.map c.GB.subtype
  obtain ⟨a, ha⟩ := Representation.Hexacode.triple_cover_equiv
    (c.residualA6Map e hM) (c.residualA6Map_surjective e hM)
    (c.residualA6Map_ker_central e hM) hk
  have hka : (c.B.subgroupOf c.LB).map a.toMonoidHom = Atlas.Codes.hexEvenCoordinate.ker := by
    rw [← c.residualA6Map_ker e hM, ← ha, ← MonoidHom.comap_ker]
    rw [map_comap_eq, MonoidHom.range_eq_top.mpr a.surjective, top_inf_eq]
  exact ⟨hBL, ⟨a, ha, hka⟩, S, hcard, hextra, hexp, hcenter, hcomm, hfusion⟩

end
end CFSG.Quasithin.ChapterJ.Centralizers.Choices
