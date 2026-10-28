module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Sylow-fixed orders in a natural central cover

An elementary complement to the center injects into the natural Sylow
fixed line. Multiplying by the central kernel gives the needed order bound
for the actual fixed subgroup, without imposing a splitting on the block.

Source: Aschbacher–Smith, 2.4.16(2), printed p.533.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

/-- A Sylow-fixed subgroup of the natural cover has order at most q times
the order of the block center. The complement is taken inside the actual
elementary subgroup, and its projection is injective. -/
theorem IsL2EvenBlock.card_le_of_sylow_fixed
    {n : ℕ} (hL : IsL2EvenBlock L n) (P : Sylow 2 L)
    (E : Subgroup L) (hE : E ≤ blockU L)
    (hEP : E ≤ centralizer (P : Set L)) (hZE : center L ≤ E) :
    Nat.card E ≤ 2^n * Nat.card (center L) := by
  let : IsElementaryAbelian 2 (blockU L) := hL.2.1.elementary
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (inclusion hE) (inclusion_injective hE)
  let Z := (center L).subgroupOf E
  obtain ⟨C,hC⟩ := IsElementaryAbelian.exists_isCompl 2 E Z
  let D := C.map E.subtype
  have hDE : D ≤ E := map_subtype_le _
  have hDZ : Disjoint D (center L) := by
    apply disjoint_def.mpr
    rintro x ⟨y,hy,rfl⟩ hz
    have hyZ : y ∈ Z := hz
    exact congrArg Subtype.val (hC.disjoint.le_bot ⟨hyZ,hy⟩)
  have hDcard := hL.card_le_of_sylow_fixed_disjoint_center P D (hDE.trans hE)
    (hDE.trans hEP) hDZ
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z C
    (by rw [normalizer_eq_top]; exact le_top)
  have hZn : Z.Normal := inferInstance
  rw [hC.disjoint.eq_bot,hC.sup_eq_top,card_bot,one_mul,Nat.card_congr topEquiv.toEquiv] at hc
  have hcD : Nat.card C = Nat.card D := (card_map_of_injective E.subtype_injective).symm
  have hcZ : Nat.card Z = Nat.card (center L) :=
    Nat.card_congr (subgroupOfEquivOfLe hZE).toEquiv
  rw [← hc,hcD,hcZ,mul_comm]
  exact Nat.mul_le_mul_right _ hDcard
end CFSG.Quasithin.ChapterC
