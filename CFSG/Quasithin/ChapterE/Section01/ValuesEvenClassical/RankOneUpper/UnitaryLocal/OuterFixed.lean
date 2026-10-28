module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.Model
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Unitary

/-!
# The actual linear fixed subgroup of an outer unitary involution

Trivial centralizer of L makes conjugation faithful. Thus an element outside
L acts noninnerly on L. Transporting this action through the literal PSU₃
model and applying the proved outer-involution classification identifies
its fixed subgroup with PSL₂ over the Hermitian fixed field. The domain is
exactly the intrinsic subgroup `C_G(t).subgroupOf L`.

Source: GLS4, Chapter 4, Lemma 3.4(c), used here for the local construction
in Aschbacher–Smith E.1.14(1). This does not identify the radical quotient
of the larger local E-member; that calculation is still required.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G]

/-- The fixed linear subgroup, with the actual ambient centralizer convention
and the original matrix field retained. -/
theorem outer_fixed_equiv (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1) :
    Nonempty ((centralizer ({t} : Set G)).subgroupOf L ≃*
      PSL2MatrixGroup (FixedBy.subfield (UField f) (uconj f))) := by
  let : NeZero f := ⟨by omega⟩
  let a : MulAut L := MulAut.conjNormal t
  let eM := e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f))
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hao : ¬ ∃ x : L, a = MulAut.conj x := by
    rintro ⟨x, hx⟩
    have he : t = (x : G) := MulAut.conjNormal_injective_of_centralizer_eq_bot L hC
      (hx.trans MulAut.conjNormal_val.symm)
    exact ht (by simpa only [he] using x.property)
  obtain ⟨ef⟩ := BenderSuzuki.ZD.UnitaryAutomorphisms.outer_fixedSubgroup_equiv
    (uform f) hf (uform_form f) (card_UField f (by omega))
    (card_fixed_UField f (by omega)) (MulAut.congr eM a)
    (by rw [← map_pow, ha2, map_one])
    (fun h => hao ((MulAut.congr_inner_iff eM a).mp h))
  have hfix : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf L := by
    ext x
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    change t * (x : G) * t⁻¹ = (x : G) ↔ (x : G) * t = t * x
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  exact ⟨(MulEquiv.subgroupCongr hfix).symm.trans
    ((MulAut.fixedSubgroupCongr eM a).trans ef)⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
