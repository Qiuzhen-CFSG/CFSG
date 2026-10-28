module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralCommutator
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup

/-!
# Elimination of the central-kernel displacement

In a supplement UAC, the auxiliary factors A and C centralize Uˣ.
For an original K-centralizer element its commutator with Uˣ is therefore
a single U-commutator. Normalization of K puts it in C(K), and genuine
fixed-vector lifting makes it trivial. This is the pointwise final step
of C.5.6(7), retaining the central cover.
-/
public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.centralizer_centralizes_of_supplement
    (h : Setup R K F) {x : G} (hx : x ∈ normalizer (R : Set G))
    (A P C : Subgroup G)
    (hAU : A ≤ centralizer (U K : Set G))
    (hAV : A ≤ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (hPV : P ≤ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (hPN : P ≤ normalizer (U K ⊔ A : Subgroup G))
    (hCK : C ≤ centralizer (K : Set G)) (hCP : C ≤ (U K ⊔ A) ⊔ P) :
    C ≤ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hNC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hVC : V ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (h.conjugate_le hx).trans (h.normalizes.trans hNC)
  intro c hc v hv
  have hm : c ∈ ((U K ⊔ A : Subgroup G) : Set G) * (P : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hPN]
    exact hCP hc
  obtain ⟨u,hu,p,hp,hup⟩ := hm
  have hu' : u ∈ (U K : Set G) * (A : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (hAU.trans (Subgroup.centralizer_le_normalizer _))]
    exact hu
  obtain ⟨w,hw,a,ha,hwa⟩ := hu'
  have hcomm : ⁅c,v⁆ = ⁅w,v⁆ := by
    rw [← hup,← hwa,commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_mul_comm.mpr (hPV hp v hv).symm]
    simp only [mul_one]
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_mul_comm.mpr (hAV ha v hv).symm]
    simp
  have hcommC : ⁅c,v⁆ ∈ centralizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mp hVC (commutator_mem_commutator (hCK hc) hv)
  have hz := h.central_commutator_eq_one hw (h.conjugate_le hx hv) (hcomm ▸ hcommC)
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hcomm.trans hz)).symm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
