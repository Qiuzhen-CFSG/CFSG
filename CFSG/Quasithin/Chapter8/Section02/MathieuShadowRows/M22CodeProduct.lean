module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreSections
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourProduct
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourProduct

/-!
# The full product action on the original M22-code core section

For a selected degree-one M22-code pair, the literal P/U is elementary of
order 2^10. The full residual kernel on B/U extends to P/U by the two
original conjugate factors. The residual and pair action images commute;
the centreless pair quotient makes them disjoint. Thus the full action
kernel is O₂(RI)=O₂(R)O₂(I), and its quotient is the product of the original
two-core quotients.

This intentionally reuses the private generic join-action argument of
HermitianSourceFieldFourProduct. That argument has no Hermitian premise;
the eight-space specialization is not used. The M22-code application supplies
the actual rank-five and rank-four data and the full B/U kernel.
Source: Aschbacher--Smith E.2.10, E.2.13--14 and 8.2.8(4), printed
pp.222--226,718--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G]

/-- The literal rank-ten section and the full original product action,
including both restriction kernels and quotient representatives. -/
@[expose] def M22CodePairProductAction (R I V U : Subgroup G) : Prop :=
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
          Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^10 ∧
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          let B₀ := V ⊓ I.pCoreIn 2
          ∃ hRB : R ≤ normalizer (B₀ : Set G),
            ∃ hBU : (U.subgroupOf B₀).Normal, letI := hBU
              let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl)
                (show B₀ ≤ I.pCoreIn 2 from inf_le_right)
              (∀ (r : R) (b : B₀ ⧸ U.subgroupOf B₀),
                q (sectionAction R B₀ U hRB (le_sup_left.trans hYU) r b) =
                  f (inclusion le_sup_left r) (q b)) ∧
              ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
                ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
                  (inclusion le_sup_left r * inclusion le_sup_right a)) =
                  (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a)

/-- The original degree-one M22-code pair supplies the full product action.
Every normality statement is relative to the actual join R∨I. -/
theorem selected_m22_code_full_product_action
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G))
    (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = 5)
    (hu : rank U = 4)
    (hRI : R ≤ normalizer (I : Set G))
    (hRU : R ≤ normalizer (U : Set G))
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (hRB : R ≤ normalizer (V ⊓ I.pCoreIn 2 : Set G))
    (hBU : (U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal)
    (hk : letI := hBU; (sectionAction R (V ⊓ I.pCoreIn 2) U hRB hRU).ker = pCore 2 R) :
    M22CodePairProductAction R I V U := by
  let := hBU
  have hB (r : R) : (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔
      r ∈ pCore 2 R := by
    rw [←hk]
    exact (mem_sectionAction_ker R (V ⊓ I.pCoreIn 2) U hRB hRU r).symm
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPi : (I.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  have hP : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 := by
    rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
    exact (selected_one_core_product s).symm
  obtain ⟨hUN,hI⟩ := selected_core_action_kernel s U hU
  obtain ⟨hYP,hYU,hUP,hker,hcore,hR,hI',e,heq⟩ :=
    pair_join_action R I V U hRI hRU hIC hcomm i hP hB hUN hI (selected_centerless s)
  let := hUP
  obtain ⟨hUP',hEl,hcard,_⟩ := selected_core_section_of_ranks s U hU hIC 5 4 hr hu
  refine ⟨hYP,hYU,hUP,hEl,hcard,hker,hcore,hR,hI',hRB,hBU,?_,e,heq⟩
  intro r b
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (V ⊓ I.pCoreIn 2)) b
  rfl

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
