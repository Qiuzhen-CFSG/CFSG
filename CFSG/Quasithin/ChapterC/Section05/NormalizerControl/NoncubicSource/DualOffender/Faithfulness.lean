module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedCore
public import Theory.Representation.BinaryTwoLayerFaithfulness
/-!
# Faithfulness on the original C.5.13 moved module

The source omega-center span is two-reduced. Its canonical centralizer
quotient consequently has trivial two-core. The image of the normal conjugate
span L is normal in this quotient. On I=[V,L], the action kernel fixes I and
acts trivially on V/I, hence is a two-group and is trivial. The inverse-dual
action is faithful as well. All actions retain the original L-image inside
N/C_N(V); no quotient of the central layer of I is taken.

Quasisimplicity is not needed for this step. In particular, faithfulness
makes no irreducibility assertion: a commutator-generated central cover
can still have a nonzero fixed subspace.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G]
/-- Reducedness makes the original normal-closure image faithful on its moved module and dual. -/
theorem moved_faithful_of_reduced (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hV : Theory.GroupTheory.IsPReduced 2 V) :
    Function.Injective (movedRepresentation V K) ∧
      Function.Injective (movedRepresentation V K).dual := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let : (closureImage V K).Normal := Normal.map inferInstance q
    (QuotientGroup.mk'_surjective (centralizer (V : Set G)))
  have hd (g : closureImage V K) (w : Additive V) :
      centralizerQuotient V g w - w ∈ movedSpace V K := by
    obtain ⟨k,hk,hkg⟩ := g.property
    change ((centralizerQuotient V (g : G ⧸ centralizer (V : Set G)) w - w).toMul : G) ∈
      ⁅V,normalClosure (K : Set G)⁆
    rw [← hkg]
    have he : ((centralizerQuotient V (q k) w - w).toMul : G) =
        ⁅k,(w.toMul : G)⁆ := by
      simp only [toMul_sub,div_eq_mul_inv]
      rfl
    rw [he,commutator_comm]
    exact commutator_mem_commutator hk w.toMul.property
  have hf : Function.Injective (movedRepresentation V K) :=
    normal_two_layer_restriction_faithful (centralizerQuotient V) (movedSpace V K)
      (closureImage V K)
      ((asGroupHom_injective_iff (centralizerQuotient V)).mp (centralizerQuotient_faithful V))
      hd hV.quotient_pCore_eq_bot
  exact ⟨hf,dual_faithful_of_faithful _ hf⟩

variable [Finite G]
open ConjugateSource.RankOne
/-- The genuine noncubic source supplies reducedness, so neither faithful-action conclusion is an extra premise. -/
theorem noncubic_source_moved_faithful (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    Function.Injective (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ∧
      Function.Injective (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  exact moved_faithful_of_reduced (V.subgroupOf N) (K.subgroupOf N) hs.2.2.2.2.2.2.1
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
