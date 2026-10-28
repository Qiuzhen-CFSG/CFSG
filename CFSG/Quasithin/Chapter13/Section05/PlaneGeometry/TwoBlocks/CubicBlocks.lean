module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.CubicPair
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Cubic actors produce the original pair of A₃ blocks

Complementary supports of order four and the two cross-fixation
identities construct the actual commuting factors [V,Pᵢ]Pᵢ. Coprime
commutator idempotence supplies their full cubic action. The join is
V(P₁P₂), with its original embedded two-core V and an A₄² equivalence.
The native plane family and the marked coprime-kernel lift supply exactly
these action identities in the source application.

Source: Aschbacher–Smith 13.5.6, printed p.917.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

omit [Finite G] in
private theorem cubic_twoPerfect (P:Subgroup G) (hP:Nat.card P=3) : IsPPerfect 2 P := by
  apply (pResidual_eq_top_iff 2 P).mp
  apply top_unique
  intro p _
  exact mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (hP ▸ orderOf_dvd_natCard p))

theorem cubic_blocks_of_axes (P₁ P₂:Subgroup G)
    (hL₁:P₁≤L⊔(T:Subgroup G)) (hL₂:P₂≤L⊔(T:Subgroup G))
    (hp₁:Nat.card P₁=3) (hp₂:Nat.card P₂=3)
    (hpp:P₁≤centralizer (P₂:Set G))
    (hu₁:Nat.card (image d ⁅V,P₁⁆)=4) (hu₂:Nat.card (image d ⁅V,P₂⁆)=4)
    (hcompl:IsCompl (image d ⁅V,P₁⁆) (image d ⁅V,P₂⁆))
    (hf₁:∀a∈(actor d P₁ hL₁).range,∀v∈image d ⁅V,P₂⁆,
      naturalRepresentation (Fin 6) a v=v)
    (hf₂:∀a∈(actor d P₂ hL₂).range,∀v∈image d ⁅V,P₁⁆,
      naturalRepresentation (Fin 6) a v=v) :
    ChapterC.IsAlternatingBlock (⁅V,P₁⁆⊔P₁ : Subgroup G) 3 ∧
    ChapterC.IsAlternatingBlock (⁅V,P₂⁆⊔P₂ : Subgroup G) 3 ∧
    (⁅V,P₁⁆⊔P₁) ≤ centralizer ((⁅V,P₂⁆⊔P₂ : Subgroup G):Set G) ∧
    (⁅V,P₁⁆⊔P₁)⊔(⁅V,P₂⁆⊔P₂)=V⊔(P₁⊔P₂) ∧
    Nonempty ((V⊔(P₁⊔P₂) : Subgroup G)≃*AlternatingFourPair.Model) ∧
    (V⊔(P₁⊔P₂)).pCoreIn 2=V := by
  let := elementary d
  have hn₁ := hL₁.trans d.normalizes_V
  have hn₂ := hL₂.trans d.normalizes_V
  have hUV₁ : ⁅V,P₁⁆≤V := le_normalizer_iff_commutator_le_left.mp hn₁
  have hUV₂ : ⁅V,P₂⁆≤V := le_normalizer_iff_commutator_le_left.mp hn₂
  let : IsElementaryAbelian 2 (⁅V,P₁⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion hUV₁) (inclusion_injective hUV₁)
  let : IsElementaryAbelian 2 (⁅V,P₂⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion hUV₂) (inclusion_injective hUV₂)
  have hgen : ⁅V,P₁⁆⊔⁅V,P₂⁆=V := by
    apply QuadraticSource.image_injective_on_subgroups d (sup_le hUV₁ hUV₂) le_rfl
    rw [image_sup d _ _ hUV₁ hUV₂,hcompl.sup_eq_top,image_module d]
  have hc₁ := centralizes_of_fixes d P₁ ⁅V,P₂⁆ hL₁ hUV₂ hf₁
  have hc₂ := centralizes_of_fixes d P₂ ⁅V,P₁⁆ hL₂ hUV₁ hf₂
  have hUU : ⁅V,P₁⁆≤centralizer ((⁅V,P₂⁆ : Subgroup G) : Set G) := by
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm' (⟨v,hUV₂ hv⟩:V) ⟨u,hUV₁ hu⟩)
  have hc : ⁅V,P₁⁆⊔P₁ ≤ centralizer ((⁅V,P₂⁆⊔P₂ : Subgroup G):Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le hUU hc₁
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp hc₂) hpp
  have hmu₁ := commutator_isPPerfect_idempotent P₁ V (cubic_twoPerfect P₁ hp₁)
    (IsElementaryAbelian.isPGroup 2 V) hn₁
  have hmu₂ := commutator_isPPerfect_idempotent P₂ V (cubic_twoPerfect P₂ hp₂)
    (IsElementaryAbelian.isPGroup 2 V) hn₂
  obtain ⟨hb₁,hb₂,he,hq⟩ := ChapterC.cubic_pair_product ⁅V,P₁⁆ ⁅V,P₂⁆ P₁ P₂
    ((image_card d _ hUV₁).symm.trans hu₁) ((image_card d _ hUV₂).symm.trans hu₂)
    hp₁ hp₂ (normalizer_commutator_ge_right V P₁) (normalizer_commutator_ge_right V P₂)
    hmu₁ hmu₂ hc
  rw [hgen] at he hq
  refine ⟨hb₁,hb₂,hc,?_,he,hq⟩
  calc
    _=(⁅V,P₁⁆⊔⁅V,P₂⁆)⊔(P₁⊔P₂) := by ac_rfl
    _=V⊔(P₁⊔P₂) := by rw [hgen]
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
