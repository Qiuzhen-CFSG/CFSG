module

public import Theory.GroupTheory.Commutator.CentralizingComplement
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.Representation.InvertedCubicTransvection
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# The cubic action branch of C.5.13

In the literal quotient X₁/C_X₁(V₁), the marked cubic is normal because
an inverting involution acts as a transvection and a Sylow two-subgroup
has order two. Hence its conjugate closure has the same image. The
short-block displacement theorem identifies [V₁,K₁] with U(K₁), so the
original module is normal in X₁. This supplies the required normalizer
bound in the A₃ action branch. The earlier source construction of V₁
and its transvection, and the non-A₃ branches, are separate inputs.

Source: Aschbacher–Smith, C.5.13, printed p.162.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {X₁ : Type*} [Group X₁] [Finite X₁]

/-- The cubic image of the original K₁ is normal in the literal action quotient
X₁/C_X₁(V₁), so its conjugate closure has the same image. This proves the
representation step of the A₃ branch before the remaining short-block lift. -/
theorem cubic_block_closure_image
    (V₁ K₁ : Subgroup X₁) [V₁.Normal] [IsElementaryAbelian 2 V₁]
    (ρ : Representation (ZMod 2) (X₁ ⧸ centralizer (V₁ : Set X₁)) (Additive V₁))
    (hρ : Function.Injective ρ.asGroupHom)
    (Tstar : Sylow 2 (X₁ ⧸ centralizer (V₁ : Set X₁))) (hT : Nat.card Tstar = 2)
    (hK : Nat.card (K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁)))) = 3)
    (x : X₁) (hx : IsInvolution (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x))
    (hinvert : ∀ c ∈ K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁))),
      QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x * c *
        (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x)⁻¹ = c⁻¹)
    (htrans : LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x)) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V₁)) :
    (K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁)))).Normal ∧
      (conjugateSpanBy K₁ ⊤).map (QuotientGroup.mk' (centralizer (V₁ : Set X₁))) =
        K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁))) := by
  let q := QuotientGroup.mk' (centralizer (V₁ : Set X₁))
  let B := K₁.map q
  let : IsCyclic B := isCyclic_of_prime_card hK
  obtain ⟨c,hc⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic B)
  have hgen : zpowers (c : X₁ ⧸ centralizer (V₁ : Set X₁)) = B := by
    change zpowers (B.subtype c) = B
    rw [← MonoidHom.map_zpowers B.subtype c,hc,← MonoidHom.range_eq_map,range_subtype]
  have hc3 : orderOf (c : X₁ ⧸ centralizer (V₁ : Set X₁)) = 3 := by
    rw [← Nat.card_zpowers,hgen]
    exact hK
  have hN : B.Normal := hgen ▸ cubic_normal_of_order_two_sylow_transvection
    ρ hρ Tstar hT (q x) c hx hc3 (hinvert c c.property) htrans
  refine ⟨hN,?_⟩
  rw [map_conjugateSpanBy]
  apply le_antisymm ?_ (le_conjugateSpanBy _ _)
  let := hN
  exact conjugateSpanBy_le le_rfl (by rw [normalizer_eq_top]; exact le_top)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl

namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {X₁ : Type*} [Group X₁] [Finite X₁]
open ConjugateSource
omit [Finite X₁] in
/-- A normal block image makes its displacement on the normal module normal. -/
theorem commutator_normal_of_centralizer_image_normal
    (V K : Subgroup X₁) [V.Normal]
    (hB : (K.map (QuotientGroup.mk' (centralizer (V : Set X₁)))).Normal) : ⁅V,K⁆.Normal := by
  let C := centralizer (V : Set X₁)
  let q := QuotientGroup.mk' C
  let B := (K.map q).comap q
  let : B.Normal := hB.comap q
  have he : C ⊔ K = B := by simp only [B,q,comap_map_eq,QuotientGroup.ker_mk',sup_comm]
  have hn : K ≤ normalizer (V : Set X₁) := by rw [normalizer_eq_top]; exact le_top
  rw [commutator_eq_of_centralizing_sup he (show C ≤ centralizer (V : Set X₁) from le_rfl) hn]
  infer_instance

/-- C.5.13's A₃ normalizer conclusion on the actual covering module.
Normality of the cubic image makes [V₁,K₁] normal. The genuine short-block
and fixed-core bounds identify this commutator with the original U(K₁),
so the entire X₁ normalizes that module. -/
theorem cubic_block_module_normal
    (V₁ K₁ : Subgroup X₁) [V₁.Normal] [IsElementaryAbelian 2 V₁]
    (hshort : IsShort K₁)
    (hUV : RankOne.U K₁ ≤ V₁)
    (hVN : V₁ ≤ normalizer (K₁ : Set X₁))
    (hVC : V₁ ≤ centralizer (RankOne.U K₁ : Set X₁))
    (ρ : Representation (ZMod 2) (X₁ ⧸ centralizer (V₁ : Set X₁)) (Additive V₁))
    (hρ : Function.Injective ρ.asGroupHom)
    (Tstar : Sylow 2 (X₁ ⧸ centralizer (V₁ : Set X₁))) (hT : Nat.card Tstar = 2)
    (hK : Nat.card (K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁)))) = 3)
    (x : X₁) (hx : IsInvolution (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x))
    (hinvert : ∀ c ∈ K₁.map (QuotientGroup.mk' (centralizer (V₁ : Set X₁))),
      QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x * c *
        (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x)⁻¹ = c⁻¹)
    (htrans : LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom (QuotientGroup.mk' (centralizer (V₁ : Set X₁)) x)) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V₁)) : (RankOne.U K₁).Normal := by
  have hN := (cubic_block_closure_image V₁ K₁ ρ hρ Tstar hT hK x hx hinvert htrans).1
  have hC := commutator_normal_of_centralizer_image_normal V₁ K₁ hN
  have hUK : ⁅RankOne.U K₁,K₁⁆ = RankOne.U K₁ := by
    have hi := commutator_isPPerfect_idempotent K₁ (pCoreIn 2 K₁)
      hshort.twoPerfect (isPGroup_pCoreIn 2 K₁)
      (K₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K₁ (pCore 2 K₁)))
    simpa only [RankOne.U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  have he : ⁅V₁,K₁⁆ = RankOne.U K₁ := by
    apply le_antisymm
    · rw [commutator_comm]
      exact RankOne.block_fixer_displacement hshort hVN hVC
    · exact hUK.symm.trans_le (commutator_mono hUV le_rfl)
  rwa [he] at hC
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
