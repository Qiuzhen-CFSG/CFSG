module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source

/-!
# The original moved-module conclusion of Baumann's lemma

Use the marked natural quotient of the literal subgroup W=[U,O²(H)]
from B.6.10. Its faithfulness proves C_H(W)=C_H(U), so W is reduced and
the original Thompson subgroup still moves it. The complete natural
Baumann theorem then gives both the Sylow conclusion and the source
identity Ω₁(Z(J(T)))=C_W(J(T)) C_{Ω₁(Z(J(T)))}(O²(H)).
The quotient map is equivariant for actual ambient conjugation, and its
kernel is the actual residual fixed space; U need not split.
Source: Aschbacher–Smith B.6.10(2),(3), printed p.117.
-/

open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

/-- The actual commutator subgroup inherits its elementary structure. -/
public local instance moved_elementary (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] :
    IsElementaryAbelian 2 (⁅U,pResidual 2 G⁆ : Subgroup G) :=
  IsElementaryAbelian.of_le (commutator_le_left U (pResidual 2 G))

public theorem natural_moved_baumann_sylow_and_alpha
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = N (q g) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let W := ⁅U,pResidual 2 G⁆
  have hWU : W ≤ U := commutator_le_left _ _
  have hkerW : q.ker = centralizer (W : Set G) := by
    apply le_antisymm (hker.le.trans (centralizer_le hWU))
    intro g hg
    change q g = 1
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨w,rfl⟩ := hf v
    have hw : Additive.ofMul (MulAut.conjNormal g w.toMul) = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change g * (w.toMul : G) * g⁻¹ = w.toMul
      rw [← hg w.toMul w.toMul.property,mul_inv_cancel_right]
    have hew := he g w
    rw [hw] at hew
    change f w = (q g).val.mulVec (f w) at hew
    change (q g).val.mulVec (f w) = (1 : Matrix (Fin 2) (Fin 2) F).mulVec (f w)
    simpa only [Matrix.one_mulVec] using hew.symm
  have hCW : centralizer (W : Set G) = centralizer (U : Set G) := hkerW.symm.trans hker
  have hW : IsPReduced 2 W := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let e := QuotientGroup.quotientMulEquivOfEq hCW
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso 2 e]
    exact hU.quotient_pCore_eq_bot
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq hCW)
  have heW : ∀ a v, f (NormalElementaryQuotient.representation W q hq hkerW a v) = N a (f v) := by
    intro a v
    obtain ⟨g,rfl⟩ := hq a
    have hv : NormalElementaryQuotient.representation W q hq hkerW (q g) v =
        Additive.ofMul (MulAut.conjNormal g v.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W q hq hkerW g v
    rw [hv]
    exact he g v
  have hkW : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation W q hq hkerW) ((pResidual 2 G).map q) := by
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image W q hq hkerW]
    exact hk v
  obtain ⟨hs,ha⟩ := natural_baumann_sylow_and_alpha T hP W hW hJW q hq hkerW f hf heW hkW
  exact ⟨hs,ha.trans (sup_comm _ _)⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann
