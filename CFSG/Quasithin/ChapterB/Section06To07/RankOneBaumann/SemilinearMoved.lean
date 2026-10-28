module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SemilinearSource
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer

/-!
# The semilinear Baumann theorem on the original moved subgroup

The B.6.9 marker belongs to W=[U,O²(H)], and U need not split over its
residual-fixed space. Reducedness alone proves C_H(W)=C_H(U), hence W
remains reduced and is moved by the original J(T). Applying the normal
semilinear theorem to W gives both the original Sylow conclusion and the
source alpha identity with C_W(J(T)). All quotient actions below use the
actual ambient conjugation and the actual fixed kernel.
Source: Aschbacher–Smith B.6.10(2),(3), printed p.117; E.2.3, pp.216–217.
-/

open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]

public local instance semilinear_moved_elementary
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] :
    IsElementaryAbelian 2 (⁅U,pResidual 2 G⁆ : Subgroup G) :=
  IsElementaryAbelian.of_le (commutator_le_left U _)

public theorem semilinear_moved_baumann_sylow_and_alpha
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = ρ (q g) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let W := ⁅U,pResidual 2 G⁆
  have hCW : centralizer (W : Set G) = centralizer (U : Set G) :=
    hU.centralizer_moved_eq U
  have hkerW : q.ker = centralizer (W : Set G) := hker.trans hCW.symm
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq hCW)
  have heW : ∀ a v,
      f (NormalElementaryQuotient.representation W q hq hkerW a v) = ρ a (f v) := by
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
  obtain ⟨hs,ha⟩ := semilinear_baumann_sylow_and_alpha T hP W (hU.moved U) hJW
    q hq hkerW L e ρ hfaith hnat hF f hf heW hkW
  exact ⟨hs,ha.trans (sup_comm _ _)⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann
