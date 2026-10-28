module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointCentralizer
public import Theory.Representation.BinaryNaturalMultiplicity
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The original point-centralizer multiplicity action

Inside the literal J/O₂(J), let C centralize the natural image of L₁.
Normality of L₁ makes C normal, hence O₂(C) = 1. The original homogeneous
coordinates construct a faithful representation of C on the multiplicity
space. The same coordinates retain the natural L₁ action and its exact
O₂(L₁) kernel; no natural constituent is assumed invariant under C.

For every subgroup A of C the fixed codimension on U_J/V₁ is exactly
(n-1) times its multiplicity fixed codimension. In the actual Case I escape,
the original nonzero F.9 actor lies in C and has the quadratic upper bound
two times its rank. Since n is four or five, it is a strong quadratic
offender on the faithful multiplicity action. The original H₁, its minimal
parabolic structure, its residual image, and both actor inclusions are kept.

This supplies the actual multiplicity action, not the remaining B.6.9
chief-factor inequality. To exclude the escape one must still connect the
minimal parabolic H₁ to that multiplicity action and apply the chief bound.
In particular O₂(C) = 1 alone does not exclude strong offenders.

Source: Aschbacher--Smith, proof of 12.9.5, Case I, printed pp.860--861,
using 12.8.5(1) and B.6.9(1), pp.850 and115 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The centralizer of the literal natural image in the local core quotient. -/
@[expose] def localNaturalCentralizer (F : InvariantFlag T V n)
    (L J : Subgroup G) : Subgroup (J ⧸ pCore 2 J) :=
  centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) :
    Set (J ⧸ pCore 2 J))

/-- This normal centralizer has trivial intrinsic two-core. -/
theorem localNaturalCentralizer_core
    (F : InvariantFlag T V n) (L J : Subgroup G)
    [((F.Li L 1).subgroupOf J).Normal] :
    pCore 2 (localNaturalCentralizer F L J) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := ((F.Li L 1).subgroupOf J).map q
  let : N.Normal := (inferInstance : ((F.Li L 1).subgroupOf J).Normal).map
    q (QuotientGroup.mk'_surjective _)
  let : (localNaturalCentralizer F L J).Normal := by
    change (Subgroup.centralizer (N : Set (J ⧸ pCore 2 J))).Normal
    infer_instance
  rw [pCore_eq_comap_of_normal 2 (localNaturalCentralizer F L J),
    pCore_quotient_pCore_eq_bot,MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff _).mpr Subtype.val_injective

omit [Finite G] in
/-- Construct the faithful multiplicity action in the given original coordinates. -/
theorem local_centralizer_multiplicity
    (F : InvariantFlag T V n) {J : Subgroup G}
    (hLJ : F.Li L 1 ≤ J) [IsElementaryAbelian 2 (F.UH J)]
    (a : LocalQuotientAction J (F.UH J) (F.Vi 1)) (hd : 2 ≤ n-1)
    (α : F.Li L 1 →* BinaryLinear.OuterCyclic.LinearGroup (n-1))
    (hα : Function.Surjective α) (r : ℕ)
    (e : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃ₗ[ZMod 2]
      (Fin r → Fin (n-1) → ZMod 2))
    (he : ∀ k u i,
      e (a.representation (QuotientGroup.mk' (pCore 2 J) (inclusion hLJ k)) u) i =
        α k (e u i)) :
    ∃ μ : Representation (ZMod 2) (localNaturalCentralizer F L J) (Fin r → ZMod 2),
      Function.Injective μ ∧
      (∀ c v j i, e (a.representation c.val v) i j = μ c (fun k => e v k j) i) ∧
      ∀ (A : Subgroup (J ⧸ pCore 2 J)), A ≤ localNaturalCentralizer F L J →
        fixedCodim a.representation A = (n-1) * fixedCodim μ (A.subgroupOf (localNaturalCentralizer F L J)) ∧
        (IsQuadratic a.representation A → IsQuadratic μ (A.subgroupOf (localNaturalCentralizer F L J))) := by
  let C := localNaturalCentralizer F L J
  let q := QuotientGroup.mk' (pCore 2 J)
  let σ := a.representation.comp (q.comp (inclusion hLJ))
  let τ := a.representation.comp C.subtype
  have hc : ∀ (c : C) (k : F.Li L 1) v, τ c (σ k v) = σ k (τ c v) := by
    intro c k v
    change a.representation c.val (a.representation (q (inclusion hLJ k)) v) =
      a.representation (q (inclusion hLJ k)) (a.representation c.val v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    apply congrArg (fun x => a.representation x v)
    exact (mem_centralizer_iff.mp c.property (q (inclusion hLJ k))
      (mem_map_of_mem q k.property)).symm
  obtain ⟨μ,hμ⟩ := BinaryNaturalMultiplicity.exists_coordinates hd α hα σ τ hc e he
  refine ⟨μ,BinaryNaturalMultiplicity.faithful τ e μ hμ
    (a.faithful.comp Subtype.val_injective),hμ,?_⟩
  intro A hA
  have hh : fixedCodim τ (A.subgroupOf C) = fixedCodim a.representation A :=
    by
      change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp C.subtype) _) = _
      rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hA]
      rfl
  refine ⟨hh.symm.trans (BinaryNaturalMultiplicity.fixedCodim_eq τ e μ hμ _),?_⟩
  intro hquad
  apply BinaryNaturalMultiplicity.quadratic τ e μ hμ (by omega)
  intro c hc b hb v
  exact hquad c.val hc b.val hb v

/-- The original Case I escape forces a faithful strong offender on its
actual multiplicity space. The actor remains the same B in R₁ and H₁;
its natural-coordinate cost is exactly n-1, not an assumed lower bound. -/
theorem point_centralizer_escape_strong_multiplicity
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C₁ : ComponentGeometry F L)
    (hout : ¬ pointQuotientCentralizer C₁ ≤ normalizer (L : Set G)) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T H₁ ∧
      (pResidual 2 H₁).map H₁.subtype ≤ pointQuotientCentralizer C₁ ∧
      let J := F.Li L 1 ⊔ H₁
      ∃ hJ : J ∈ F.Hz L (normalizer (L : Set G)),
        ((F.Li L 1).subgroupOf J).Normal ∧
        ∃ hU : IsElementaryAbelian 2 (F.UH J),
          let := hU
          ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
            quadraticRatio a.representation ≤ 2 ∧
            let q := QuotientGroup.mk' (pCore 2 J)
            let C := localNaturalCentralizer F L J
            ∃ B : Subgroup J,
              B ≤ (F.Ri L 1).subgroupOf J ∧ B ≤ H₁.subgroupOf J ∧
              IsElementaryTwo (B.map q) ∧ IsQuadratic a.representation (B.map q) ∧
              fixedCodim a.representation (B.map q) ≤ 2 * rank (B.map q) ∧
              B.map q ≤ C ∧
              (((pResidual 2 H₁).map H₁.subtype).subgroupOf J).map q ≤ C ∧
              pCore 2 C = ⊥ ∧
              ∃ α : F.Li L 1 →* BinaryLinear.OuterCyclic.LinearGroup (n-1),
                Function.Surjective α ∧ α.ker = pCore 2 (F.Li L 1) ∧
              ∃ r : ℕ, 0 < r ∧
                ∃ e : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃ₗ[ZMod 2]
                    (Fin r → Fin (n-1) → ZMod 2),
                  (∀ (k : F.Li L 1) u i,
                    e (a.representation (q (inclusion (F.Li_one_le_of_mem_Hz hJ) k)) u) i =
                      α k (e u i)) ∧
                ∃ μ : Representation (ZMod 2) C (Fin r → ZMod 2),
                  Function.Injective μ ∧
                  (∀ c v j i, e (a.representation c.val v) i j =
                    μ c (fun k => e v k j) i) ∧
                  (∀ (A : Subgroup (J ⧸ pCore 2 J)), A ≤ C →
                    fixedCodim a.representation A =
                      (n-1) * fixedCodim μ (A.subgroupOf C)) ∧
                  IsStrongOffender μ ((B.map q).subgroupOf C) ∧
                  IsQuadratic μ ((B.map q).subgroupOf C) := by
  obtain ⟨H₁,hstar,hmin,hr,hJ,hN,hU,a,ha,B,hBR,hBH,hB,hquad,hbound,hBC,hRC,
    α,hα,hker,r,hrpos,e,he⟩ :=
      point_centralizer_escape_quadratic_coordinates h hn earlier F hab C₁ hout
  let J := F.Li L 1 ⊔ H₁
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := localNaturalCentralizer F L J
  let := hN
  let := hU
  obtain ⟨μ,hμ,heμ,hcost⟩ := local_centralizer_multiplicity F
    (F.Li_one_le_of_mem_Hz hJ) a (by rcases hn with rfl | rfl <;> decide) α hα r e he
  have hmap : ((B.map q).subgroupOf C).map C.subtype = B.map q :=
    map_subgroupOf_eq_of_le hBC
  have hBe : IsElementaryTwo ((B.map q).subgroupOf C) := by
    let := hB.2
    refine ⟨?_,IsElementaryAbelian.subgroupOf hBC⟩
    intro hb
    apply hB.1
    rw [←hmap,hb,Subgroup.map_bot]
  have hrank : rank ((B.map q).subgroupOf C) = rank (B.map q) := by
    exact (rank_map_injective C.subtype C.subtype_injective _).symm.trans (congrArg rank hmap)
  have hcostB : fixedCodim a.representation (B.map q) =
      (n-1) * fixedCodim μ ((B.map q).subgroupOf C) := (hcost (B.map q) hBC).1
  have hstrong : IsStrongOffender μ ((B.map q).subgroupOf C) := by
    refine ⟨hBe,?_⟩
    have hpos := hBe.rank_pos
    rw [hcostB,←hrank] at hbound
    have hd : 3 ≤ n-1 := by omega
    have hs : 3 * fixedCodim μ ((B.map q).subgroupOf C) ≤
        2 * rank ((B.map q).subgroupOf C) :=
      (Nat.mul_le_mul_right _ hd).trans hbound
    omega
  exact ⟨H₁,hstar,hmin,hr,hJ,hN,hU,a,ha,B,hBR,hBH,hB,hquad,hbound,hBC,hRC,
    localNaturalCentralizer_core F L J,α,hα,hker,r,hrpos,e,he,μ,hμ,heμ,
    fun A hA => (hcost A hA).1,hstrong,(hcost (B.map q) hBC).2 hquad⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
