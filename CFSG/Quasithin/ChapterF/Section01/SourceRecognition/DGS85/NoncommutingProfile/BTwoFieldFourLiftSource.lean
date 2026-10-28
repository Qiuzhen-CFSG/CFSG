module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourActionSource
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.SplitRecognition

/-!
# Lifting the field-four beta comparison to the actual split endpoint

The source complement acts faithfully on its minus extraspecial core. The
alternating-action comparison and the native J₂ complement lift the earlier
central-quotient comparison to an isomorphism of the entire beta enlargement.
The core inclusion square is exact, and the central-quotient square and the
literal original PSL₂(4) quotient marking are retained on every element.

The enlargement is the order-1920 endpoint. Identifying both full original
parabolics and their common full Borel remains a further amalgam argument;
no source path parameter follows from this single-endpoint comparison.
Source: DGS, Groups and Graphs (1985), (5.16), p.117 and (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourLiftAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

open MinusExtraspecial.AlternatingAction
local notation "Jβ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
local notation "eJ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.coreModelEquiv
local notation "jJ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv

/-- The full original beta enlargement is the native J₂ first endpoint, with
its original quotient and exact core and central-quotient squares. -/
theorem original_bTwo_field_four_beta_enlargement_equiv
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    let X := enlargedEndpoint L S 1
    let N := pCore 2 X
    Nat.card X = 1920 ∧ Nat.card ((commonBorel L S).pCoreIn 2) = 128 ∧
      Nat.card (X ⊓ commonBorel L S : Subgroup G) = 384 ∧
      ∃ eX : (X ⧸ N) ≃* PSL(2,K),
        (∀ x : L 1, eX (QuotientGroup.mk' N
          (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x)) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x)) ∧
        ∃ (eN : N ≃* MinusExtraspecial.Model) (f : X ≃* Jβ),
          (∀ n : N, f (n : X) = ((eJ).symm (eN n) : Jβ)) ∧
          (∀ x : X, coreAction (pCore 2 Jβ) eJ (f x) = coreAction N eN x) ∧
          ∃ j : (X ⧸ center X) ≃* (Jβ ⧸ center Jβ),
            (∀ x : X, j (QuotientGroup.mk' (center X) x) =
              QuotientGroup.mk' (center Jβ) (f x)) ∧
            (∀ x : X, (jJ (j (QuotientGroup.mk' (center X) x)) :
              MulAut MinusExtraspecial.Model) = coreAction N eN x) ∧
            ∃ d : (Jβ ⧸ pCore 2 Jβ) ≃* PSL(2,K),
              (∀ x : X, d (QuotientGroup.mk' (pCore 2 Jβ) (f x)) =
                eX (QuotientGroup.mk' N x)) ∧
              ∀ x : L 1, d (QuotientGroup.mk' (pCore 2 Jβ)
                (f (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x))) =
                  e (QuotientGroup.mk' (pCore 2 (L 1)) x) := by
  let X := enlargedEndpoint L S 1
  let N := pCore 2 X
  obtain ⟨hX,hT,hB,eX,heX,a,A,B,C,ha,hac,hd,hBs,hAB,hABs,
    hC,hCcard,haC,eC,eN,heC,hZ,hφ,dK,hdK,hdφ,fS,hfS,z,hz,j,hj,hjn⟩ :=
    original_bTwo_field_four_split_action h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let φ := complementAction N eN C eC
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  let σ := φ.comp eA.symm.toMonoidHom
  let g : MinusExtraspecial.Model ⋊[φ] PSL(2,K) ≃*
      MinusExtraspecial.Model ⋊[σ] alternatingGroup (Fin 5) :=
    SemidirectProduct.congr (MulEquiv.refl _) eA (fun x => MulEquiv.ext fun q => by
      change φ x q = φ (eA.symm (eA x)) q
      rw [eA.symm_apply_apply])
  obtain ⟨fJ,hfJ⟩ :=
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.faithful_split_equiv σ
      (hφ.comp eA.symm.injective)
  let f : X ≃* Jβ := fS.trans (g.trans fJ)
  have hfN (n : N) : f (n : X) = ((eJ).symm (eN n) : Jβ) := by
    have hs : fS (n : X) = SemidirectProduct.inl (eN n) := by
      apply fS.symm.injective
      rw [fS.symm_apply_apply,hfS]
      simp only [SemidirectProduct.left_inl,SemidirectProduct.right_inl,eN.symm_apply_apply,
        map_one,Subgroup.coe_one,mul_one]
    have hg : g (SemidirectProduct.inl (eN n)) = SemidirectProduct.inl (eN n) := by
      apply SemidirectProduct.ext <;> simp [g,SemidirectProduct.congr]
    change fJ (g (fS (n : X))) = _
    rw [hs,hg,hfJ]
  have hfaction (x : X) : coreAction (pCore 2 Jβ) eJ (f x) = coreAction N eN x := by
    apply MulEquiv.ext
    intro v
    obtain ⟨n,rfl⟩ := eN.surjective v
    have hh : MulAut.conjNormal (f x) ((eJ).symm (eN n)) =
        (eJ).symm (eN (MulAut.conjNormal x n)) := by
      apply Subtype.ext
      change f x * ((eJ).symm (eN n) : Jβ) * (f x)⁻¹ = _
      rw [←hfN,←map_inv,←map_mul,←map_mul]
      exact hfN (MulAut.conjNormal x n)
    have he := coreAction_apply (pCore 2 Jβ) eJ (f x) ((eJ).symm (eN n))
    rw [(eJ).apply_symm_apply,hh,(eJ).apply_symm_apply] at he
    rw [he,coreAction_apply]
  have hjf (x : X) : j (QuotientGroup.mk' (center X) x) =
      QuotientGroup.mk' (center Jβ) (f x) := by
    apply (jJ).injective
    apply Subtype.ext
    rw [hj,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv_apply,
      hfaction]
  let fq := QuotientGroup.congr N (pCore 2 Jβ) f (pCore_map_iso 2 f)
  let d := fq.symm.trans eX
  have hdmark (x : X) : d (QuotientGroup.mk' (pCore 2 Jβ) (f x)) =
      eX (QuotientGroup.mk' N x) := by
    change eX (fq.symm (fq (QuotientGroup.mk' N x))) = _
    rw [fq.symm_apply_apply]
  exact ⟨hX,hT,hB,eX,heX,eN,f,hfN,hfaction,j,hjf,hj,d,hdmark,
    fun x => (hdmark _).trans (heX x)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
