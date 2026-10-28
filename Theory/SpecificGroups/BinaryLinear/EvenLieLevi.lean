module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.LinearAlgebra.Isomorphisms
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
import Mathlib.Tactic

/-!
# Binary two-block Levi complements and the degree-six obstruction

For a binary space U × V, the stabilizer of U × 0 has a split block-action
map onto GL(U) × GL(V). Its kernel is the literal unipotent radical, and
every stabilizer element is a radical element times a diagonal block map.
The explicit projective-to-linear equivalence transports these diagonal
blocks to an L₂(2) × Lₘ(2) subgroup of the actual PSL₂₊ₘ(2) parabolic.
The action formula retains both natural block markings.

An order-three rotation on the first plane contributes rank one; the
already constructed binary linear witness contributes rank two on every
second block of dimension at least four. The nontrivial radical makes the
parabolic two-local. Thus PSLₙ(2) is not quasithin for n ≥ 6.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, A.2.18, printed p.40 (refs/quasithin.pdf).
The imported binary linear rank construction also supplies the lower
bound used in B.4.2/B.5.1. No classification premise is used here.
-/

@[expose] public section

open Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.EvenLieLevi
open SmallParabolicLevi OuterCyclic
variable (U V : Type*) [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

private instance [Finite U] : Finite (BinaryLinear.GL U) :=
  Finite.of_injective (fun g : BinaryLinear.GL U => (g : U → U)) DFunLike.coe_injective

def leftSpace : Submodule (ZMod 2) (U × V) := LinearMap.ker (LinearMap.snd (ZMod 2) U V)

@[simp] theorem mem_leftSpace (x : U × V) : x ∈ leftSpace U V ↔ x.2 = 0 := Iff.rfl

def leftEquiv : leftSpace U V ≃ₗ[ZMod 2] U where
  toFun x := x.val.1
  invFun u := ⟨(u, 0), rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl x.property.symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightEquiv : ((U × V) ⧸ leftSpace U V) ≃ₗ[ZMod 2] V :=
  (LinearMap.snd (ZMod 2) U V).quotKerEquivOfSurjective (fun v => ⟨(0,v), rfl⟩)

@[simp] theorem rightEquiv_mk (x : U × V) :
    rightEquiv U V ((leftSpace U V).mkQ x) = x.2 := rfl

def embedding : BinaryLinear.GL U × BinaryLinear.GL V →* parabolic (leftSpace U V) where
  toFun g := ⟨g.1.prodCongr g.2, by
    intro x
    change g.2 x.2 = 0 ↔ x.2 = 0
    exact g.2.map_eq_zero_iff⟩
  map_one' := by apply Subtype.ext; ext x <;> rfl
  map_mul' _ _ := by apply Subtype.ext; ext x <;> rfl

theorem embedding_injective : Function.Injective (embedding U V) := by
  intro a b h
  have he := congrArg Subtype.val h
  apply Prod.ext
  · ext u
    exact congrArg Prod.fst (LinearEquiv.congr_fun he (u,0))
  · ext v
    exact congrArg Prod.snd (LinearEquiv.congr_fun he (0,v))

noncomputable def projection : parabolic (leftSpace U V) →* BinaryLinear.GL U × BinaryLinear.GL V :=
  ((linearGroupCongr (leftEquiv U V)).prodCongr
    (linearGroupCongr (rightEquiv U V))).toMonoidHom.comp (blockAction (leftSpace U V))

@[simp] theorem projection_embedding (g : BinaryLinear.GL U × BinaryLinear.GL V) :
    projection U V (embedding U V g) = g := by
  apply Prod.ext
  · ext u
    rfl
  · ext v
    change rightEquiv U V (quotientAction (leftSpace U V) (embedding U V g)
      ((rightEquiv U V).symm v)) = g.2 v
    have hv : (rightEquiv U V).symm v = (leftSpace U V).mkQ (0,v) := by
      apply (rightEquiv U V).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hv, quotientAction_mk]
    rfl

theorem ker_projection : (projection U V).ker =
    (radical (leftSpace U V)).subgroupOf (parabolic (leftSpace U V)) := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _)]
  exact ker_blockAction _

/-- The actual radical times the diagonal blocks exhausts the stabilizer. -/
theorem decomposition (g : parabolic (leftSpace U V)) :
    ∃ r : (radical (leftSpace U V)).subgroupOf (parabolic (leftSpace U V)),
      ∃ l : BinaryLinear.GL U × BinaryLinear.GL V, r.val * embedding U V l = g := by
  let l := projection U V g
  refine ⟨⟨g * (embedding U V l)⁻¹, ?_⟩, l, ?_⟩
  · rw [← ker_projection, MonoidHom.mem_ker, map_mul, map_inv, projection_embedding]
    exact mul_inv_cancel _
  · simp

theorem leftSpace_ne_bot [Nontrivial U] : leftSpace U V ≠ ⊥ := by
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  intro h
  have hm : (u, (0 : V)) ∈ leftSpace U V := rfl
  rw [h, Submodule.mem_bot] at hm
  exact hu (congrArg Prod.fst hm)

theorem leftSpace_ne_top [Nontrivial V] : leftSpace U V ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro h
  have hm : ((0 : U), v) ∈ leftSpace U V := h ▸ Submodule.mem_top
  exact hv hm

theorem parabolic_isTwoLocal [Nontrivial U] [Nontrivial V] :
    IsTwoLocal (parabolic (leftSpace U V)) := by
  exact ⟨radical (leftSpace U V), radical_ne_bot (leftSpace_ne_bot U V)
    (leftSpace_ne_top U V), radical_two _, (normalizer_radical (leftSpace_ne_bot U V)).symm⟩

/-- The parabolic is proper, so it is an admissible local subgroup for A.2.15. -/
theorem parabolic_ne_top [Nontrivial U] [Nontrivial V] :
    parabolic (leftSpace U V) ≠ ⊤ :=
  FourParabolicAction.parabolic_ne_top (leftSpace_ne_bot U V) (leftSpace_ne_top U V)

private def cubic (a : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  if a = 0 then 1 else if a = 1 then !![0,1;1,1] else !![1,1;1,0]
private theorem cubic_det : ∀ a, (cubic a).det = 1 := by decide
private theorem cubic_add : ∀ a b, cubic (a+b) = cubic a * cubic b := by decide
private theorem cubic_inj : Function.Injective cubic := by decide
private def cubicHom : Multiplicative (ZMod 3) →* SL(2, ZMod 2) where
  toFun a := ⟨cubic a.toAdd, cubic_det _⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext (cubic_add _ _)

private theorem linearTwo_rank : 1 ≤ primeRank 3 (LinearGroup 2) := by
  rw [← primeRank_equiv 3 (slEquivLinear 2)]
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative (ZMod 3))
    (fun a => congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 a.toAdd))
    (by simp [Nat.card_eq_fintype_card]) cubicHom
  intro a b h
  exact congrArg Multiplicative.ofAdd (cubic_inj (congrArg Subtype.val h))

theorem parabolic_rank {m : ℕ} (hm : 4 ≤ m) :
    3 ≤ primeRank 3 (parabolic (leftSpace (Space 2) (Space m))) := by
  have htwo : 2 ≤ primeRank 3 (LinearGroup m) := by
    rw [← primeRank_equiv 3 (slEquivLinear m)]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hm
  have hprod : 3 ≤ primeRank 3 (LinearGroup 2 × LinearGroup m) := by
    rw [primeRank_prod_eq_add]
    have := linearTwo_rank
    omega
  exact hprod.trans (primeRank_le_of_injective 3 _ (embedding_injective (Space 2) (Space m)))

private theorem not_quasithin_productSpace {m : ℕ} (hm : 4 ≤ m) :
    ¬ IsQuasithin (BinaryLinear.GL (Space 2 × Space m)) := by
  let : NeZero m := ⟨by omega⟩
  intro h
  have := isQuasithin_iff_twoLocal.mp h _ (parabolic_isTwoLocal (Space 2) (Space m))
    3 (by decide) (by decide)
  have := parabolic_rank hm
  omega

noncomputable def splitCoordinates (m : ℕ) : Space (2+m) ≃ₗ[ZMod 2] Space 2 × Space m :=
  (LinearEquiv.piCongrLeft (ZMod 2) (fun _ => ZMod 2) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin m) (ZMod 2) (ZMod 2))

/-- The literal binary projective group in coordinates adapted to the two-space. -/
noncomputable def projectiveCoordinates (m : ℕ) :
    PSL(2+m, ZMod 2) ≃* BinaryLinear.GL (Space 2 × Space m) :=
  (projectiveEquivLinear (by omega)).trans (linearGroupCongr (splitCoordinates m))

/-- The actual two-space stabilizer in the projective matrix carrier. -/
noncomputable def projectiveParabolic (m : ℕ) : Subgroup PSL(2+m, ZMod 2) :=
  (parabolic (leftSpace (Space 2) (Space m))).map (projectiveCoordinates m).symm.toMonoidHom

/-- Transport retains the marked parabolic embedding into the ambient group. -/
noncomputable def parabolicEquiv (m : ℕ) :
    parabolic (leftSpace (Space 2) (Space m)) ≃* projectiveParabolic m :=
  Subgroup.equivMapOfInjective _ _ (projectiveCoordinates m).symm.injective

/-- The promised L₂(2) × Lₘ(2) Levi subgroup, inside the actual parabolic. -/
noncomputable def projectiveLevi (m : ℕ) (hm : 0 < m) :
    PSL(2, ZMod 2) × PSL(m, ZMod 2) →* projectiveParabolic m :=
  (parabolicEquiv m).toMonoidHom.comp ((embedding (Space 2) (Space m)).comp
    ((projectiveEquivLinear (by decide)).prodCongr (projectiveEquivLinear hm)).toMonoidHom)

theorem projectiveLevi_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (projectiveLevi m hm) :=
  (parabolicEquiv m).injective.comp ((embedding_injective _ _).comp
    ((projectiveEquivLinear (by decide)).prodCongr (projectiveEquivLinear hm)).injective)

/-- The two factors act by their usual binary matrices on complementary blocks. -/
theorem projectiveLevi_action (m : ℕ) (hm : 0 < m)
    (g : PSL(2, ZMod 2) × PSL(m, ZMod 2)) (x : Space 2 × Space m) :
    projectiveCoordinates m (projectiveLevi m hm g).val x =
      (projectiveEquivLinear (by decide) g.1 x.1, projectiveEquivLinear hm g.2 x.2) := by
  change projectiveCoordinates m ((projectiveCoordinates m).symm
    (embedding (Space 2) (Space m) _).val) x = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem projectiveParabolic_isTwoLocal {m : ℕ} (hm : 0 < m) :
    IsTwoLocal (projectiveParabolic m) := by
  let : NeZero m := ⟨by omega⟩
  exact isTwoLocal_map (projectiveCoordinates m).symm
    (parabolic_isTwoLocal (Space 2) (Space m))

/-- The marked projective parabolic is proper. -/
theorem projectiveParabolic_ne_top {m : ℕ} (hm : 0 < m) :
    projectiveParabolic m ≠ ⊤ := by
  let : NeZero m := ⟨by omega⟩
  intro h
  have hmap := congrArg (Subgroup.map (projectiveCoordinates m).toMonoidHom) h
  apply parabolic_ne_top (Space 2) (Space m)
  simpa [projectiveParabolic, Subgroup.map_map] using hmap

/-- The literal projective parabolic is the product of its transported
radical and the constructed L₂(2) × Lₘ(2) Levi complement. -/
theorem projectiveLevi_decomposition (m : ℕ) (hm : 0 < m)
    (g : projectiveParabolic m) :
    ∃ r : (radical (leftSpace (Space 2) (Space m))).subgroupOf
        (parabolic (leftSpace (Space 2) (Space m))),
      ∃ l : PSL(2, ZMod 2) × PSL(m, ZMod 2),
        parabolicEquiv m r.val * projectiveLevi m hm l = g := by
  let e := (projectiveEquivLinear (by decide : 0 < 2)).prodCongr
    (projectiveEquivLinear hm)
  obtain ⟨r, l, hl⟩ := decomposition (Space 2) (Space m) ((parabolicEquiv m).symm g)
  refine ⟨r, e.symm l, ?_⟩
  change parabolicEquiv m r.val *
    parabolicEquiv m (embedding (Space 2) (Space m) (e (e.symm l))) = g
  rw [e.apply_symm_apply, ← map_mul, hl, MulEquiv.apply_symm_apply]

theorem projectiveParabolic_rank {m : ℕ} (hm : 4 ≤ m) :
    3 ≤ primeRank 3 (projectiveParabolic m) := by
  rw [← primeRank_equiv 3 (parabolicEquiv m)]
  exact parabolic_rank hm

/-- The L₂(2) × Lₘ(2) obstruction excludes every binary degree at least six. -/
theorem not_quasithin_projective {n : ℕ} (hn : 6 ≤ n) : ¬ IsQuasithin PSL(n, ZMod 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  intro h
  exact not_quasithin_productSpace (by omega : 4 ≤ m)
    (isQuasithin_of_equiv ((projectiveEquivLinear (by omega)).trans
      (linearGroupCongr (splitCoordinates m))) h)
end BinaryLinear.EvenLieLevi
