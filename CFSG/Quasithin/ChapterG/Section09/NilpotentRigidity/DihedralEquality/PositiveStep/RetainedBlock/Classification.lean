module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock.Action
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock.Rotations
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RankOne

/-!
# The retained plane and the natural orthogonal four-space

The degree bound makes every retained factor cubic. If there is only the
distinguished factor, evaluation identifies the group with S₃ and its moved
space is a plane. Otherwise evaluation at the two retained indices gives
actual product coordinates. Both standard rotations have zero fixed space,
so the orthogonal-pair input supplies a group equivalence with Ω₄⁺(2) and
an intertwining linear equivalence of the actual moved four-space.

Source: Aschbacher--Smith G.9.2, printed p.353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
open DihedralDegree DihedralGroup
universe v

section Coordinates
variable {η : Type} [DecidableEq η] (D : η → Type) [∀ k, Group (D k)]

private def oneCoordinates (a : η) (ha : ∀ k, k = a) : (∀ k, D k) ≃* D a where
  toFun g := g a
  invFun x := Pi.mulSingle a x
  left_inv g := by ext k; obtain rfl := ha k; simp
  right_inv x := by simp
  map_mul' _ _ := rfl

private def twoCoordinates (a b : η) (hab : a ≠ b)
    (hall : ∀ k, k = a ∨ k = b) : (∀ k, D k) ≃* D a × D b where
  toFun g := (g a, g b)
  invFun x := Pi.mulSingle a x.1 * Pi.mulSingle b x.2
  left_inv g := by
    ext k
    rcases hall k with rfl | rfl <;> simp [hab, hab.symm]
  right_inv x := by simp [hab, hab.symm]
  map_mul' _ _ := rfl

end Coordinates

private theorem cast_rotation {m n : ℕ} (h : m = n) :
    (MulEquiv.cast h : DihedralGroup m ≃* DihedralGroup n) (r 1) = r 1 := by
  subst n
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι)
  [FiniteDimensional (ZMod 2) W]

theorem ordinary_retained
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (pair : OrthogonalPairTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    (hp : ∀ j, (p j).Prime) (ho : ∀ j, Odd (p j)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional) :
    IsOrdinaryFactor ((movedRep σ i).comp (subproductHom s.retainedIndices)) ⊤ := by
  let R := s.retainedIndices
  let M := rotationMoved (factorRep σ i)
  let τ := (movedRep σ i).comp (subproductHom R)
  let a : R := ⟨i, Finset.mem_insert_self _ _⟩
  have hfaith := retained_faithful σ i split centralizer (hp i) (ho i) hf s
  have hm := retained_moved_top σ i split centralizer (hp i) (ho i) hf s
  have hc := retained_cubic σ i split bounds centralizer hp ho hf s
  change IsOrdinaryFactor τ ⊤
  unfold IsOrdinaryFactor
  change movedSpace τ ⊤ = ⊤ at hm
  rw [hm]
  rcases s.small with ⟨hJ, hM⟩ | ⟨hJ, hM⟩
  · left
    have hall : ∀ k : R, k = a := by
      intro k
      apply Subtype.ext
      change k.val = i
      have hk := k.property
      simpa [R, PreparedSplit.retainedIndices, Finset.card_eq_zero.mp hJ] using hk
    obtain ⟨e3⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
    refine ⟨⟨Subgroup.topEquiv.trans ((oneCoordinates _ a hall).trans
      ((MulEquiv.cast (hc a)).trans e3))⟩, ?_⟩
    simpa only [finrank_top] using hM
  · right
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hJ
    have hji : j ≠ i := by
      intro he
      exact s.actions.excluded (by simp [hj, he])
    let b : R := ⟨j, Finset.mem_insert_of_mem (by simp [hj])⟩
    have hab : a ≠ b := fun h => hji (congrArg Subtype.val h).symm
    have hall : ∀ k : R, k = a ∨ k = b := by
      intro k
      have hk : k.val = i ∨ k.val = j := by
        simpa only [R, PreparedSplit.retainedIndices, hj, Finset.mem_insert,
          Finset.mem_singleton] using k.property
      exact hk.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h))
    let e : (∀ k : R, DihedralGroup (p k)) ≃* DihedralGroup 3 × DihedralGroup 3 :=
      (twoCoordinates _ a b hab hall).trans
        (MulEquiv.prodCongr (MulEquiv.cast (hc a)) (MulEquiv.cast (hc b)))
    have hea : e (Pi.mulSingle a (r 1)) = (r 1, 1) := by
      change ((MulEquiv.cast (hc a) : DihedralGroup (p a) ≃* DihedralGroup 3)
          (Pi.mulSingle (M := fun k : R => DihedralGroup (p k)) a (r 1) a),
        (MulEquiv.cast (hc b) : DihedralGroup (p b) ≃* DihedralGroup 3)
          (Pi.mulSingle (M := fun k : R => DihedralGroup (p k)) a (r 1) b)) = _
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab.symm, map_one, cast_rotation]
    have heb : e (Pi.mulSingle b (r 1)) = (1, r 1) := by
      change ((MulEquiv.cast (hc a) : DihedralGroup (p a) ≃* DihedralGroup 3)
          (Pi.mulSingle (M := fun k : R => DihedralGroup (p k)) b (r 1) a),
        (MulEquiv.cast (hc b) : DihedralGroup (p b) ≃* DihedralGroup 3)
          (Pi.mulSingle (M := fun k : R => DihedralGroup (p k)) b (r 1) b)) = _
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab, map_one, cast_rotation]
    let ν := τ.comp e.symm.toMonoidHom
    have hfa (w : M) (hw : ν (r 1, 1) w = w) : w = 0 := by
      apply Subtype.ext
      apply distinguished_rotation_fixed_zero σ i split (hp i) (ho i) hf w
      have heq := congrArg Subtype.val hw
      change σ (subproductHom R (e.symm (r 1, 1))) w = (w : W) at heq
      rw [← hea, e.symm_apply_apply, subproductHom_single] at heq
      exact heq
    have hfb (w : M) (hw : ν (1, r 1) w = w) : w = 0 := by
      apply Subtype.ext
      apply second_rotation_fixed_zero σ i split hp ho hf s hM ⟨j, by simp [hj]⟩ w
      have heq := congrArg Subtype.val hw
      change σ (subproductHom R (e.symm (1, r 1))) w = (w : W) at heq
      rw [← heb, e.symm_apply_apply, subproductHom_single] at heq
      exact heq
    obtain ⟨eg, ev, hinter⟩ := pair M ν (hfaith.comp e.symm.injective) hM hfa hfb
    refine ⟨⟨Subgroup.topEquiv.trans (e.trans eg), Submodule.topEquiv.trans ev, ?_⟩, ?_⟩
    · intro g w
      apply ev.injective
      change ev (τ g w) = ev (ev.symm ((eg (e g)).val.val (ev w)))
      rw [ev.apply_symm_apply]
      have hh := hinter (e g) (w : M)
      simpa only [ν, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        e.symm_apply_apply] using hh
    · simpa only [finrank_top] using hM

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
