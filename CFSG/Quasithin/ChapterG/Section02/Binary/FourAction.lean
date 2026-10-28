module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Source
public import Theory.Representation.BinaryPlaneAutomorphisms
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Natural binary coordinates from the actual four-group action

A full action of LT on its elementary four-group, with kernel O₂(LT),
identifies the literal star quotient with S₃. The actual L-image is its
two-residual A₃. Choosing four-group coordinates and conjugating the
full automorphism action constructs compatible natural coordinates;
no independent module-marking assumption remains.

Source: Aschbacher–Smith G.2.3, printed p.333. The original Chapter 14
rank-two source provides the full action and its exact kernel.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

noncomputable def binaryNaturalData_of_four_action
    (h : D.Hypothesis) (hL : D.L ≤ normalizer (D.V : Set G))
    (hc : Nat.card D.V = 4) (hspan : D.V = D.VL)
    (hfull : Function.Surjective (D.V.normalizerMonoidHom.comp
      (inclusion (sup_le hL h.T_normalizes_V))))
    (hker : (D.V.normalizerMonoidHom.comp
      (inclusion (sup_le hL h.T_normalizes_V))).ker = pCore 2 D.LT)
    (hres : (D.V.normalizerMonoidHom.comp (inclusion hL)).range =
      pResidual 2 (MulAut D.V))
    (hpoint : Nat.card D.V₁ = 2) (hne : D.star D.U ≠ ⊥) :
    D.BinaryNaturalData := by
  let := h.elementary
  let : Nontrivial D.V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  let : IsKleinFour D.V := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  let c : D.V ≃* BinaryPlane.Plane := Classical.choice IsKleinFour.nonempty_mulEquiv
  let a : MulAut D.V ≃* Equiv.Perm (Fin 3) :=
    (MulAut.congr c).trans BinaryPlane.equiv.symm
  let f : D.LT →* MulAut D.V := D.V.normalizerMonoidHom.comp
    (inclusion (sup_le hL h.T_normalizes_V))
  have hk : f.ker = pCore 2 D.LT := hker
  let e₀ : D.Star ≃* MulAut D.V :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfull)
  let e := e₀.trans a
  have he (x : D.LT) : e (QuotientGroup.mk' (pCore 2 D.LT) x) = a (f x) := rfl
  have him : (D.star D.L).map e.toMonoidHom = alternatingGroup (Fin 3) := by
    have hr : (D.star D.L).map e₀.toMonoidHom =
        (D.V.normalizerMonoidHom.comp (inclusion hL)).range := by
      ext x
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨QuotientGroup.mk' (pCore 2 D.LT) ⟨y, mem_sup_left y.property⟩,
          ⟨⟨y, mem_sup_left y.property⟩, y.property, rfl⟩, rfl⟩
    change (D.star D.L).map (a.toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map, hr, hres, map_pResidual, Equiv.Perm.twoResidual_eq_alternating]
  let eL : D.star D.L ≃* alternatingGroup (Fin 3) :=
    (e.subgroupMap (D.star D.L)).trans (MulEquiv.subgroupCongr him)
  refine ⟨eL, hspan, c, ?_, hpoint, hne⟩
  intro l v
  have hel : (eL (D.binaryLStar l)).val = a (f ⟨l, mem_sup_left l.property⟩) :=
    he ⟨l, mem_sup_left l.property⟩
  have hx := congrArg (fun k : MulAut BinaryPlane.Plane => k (c v))
    (show BinaryPlane.equiv (eL (D.binaryLStar l)).val =
      MulAut.congr c (f ⟨l, mem_sup_left l.property⟩) by
      rw [hel]
      exact BinaryPlane.equiv.apply_symm_apply _)
  simpa [MulAut.congr_apply, BinaryPlane.equiv, BinaryPlane.action, BinaryPlane.aut, f, Subgroup.inclusion] using
    (congrArg Multiplicative.toAdd hx).symm

end CFSG.Quasithin.ChapterG.Section02.Setup
