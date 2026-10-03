module
public import GorensteinWalter.DeterminantLevelPGLProjection
public import Theory.SpecificGroups.GL2.OddCoefficientFixedSylow
public import Theory.SpecificGroups.SL2.NoIndexTwo
public import Theory.GroupTheory.CentralKernelSemilinearLift

/-!
# The actual linear semilinear embedding

Let a finite group H have a normal constituent L and an odd complement E.
Suppose L is identified with an actual determinant two-power level over
an odd finite field, preserving a prescribed normal SL2 core. A projective
map of H records the actual coefficient action of E, with central two-kernel
on L and kernel/core join of index dividing two. Then the supplied linear
identification extends to an injective homomorphism into GammaL2. The map
preserves every linear and coefficient coordinate and the exact image of L.
The group and field may inhabit different universes; order three is included.

Transport the projective map through the linear equivalence. Its equation
on the prescribed core implies the canonical level-zero equation, so the
normal PSL2 rigidity theorem identifies its coefficient action. An odd
coefficient subgroup fixes a Sylow two-subgroup of the determinant level.
SL2 has no subgroup of index two, and the central-kernel semilinear lifting
theorem now extends the equivalence. Finally embed the supplied faithful
coefficient group into the full field automorphism group coordinatewise.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27–28.
This is the actual linear field-action lift after constituent recognition;
no separate matrix action agreement is assumed.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_linear_semilinear_embedding_of_core_equiv
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (hodd : Odd (Nat.card E))
    (c : E →* (F ≃+* F)) (hc : Function.Injective c)
    (φ : L →* PGL2 F) (hφtwo : IsPGroup 2 φ.ker)
    (hφcentral : φ.ker.map L.subtype ≤ Subgroup.center H)
    (M : Subgroup L) [M.Normal]
    (e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hφ0 : ∀ x : M, φ x.val = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection F (e0 x)))
    (hindex : (φ.ker ⊔ M).index ∣ 2)
    (m : ℕ) (hm : 2 ^ m ∣ Nat.card F - 1)
    (eL : L ≃* determinantTwoPower F m)
    (heL : ∀ x : M, (eL x.val).val = Matrix.SpecialLinearGroup.toGL (e0 x))
    (f : H →* PGL2 F ⋊[(pgl2FieldAut F).comp c] E)
    (hfL : ∀ l : L, f l = SemidirectProduct.inl (φ l))
    (hfE : ∀ e : E, f e = SemidirectProduct.inr e) :
    ∃ F' : H →* GammaL2 F, Function.Injective F' ∧
      (∀ l : L, F' l = SemidirectProduct.inl (eL l).val) ∧
      (∀ e : E, F' e = SemidirectProduct.inr (c e)) ∧
      L.map F' = (determinantTwoPower F m).map SemidirectProduct.inl ∧
      E.map F' ≤ (SemidirectProduct.inr : (F ≃+* F) →* GammaL2 F).range := by
  classical
  let D := determinantTwoPower F m
  let α : E →* MulAut (GL (Fin 2) F) := (coefficientAction F).comp c
  let β : E →* MulAut (PGL2 F) := (pgl2FieldAut F).comp c
  let q : D →* PGL2 F := φ.comp eL.symm.toMonoidHom
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hp, _, he⟩ := hF
    rw [he]
    exact hp.pow
  have hq0 (x : determinantTwoPower F 0) :
      q ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (sl2ProjectiveProjection F (determinantTwoPowerZeroEquivSL F x)) := by
    let a := e0.symm (determinantTwoPowerZeroEquivSL F x)
    have ha : eL a.val = ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ := by
      apply Subtype.ext
      rw [heL a, show e0 a = determinantTwoPowerZeroEquivSL F x from e0.apply_symm_apply _]
      exact determinantTwoPowerZeroEquivSL_toGL F x
    change φ (eL.symm _) = _
    rw [← ha, eL.symm_apply_apply, hφ0 a]
    congr 2
    exact e0.apply_symm_apply _
  have hq (a : E) (x y : D) (hxy : y.val = α a x.val) :
      φ (eL.symm y) = β a (φ (eL.symm x)) := by
    exact determinantTwoPower_pgl_hom_coefficient F hF m q hq0 (c a) x y hxy
  have hAc : Odd (Nat.card c.range) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hc).toEquiv]
    exact hodd
  obtain ⟨T, hT⟩ := exists_sylow_fixed_by_odd_coefficient_subgroup F hFodd c.range hAc m hm
  have hT' (a : E) (t : T) : α a t.val.val = t.val.val :=
    hT ⟨c a, ⟨a, rfl⟩⟩ t
  have hno : ∀ N : Subgroup M, N.Normal → N.index ≠ 2 := by
    intro N _
    have hh := Matrix.SpecialLinearGroup.index_ne_two
      (two_ne_zero_of_odd_card F hFodd) (N.map e0.toMonoidHom)
    exact fun hi => hh ((N.index_map_equiv e0).trans hi)
  obtain ⟨g, hg, hgL, hgE, hgLi, hgEi⟩ :=
    Subgroup.exists_injective_semilinear_model_of_central_kernel D L E hcomp hodd α
      (fun a x => coefficientAction_mem_determinantTwoPower_iff F m (c a) x)
      β eL φ hφtwo hφcentral hq f hfL hfE T hT' M hno hindex
  let j : GL (Fin 2) F ⋊[α] E →* GammaL2 F :=
    SemidirectProduct.map (MonoidHom.id _) c (fun _ => rfl)
  have hj : Function.Injective j := by
    intro x y h
    apply SemidirectProduct.ext
    · exact congrArg (fun z : GammaL2 F => z.left) h
    · exact hc (congrArg (fun z : GammaL2 F => z.right) h)
  have hjL (x : GL (Fin 2) F) : j (SemidirectProduct.inl x) = SemidirectProduct.inl x := by
    exact SemidirectProduct.map_inl _ _ _ x
  have hjE (a : E) : j (SemidirectProduct.inr a) = SemidirectProduct.inr (c a) := by
    exact SemidirectProduct.map_inr _ _ _ a
  refine ⟨j.comp g, hj.comp hg, ?_, ?_, ?_, ?_⟩
  · intro l
    change j (g l) = _
    rw [hgL l, hjL]
  · intro a
    change j (g a) = _
    rw [hgE a, hjE]
  · rw [← Subgroup.map_map, hgLi, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hjL
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨c ⟨a, ha⟩, ((hjE ⟨a, ha⟩).symm.trans
      (congrArg j (hgE ⟨a, ha⟩).symm))⟩

end ABG
