module
public import ABG.ChapterII.Section3.UnitaryModelProjectiveCoefficients
public import ABG.ChapterII.Section2.UnitaryOddCoefficientFixedSylow
public import Theory.GroupTheory.CentralKernelSemilinearLift
public import Theory.SpecificGroups.SL2.NoIndexTwo

/-!
# The prescribed unitary matrix model with its odd field action

Let a finite group H split over its normal constituent L with odd complement
E. Suppose L is identified with the actual Hermitian determinant level by an
equivalence preserving the supplied SL2 core through eSU. The prescribed
base-field actor and its injective quadratic lift intertwine through this
same eSU. Then the original projective homomorphism lifts to an injective
map into GammaU2, preserving every L and E coordinate and the exact level
image. No action-agreement hypothesis is used, and q=3 is retained.

Transfer the original projective map to the model. The core equation gives
its canonical value on level zero, so projective coefficient rigidity proves
compatibility on the whole level. An odd coefficient subgroup fixes a Sylow
two-subgroup pointwise. SL2 has no subgroup of index two, hence the central
kernel semilinear lift makes the original and model actions agree. Finally
include the prescribed quadratic actor into the full coefficient group.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27-28.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_unitary_semilinear_embedding_of_core_equiv
    {H : Type*} [Group H] [Finite H]
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (hodd : Odd (Nat.card E))
    (c : E →* (GaloisField p n ≃+* GaloisField p n))
    (cQ : E →* (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hcQ : Function.Injective cQ)
    (φ : L →* PGL2 (GaloisField p n)) (hφtwo : IsPGroup 2 φ.ker)
    (hφcentral : φ.ker.map L.subtype ≤ Subgroup.center H)
    (M : Subgroup L) [M.Normal]
    (e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (hφ0 : ∀ x : M, φ x.val = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection (GaloisField p n) (e0 x)))
    (hindex : (φ.ker ⊔ M).index ∣ 2)
    (m : ℕ) (hdiv : 2 ^ m ∣ p ^ n + 1)
    (eSU : (unitaryForm 2 p n hn).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (hcoeff : ∀ (a : E) (x y : (unitaryForm 2 p n hn).specialSubgroup),
      y.val = coefficientEquiv (cQ a) x.val → eSU y = sl2RingEquiv (c a) (eSU x))
    (eL : L ≃* SU2Level p n hn m)
    (heL : ∀ x : M, (eL x.val).val.val = (eSU.symm (e0 x)).val)
    (f : H →* PGL2 (GaloisField p n) ⋊[(pgl2FieldAut (GaloisField p n)).comp c] E)
    (hfL : ∀ l : L, f l = SemidirectProduct.inl (φ l))
    (hfE : ∀ e : E, f e = SemidirectProduct.inr e) :
    ∃ F : H →* GammaU2 p n hn, Function.Injective F ∧
      (∀ l : L, F l = SemidirectProduct.inl (eL l).val) ∧
      (∀ e : E, F e = SemidirectProduct.inr (cQ e)) ∧
      L.map F = (SU2Level p n hn m).map SemidirectProduct.inl ∧
      E.map F ≤ (SemidirectProduct.inr :
        (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)) →* GammaU2 p n hn).range := by
  classical
  let K := GaloisField p n
  let D := SU2Level p n hn m
  let q := φ.comp eL.symm.toMonoidHom
  have hq0 (a : SU2Level p n hn 0) :
      q ⟨a.val, SU2Level_mono p n hn (Nat.zero_le m) a.property⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (sl2ProjectiveProjection K (eSU (SU2LevelZeroEquivSpecial p n hn a))) := by
    let x : M := e0.symm (eSU (SU2LevelZeroEquivSpecial p n hn a))
    have hex : eL x.val = ⟨a.val, SU2Level_mono p n hn (Nat.zero_le m) a.property⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [heL]
      simp only [x, e0.apply_symm_apply, eSU.symm_apply_apply]
      simpa only [MulEquiv.symm_apply_apply] using
        (SU2LevelZeroEquivSpecial_symm_val p n hn
          (SU2LevelZeroEquivSpecial p n hn a)).symm
    change φ (eL.symm _) = _
    rw [← hex, eL.symm_apply_apply, hφ0]
    simp only [x, e0.apply_symm_apply, K]
  let α := (GU2CoefficientAction p n hn).comp cQ
  let β := (pgl2FieldAut K).comp c
  have hq (a : E) (x y : D) (hxy : y.val = α a x.val) :
      φ (eL.symm y) = β a (φ (eL.symm x)) := by
    apply unitary_model_projection_coefficients p n hp hn m q eSU hq0
      (cQ a) (c a) (hcoeff a) x y
    exact congrArg Subtype.val hxy
  have hA : Odd (Nat.card cQ.range) :=
    (Nat.card_congr (MonoidHom.ofInjective hcQ).toEquiv) ▸ hodd
  obtain ⟨T, hT⟩ := exists_unitary_sylow_fixed_by_odd_coefficient_subgroup
    p n hp hn cQ.range hA m hdiv
  have hno (N : Subgroup M) (_ : N.Normal) : N.index ≠ 2 := by
    have hoddK : Odd (Nat.card K) := by rw [GaloisField.card p n hn]; exact hp.pow
    have h := Matrix.SpecialLinearGroup.index_ne_two
      (two_ne_zero_of_odd_card K hoddK) (N.map e0.toMonoidHom)
    have hi := N.index_map_equiv e0
    exact hi ▸ h
  obtain ⟨F0, hF0, hF0L, hF0E, hF0map, _⟩ :=
    Subgroup.exists_injective_semilinear_model_of_central_kernel D L E hcomp hodd α
      (fun a x => GU2CoefficientAction_mem_SU2Level_iff p n hn m (cQ a) x)
      β eL φ hφtwo hφcentral hq f hfL hfE T
      (fun a t => hT ⟨cQ a, ⟨a, rfl⟩⟩ t) M hno hindex
  let i : GU2 p n hn ⋊[α] E →* GammaU2 p n hn :=
    SemidirectProduct.map (MonoidHom.id _) cQ (fun _ => rfl)
  have hi : Function.Injective i := by
    intro x y h
    apply SemidirectProduct.ext
    · exact congrArg (fun z : GammaU2 p n hn => z.left) h
    · exact hcQ (congrArg (fun z : GammaU2 p n hn => z.right) h)
  refine ⟨i.comp F0, hi.comp hF0, ?_, ?_, ?_, ?_⟩
  · intro l
    change i (F0 l) = _
    rw [hF0L]
    exact SemidirectProduct.map_inl _ _ _ _
  · intro e
    change i (F0 e) = _
    rw [hF0E]
    exact SemidirectProduct.map_inr _ _ _ _
  · rw [← Subgroup.map_map, hF0map, Subgroup.map_map]
    congr 1
    apply DFunLike.ext
    intro x
    exact SemidirectProduct.map_inl (MonoidHom.id _) cQ (fun _ => rfl) x
  · rintro z ⟨e, he, rfl⟩
    refine ⟨cQ ⟨e, he⟩, ?_⟩
    change _ = i (F0 e)
    rw [hF0E ⟨e, he⟩]
    exact (SemidirectProduct.map_inr _ _ _ _).symm

end ABG
