module
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPoint
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant

/-!
# Two-cores of nonsingular point stabilizers in the binary determinant module

Conjugation on SL₂(4) × SL₂(4) is faithful for any binary normalizer
subgroup fixing a specified nonzero scalar matrix: its scalar kernel fixes
that matrix only when it is trivial. The point fixer preserves the inner
diagonal, so its component action centralizes the factor swap. The diagonal
core theorem bounds its two-core by that swap. Scaling a nonsingular matrix
and translating by the actual inner action gives the same order-two bound
at every nonsingular point and in every intermediate point fixer containing
the full inner stabilizer.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The literal section and reciprocal-plane applications are
in `NonsingularSectionCore` and `LocalReduction.BinaryPlaneCore`.
-/

@[expose] public noncomputable section
open Matrix Subgroup Theory.GroupTheory
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
namespace PointCore
abbrev SL := SpecialLinearGroup (Fin 2) F
abbrev BinaryAut := V ≃ₗ[ZMod 2] V

private instance sl_quasisimple : IsQuasisimple SL := by
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 5))
  let : IsSimpleGroup SL := QuotientLocal.factorAlternatingEquiv.isSimpleGroup
  let := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    decide)
  let : Group.IsPerfect SL := Group.IsPerfect.ofSurjective
    (f := Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.toMonoidHom)
    Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.surjective
  exact { simple := Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.isSimpleGroup }

private theorem action_inj : Function.Injective linearAction :=
  fun _ _ he => action_injective (congrArg LinearEquiv.toLinearMap he)

private def squareAction : normalizer (linearAction.range : Set BinaryAut) →* MulAut G :=
  (MulAut.congr (MonoidHom.ofInjective action_inj).symm).toMonoidHom.comp
    linearAction.range.normalizerMonoidHom

private theorem squareAction_spec (t : normalizer (linearAction.range : Set BinaryAut)) (g : G) :
    linearAction (squareAction t g) = t.val * linearAction g * t.val⁻¹ := by
  change ((MonoidHom.ofInjective action_inj)
    ((MonoidHom.ofInjective action_inj).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem squareAction_inner (g : G) :
    squareAction ⟨linearAction g, linearAction.range.le_normalizer ⟨g,rfl⟩⟩ = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply action_inj
  rw [squareAction_spec]
  symm
  change linearAction (g*x*g⁻¹) = _
  exact (map_mul linearAction (g*x) g⁻¹).trans
    (congrArg₂ (· * ·) (map_mul linearAction g x) (map_inv linearAction g))

private theorem diagonal_preserving_mem_swapCentralizer
    (a : MulAut G) (ha : ∀ x : SL, (a (x,x)).1 = (a (x,x)).2) :
    a ∈ QuotientLocal.SwapCentralizer SL := by
  rcases AutomorphismSquare.normal_form Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot a with
    ⟨b,c,he⟩ | ⟨b,c,he⟩
  all_goals
    have hbc : b = c := by
      apply MulEquiv.ext
      intro x
      have hh := ha x
      rw [he] at hh
      exact hh
    subst c
    apply mem_centralizer_singleton_iff.mpr
    rw [he]
    ext x <;> rfl

/-- The prime core of a point fixer containing the inner diagonal has order at most two. -/
theorem scalar_point_core_card
    (A : Subgroup BinaryAut) (hA : A ≤ normalizer (linearAction.range : Set BinaryAut))
    (c : F) (hc : c ≠ 0)
    (hfix : ∀ a ∈ A, a (c • (1 : V)) = c • (1 : V))
    (hdiag : ∀ x : SL, linearAction (x,x) ∈ A) :
    Nat.card (A.pCoreIn 2) ≤ 2 := by
  let f : A →* MulAut G := squareAction.comp (inclusion hA)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro a ha
    have hcomm (g : G) : a.val * linearAction g = linearAction g * a.val := by
      have hh := squareAction_spec (inclusion hA a) g
      have he : squareAction (inclusion hA a) = 1 := ha
      rw [he] at hh
      change linearAction g = a.val * linearAction g * a.val⁻¹ at hh
      exact (eq_mul_inv_iff_mul_eq.mp hh).symm
    obtain ⟨d,hd⟩ := centralizer_scalar a.val.toLinearMap.toAddMonoidHom
      (fun g M => LinearEquiv.congr_fun (hcomm g) M)
    change ∀ M, a.val M = d • M at hd
    have hd1 : d = 1 := by
      have hh := hfix a a.property
      rw [hd] at hh
      have hh' := congrArg (fun M : V => M 0 0) hh
      have hh' : d*c = c := by simpa only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,if_true,mul_one] using hh'
      exact (mul_right_cancel₀ hc (hh'.trans (one_mul c).symm))
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    simpa [hd1] using hd M
  have hswap : f.range ≤ QuotientLocal.SwapCentralizer SL := by
    rintro _ ⟨a,rfl⟩
    apply diagonal_preserving_mem_swapCentralizer
    intro x
    have hh := squareAction_spec (inclusion hA a) (x,x)
    have hfx := hfix a a.property
    have hinv : a.val.symm (c • (1 : V)) = c • (1 : V) := by
      exact a.val.injective (by rw [a.val.apply_symm_apply,hfx])
    have hdiagfix : linearAction (x,x) (c • (1 : V)) = c • (1 : V) := by
      change matrixAction (x,x) (c • (1 : V)) = _
      rw [LinearEquiv.map_smul]
      apply congrArg (fun M : V => c • M)
      change x.val * 1 * x⁻¹.val = 1
      rw [mul_one]
      exact congrArg Subtype.val (mul_inv_cancel x)
    have hfix' : linearAction (f a (x,x)) (c • (1 : V)) = c • (1 : V) := by
      change linearAction (squareAction (inclusion hA a) (x,x)) _ = _
      rw [hh]
      change a.val (linearAction (x,x) (a.val.symm _)) = _
      rw [hinv,hdiagfix,hfx]
    have hp : (f a) (x,x) ∈ pointStabilizer (1 : V) := by
      apply (mem_pointStabilizer _ _).mpr
      apply (smul_right_inj (M := V) hc).mp
      change matrixAction (f a (x,x)) (c • (1 : V)) = c • (1 : V) at hfix'
      exact ((matrixAction (f a (x,x))).map_smul c (1 : V)).symm.trans hfix'
    have he := (mem_pointStabilizer_iff _ _).mp hp
    apply Subtype.ext
    simpa only [mul_one,one_mul] using he
  have hinner : QuotientLocal.diagonalInner.range ≤ f.range := by
    rintro _ ⟨x,rfl⟩
    refine ⟨⟨linearAction (x,x),hdiag x⟩,?_⟩
    exact squareAction_inner (x,x)
  have hb := QuotientLocal.sandwich_core_le_swap 2
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot
    Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot f.range hswap hinner
  have hm : (pCore 2 A).map f = f.range.pCoreIn 2 := by
    have hh := pCore_map_iso 2 (MonoidHom.ofInjective hf)
    have hmap := congrArg (Subgroup.map f.range.subtype) hh
    rw [Subgroup.map_map] at hmap
    exact hmap
  have hc0 : Nat.card (pCore 2 A) = Nat.card (f.range.pCoreIn 2) := by
    rw [←hm,card_map_of_injective hf]
  have hc1 : Nat.card (zpowers (QuotientLocal.swap (S := SL))) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one (by ext x <;> rfl :
      (QuotientLocal.swap (S := SL)) ^ 2 = 1))
  rw [pCoreIn,card_map_of_injective A.subtype_injective,hc0]
  exact (card_le_of_le hb).trans hc1
private theorem point_core_of_scalar_conjugate
    (A : Subgroup BinaryAut) (hA : A ≤ normalizer (linearAction.range : Set BinaryAut))
    (v : V) (hfix : ∀ a ∈ A, a v = v)
    (hinner : (pointStabilizer v).map linearAction ≤ A)
    (g : G) (c : F) (hc0 : c ≠ 0) (hrv : linearAction g v = c • (1 : V)) :
    Nat.card (A.pCoreIn 2) ≤ 2 := by
  let r := linearAction g
  have hrn : r ∈ normalizer (linearAction.range : Set BinaryAut) :=
    linearAction.range.le_normalizer ⟨g,rfl⟩
  let f : BinaryAut →* BinaryAut := (MulAut.conj r).toMonoidHom
  let B := A.map f
  have hB : B ≤ normalizer (linearAction.range : Set BinaryAut) := by
    rintro _ ⟨b,hb,rfl⟩
    exact (normalizer _).mul_mem ((normalizer _).mul_mem hrn (hA hb))
      ((normalizer _).inv_mem hrn)
  have hBfix : ∀ b ∈ B, b (c • (1 : V)) = c • (1 : V) := by
    rintro _ ⟨b,hb,rfl⟩
    change r (b (r.symm (c • (1 : V)))) = c • (1 : V)
    rw [←hrv,r.symm_apply_apply,hfix b hb,hrv]
  have hBdiag : ∀ x : SL, linearAction (x,x) ∈ B := by
    intro x
    let y := g⁻¹ * (x,x) * g
    have hy : y ∈ pointStabilizer v := by
      apply (mem_pointStabilizer _ _).mpr
      change linearAction y v = v
      have he : linearAction y = r⁻¹ * linearAction (x,x) * r := by
        simp only [y,map_mul,map_inv,r]
      rw [he]
      change r.symm (linearAction (x,x) (r v)) = v
      rw [hrv]
      have hx : linearAction (x,x) (c • (1 : V)) = c • (1 : V) := by
        change matrixAction (x,x) (c • (1 : V)) = _
        rw [LinearEquiv.map_smul]
        apply congrArg (fun M : V => c • M)
        change x.val * 1 * x⁻¹.val = 1
        rw [mul_one]
        exact congrArg Subtype.val (mul_inv_cancel x)
      rw [hx]
      exact r.injective (by rw [r.apply_symm_apply,hrv])
    refine ⟨linearAction y,hinner (mem_map_of_mem _ hy),?_⟩
    change r * linearAction y * r⁻¹ = linearAction (x,x)
    simp only [y,map_mul,map_inv,r]
    group
  have hb := scalar_point_core_card B hB c hc0 hBfix hBdiag
  have he := map_pCoreIn_of_injective 2 A f (MulAut.conj r).injective
  rw [←he,card_map_of_injective (MulAut.conj r).injective] at hb
  exact hb

/-- The two-core bound holds at every nonsingular point and in every
intermediate group containing its full inner stabilizer. -/
theorem nonsingular_point_core_card
    (A : Subgroup BinaryAut) (hA : A ≤ normalizer (linearAction.range : Set BinaryAut))
    (v : V) (hv : v.det ≠ 0)
    (hfix : ∀ a ∈ A, a v = v)
    (hinner : (pointStabilizer v).map linearAction ≤ A) :
    Nat.card (A.pCoreIn 2) ≤ 2 := by
  obtain ⟨c,hc⟩ := Finite.surjective_of_injective
    (CharTwo.sq_injective : Function.Injective (fun c : F => c^2)) v.det
  change c^2 = v.det at hc
  have hc0 : c ≠ 0 := by intro hz; apply hv; rw [←hc,hz]; simp
  let a : SL := ⟨c⁻¹ • v,by
    rw [Matrix.det_smul]
    change c⁻¹ ^ 2 * v.det = 1
    rw [←hc,←mul_pow,inv_mul_cancel₀ hc0,one_pow]⟩
  let g : G := (a⁻¹,1)
  let r := linearAction g
  have hvform : v = c • a.val := by simp [a,hc0]
  have hrv : r v = c • (1 : V) := by
    rw [hvform]
    change matrixAction g (c • a.val) = _
    rw [LinearEquiv.map_smul]
    apply congrArg (fun M : V => c • M)
    change a⁻¹.val * a.val * (1 : SL)⁻¹.val = 1
    rw [inv_one]
    change a⁻¹.val * a.val * (1 : V) = 1
    rw [mul_one]
    exact congrArg (fun x : SL => x.val) (inv_mul_cancel a)
  exact point_core_of_scalar_conjugate A hA v hfix hinner g c hc0 hrv

end PointCore
end ClassicalOrthogonal.FourPlusMatrix.Binary
