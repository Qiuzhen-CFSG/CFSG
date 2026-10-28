module

public import Theory.AlgebraicGroup.CoordinateRing.RationalPointDimension
public import Theory.AlgebraicGroup.CoordinateRing.RegularLocalConormal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# A local Kähler-dimension criterion for smoothness

For a prime `q` of a finite-type algebra `S` over a field `k`, this module
proves that the dimension of the fibre of `Ω[S_q/k]` is bounded below by the
local dimension `height(q) + trdeg_k κ(q)`, with equality forcing smoothness.
The exported theorem is the implication (2) to (1) of Stacks Project, Tag
00TT, in the form needed by the coordinate-ring development.

The proof base-changes to an algebraic closure of `κ(q)` and uses the induced
rational point of `L ⊗[k] S`.  The rational-point height formula turns the
assumed differential bound into regularity of its local ring.  A localized
polynomial presentation, the regular-local conormal injection, and Mathlib's
presentation Jacobian criterion then prove formal smoothness at that point.
Finally, the induced map of local rings is faithfully flat.  Base-change
equivalences for Kähler differentials and cotangent homology descend both
projectivity of `Ω[S_q/k]` and vanishing of `H¹(L_{S_q/k})`, which is precisely
formal smoothness of `S_q` over `k`.
-/

open IsLocalRing Module TensorProduct
open scoped TensorProduct

universe u v

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

private lemma kerCotangentToTensor_injective_of_retraction
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra A k] (r : A →ₐ[k] k) (halgebraMap : algebraMap A k = r)
    (hr : r.comp (Algebra.ofId k A) = AlgHom.id k k) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k A k) := by
  have htower : IsScalarTower k A k :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [halgebraMap]
      simpa using (DFunLike.congr_fun hr x).symm
  letI := htower
  let I := RingHom.ker (algebraMap A k)
  have hdiff (a : A) : a - algebraMap k A (r a) ∈ I := by
    simp [I, halgebraMap]
  letI : IsScalarTower A k I.Cotangent :=
    IsScalarTower.of_algebraMap_smul fun a m ↦ by
      rw [halgebraMap]
      have h := Ideal.Cotangent.smul_eq_zero_of_mem (hdiff a) m
      rw [sub_smul, sub_eq_zero] at h
      calc
        r a • m = algebraMap k A (r a) • m :=
          (IsScalarTower.algebraMap_smul (A := A) (r a) m).symm
        _ = a • m := h.symm
  let d : Derivation k A I.Cotangent :=
    { toFun := fun a ↦ I.toCotangent ⟨a - algebraMap k A (r a), hdiff a⟩
      map_add' := fun a b ↦ by
        apply Ideal.cotangentToQuotientSquare_injective
        simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := fun c a ↦ by
        have hc : algebraMap A k (algebraMap k A c) = c := by
          rw [halgebraMap]
          simpa using r.commutes c
        calc
          I.toCotangent
              ⟨c • a - algebraMap k A (r (c • a)), hdiff (c • a)⟩ =
              algebraMap k A c •
                I.toCotangent ⟨a - algebraMap k A (r a), hdiff a⟩ := by
            rw [← I.toCotangent.map_smul]
            apply I.toCotangent_eq.mpr
            simp only [map_mul, r.commutes, Submodule.coe_smul, Algebra.smul_def,
              Algebra.algebraMap_self_apply]
            ring_nf
            exact zero_mem (I ^ 2)
          _ = algebraMap A k (algebraMap k A c) • I.toCotangent
                ⟨a - algebraMap k A (r a), hdiff a⟩ := by
            exact (IsScalarTower.algebraMap_smul (R := A) (A := k)
              (M := I.Cotangent) (algebraMap k A c) _).symm
          _ = c • I.toCotangent
                ⟨a - algebraMap k A (r a), hdiff a⟩ := by
            rw [hc]
      map_one_eq_zero' := by
        apply Ideal.cotangentToQuotientSquare_injective
        simp
      leibniz' := fun a b ↦ by
        change I.toCotangent
            ⟨a * b - algebraMap k A (r (a * b)), hdiff (a * b)⟩ =
          a • I.toCotangent ⟨b - algebraMap k A (r b), hdiff b⟩ +
            b • I.toCotangent ⟨a - algebraMap k A (r a), hdiff a⟩
        rw [← I.toCotangent.map_smul, ← I.toCotangent.map_smul,
          ← I.toCotangent.map_add]
        apply I.toCotangent_eq.mpr
        rw [pow_two]
        convert neg_mem (Ideal.mul_mem_mul (hdiff a) (hdiff b)) using 1 <;>
          simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, Algebra.smul_def,
            Algebra.algebraMap_self_apply] <;>
          ring }
  let g : k ⊗[A] Ω[A⁄k] →ₗ[k] I.Cotangent :=
    (d.liftKaehlerDifferential).liftBaseChange k
  apply Function.LeftInverse.injective (g := g)
  intro x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  dsimp only [g]
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent,
    LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]
  dsimp only [d]
  apply I.toCotangent_eq.mpr
  have hx : r (x : A) = 0 := by
    have hx' := RingHom.mem_ker.mp x.property
    rw [halgebraMap] at hx'
    exact hx'
  change (x : A) - algebraMap k A (r (x : A)) - (x : A) ∈ I ^ 2
  rw [hx]
  simp

private lemma finrank_cotangentSpace_eq_of_retraction
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] [Algebra A k]
    (r : A →ₐ[k] k) (halgebraMap : algebraMap A k = r)
    (hr : r.comp (Algebra.ofId k A) = AlgHom.id k k) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank k (CotangentSpace A) := by
  have hr_surj : Function.Surjective r := by
    intro x
    refine ⟨algebraMap k A x, ?_⟩
    simpa using DFunLike.congr_fun hr x
  have hker : RingHom.ker r = maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal r.toRingHom hr_surj
  let e : ResidueField A ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hr_surj).toRingEquiv
  have hdiff (a : A) : a - algebraMap k A (r a) ∈ maximalIdeal A := by
    rw [← hker]
    simp [halgebraMap]
  have haction (a : A) (x : CotangentSpace A) :
      r a • x = Ideal.Quotient.mk (maximalIdeal A) a • x := by
    have hzero := Ideal.Cotangent.smul_eq_zero_of_mem (hdiff a) x
    rw [sub_smul, sub_eq_zero] at hzero
    calc
      r a • x = algebraMap k A (r a) • x :=
        (IsScalarTower.algebraMap_smul A (r a) x).symm
      _ = a • x := hzero.symm
      _ = Ideal.Quotient.mk (maximalIdeal A) a • x :=
        (IsScalarTower.algebraMap_smul (A := ResidueField A) a x).symm
  let b := Module.finBasis (ResidueField A) (CotangentSpace A)
  let b' : Basis (Fin (Module.finrank (ResidueField A) (CotangentSpace A))) k
      (CotangentSpace A) := b.mapCoeffs e fun c x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact haction a x
  exact (Module.finrank_eq_card_basis b).trans
    (Module.finrank_eq_card_basis b').symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
public theorem finiteType_isSmoothAt_of_finrank_tensorKaehler_le_height_add_trdeg
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hdimension :
      (Module.finrank (ResidueField (Localization.AtPrime q))
        ((ResidueField (Localization.AtPrime q)) ⊗[Localization.AtPrime q]
          Ω[Localization.AtPrime q⁄k]) : WithBot ℕ∞) ≤
        q.height + Cardinal.toNat
          (Algebra.trdeg k (ResidueField (Localization.AtPrime q)))) :
    Algebra.IsSmoothAt k q := by
  let R := Localization.AtPrime q
  let K := q.ResidueField
  let L := AlgebraicClosure K
  let T := L ⊗[k] S
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : SMul S T := Algebra.TensorProduct.rightAlgebra.toSMul
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  letI : Module S T := Algebra.toModule
  letI : DistribMulAction S T := (inferInstance : Module S T).toDistribMulAction
  letI : IsScalarTower S S T := .of_algebraMap_eq fun s ↦ by simp
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing L T
  let ev : T →ₐ[L] L := rationalPointBaseChangeEval k S q
  letI : Algebra T L := ev.toAlgebra
  letI : IsScalarTower S T L := .of_algebraMap_eq fun (s : S) ↦ by
    rw [show algebraMap T L = ev from rfl]
    symm
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    change rationalPointBaseChangeEval k S q (1 ⊗ₜ[k] s) = algebraMap S L s
    rw [rationalPointBaseChangeEval_tmul]
    rw [one_mul]
    exact (IsScalarTower.algebraMap_apply S K L s).symm
  let m : Ideal T := RingHom.ker ev
  have hev_surj : Function.Surjective ev := by
    intro x
    refine ⟨x ⊗ₜ[k] (1 : S), ?_⟩
    change rationalPointBaseChangeEval k S q (x ⊗ₜ[k] (1 : S)) = x
    rw [rationalPointBaseChangeEval_tmul]
    simp
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev_surj
  let A := Localization.AtPrime m
  let evA : A →ₐ[L] L := IsLocalization.liftAlgHom (M := m.primeCompl) (f := ev)
    fun y ↦ by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.2 (RingHom.mem_ker.mpr hy)
  have hevA_surj : Function.Surjective evA := by
    intro x
    refine ⟨algebraMap T A (x ⊗ₜ[k] (1 : S)), ?_⟩
    rw [show evA (algebraMap T A (x ⊗ₜ[k] (1 : S))) =
        ev (x ⊗ₜ[k] (1 : S)) by simp [evA]]
    change rationalPointBaseChangeEval k S q (x ⊗ₜ[k] (1 : S)) = x
    rw [rationalPointBaseChangeEval_tmul]
    simp
  letI : Algebra A L := evA.toAlgebra
  letI : IsScalarTower T A L := .of_algebraMap_eq fun (x : T) ↦ by
    rw [show algebraMap T L = ev from rfl, show algebraMap A L = evA from rfl]
    symm
    simp [evA]
  letI : Algebra.FormallyEtale T A := .of_isLocalization m.primeCompl
  letI : Algebra.FormallyEtale S R := .of_isLocalization q.primeCompl
  let eA : A ⊗[T] Ω[T⁄L] ≃ₗ[A] Ω[A⁄L] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale L T A
  let eT := KaehlerDifferential.tensorKaehlerEquiv k L S T
  let eR : R ⊗[S] Ω[S⁄k] ≃ₗ[R] Ω[R⁄k] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S R
  let eLeft : L ⊗[A] Ω[A⁄L] ≃ₗ[L] L ⊗[S] Ω[S⁄k] :=
    AlgebraTensorModule.congr (.refl L L) eA.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange T A L L Ω[T⁄L] ≪≫ₗ
      AlgebraTensorModule.congr (.refl L L) eT.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S T L L Ω[S⁄k]
  let eRight : L ⊗[R] Ω[R⁄k] ≃ₗ[L] L ⊗[S] Ω[S⁄k] :=
    AlgebraTensorModule.congr (.refl L L) eR.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S R L L Ω[S⁄k]
  have hfinrankKaehler :
      Module.finrank L (L ⊗[A] Ω[A⁄L]) =
        Module.finrank K (K ⊗[R] Ω[R⁄k]) := by
    calc
      Module.finrank L (L ⊗[A] Ω[A⁄L]) =
          Module.finrank L (L ⊗[S] Ω[S⁄k]) := eLeft.finrank_eq
      _ = Module.finrank L (L ⊗[R] Ω[R⁄k]) := eRight.finrank_eq.symm
      _ = Module.finrank L (L ⊗[K] (K ⊗[R] Ω[R⁄k])) :=
        (AlgebraTensorModule.cancelBaseChange R K L L Ω[R⁄k]).finrank_eq.symm
      _ = Module.finrank K (K ⊗[R] Ω[R⁄k]) := Module.finrank_baseChange
  have hAregular : IsRegularLocalRing A := by
    have hret : evA.comp (Algebra.ofId L A) = AlgHom.id L L := by
      ext
    have hinj : Function.Injective
        (KaehlerDifferential.kerCotangentToTensor L A L) :=
      kerCotangentToTensor_injective_of_retraction L A evA rfl hret
    have hker : RingHom.ker (algebraMap A L) = maximalIdeal A :=
      IsLocalRing.ker_eq_maximalIdeal (algebraMap A L) hevA_surj
    letI : IsScalarTower L A L := .of_algebraMap_eq fun x ↦ (evA.commutes x).symm
    let fCotA : CotangentSpace A →ₗ[A] L ⊗[A] Ω[A⁄L] :=
      (KaehlerDifferential.kerCotangentToTensor L A L).comp
        (Ideal.Cotangent.equivOfEq (maximalIdeal A)
          (RingHom.ker (algebraMap A L)) hker.symm).toLinearMap
    have hinj' : Function.Injective fCotA :=
      hinj.comp (Ideal.Cotangent.equivOfEq (maximalIdeal A)
        (RingHom.ker (algebraMap A L)) hker.symm).injective
    let fCotL : CotangentSpace A →ₗ[L] L ⊗[A] Ω[A⁄L] :=
      { toFun := fCotA
        map_add' := fCotA.map_add
        map_smul' := fun c x ↦ by
          rw [← IsScalarTower.algebraMap_smul A c x, fCotA.map_smul,
            IsScalarTower.algebraMap_smul]
          rfl }
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      finrank_cotangentSpace_eq_of_retraction L A evA rfl hret]
    calc
      (Module.finrank L (CotangentSpace A) : WithBot ℕ∞) ≤
          Module.finrank L (L ⊗[A] Ω[A⁄L]) := by
        exact_mod_cast LinearMap.finrank_le_finrank_of_injective (f := fCotL) hinj'
      _ = Module.finrank K (K ⊗[R] Ω[R⁄k]) := congrArg ((↑) : ℕ → WithBot ℕ∞)
        hfinrankKaehler
      _ ≤ q.height + Cardinal.toNat (Algebra.trdeg k K) := hdimension
      _ = m.height := (rationalPointBaseChangeEval_ker_height_withBot k S q).symm
      _ = ringKrullDim A :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height m A).symm
  have hAformallySmooth : Algebra.FormallySmooth L A := by
    obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType L T)
    let p := m.comap f₀
    let P := Localization.AtPrime p
    let fP : P →ₐ[L] A := IsLocalization.liftAlgHom (M := p.primeCompl)
        (f := (IsScalarTower.toAlgHom L T A).comp f₀) fun x ↦ by
      simpa using IsLocalization.map_units (M := m.primeCompl) A ⟨f₀ x.1, x.2⟩
    have hfP_surj : Function.Surjective fP := by
      intro x
      obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl x
      obtain ⟨x, rfl⟩ := hf₀ x
      obtain ⟨s, rfl⟩ := hf₀ s
      refine ⟨IsLocalization.mk' (M := p.primeCompl) _ x ⟨s, hs⟩, ?_⟩
      simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
    have hkerFG : (RingHom.ker fP).FG := by
      letI : Algebra.FinitePresentation L T :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      have hker₀ := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
      convert! hker₀.map (algebraMap _ P)
      refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
      intro x hx
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
      obtain ⟨a, ha, e⟩ : ∃ a ∈ m.primeCompl, a * f₀ x = 0 := by
        simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff m.primeCompl]
          using hx
      obtain ⟨a, rfl⟩ := hf₀ a
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      exact ⟨a, ha, by simpa⟩
    algebraize [fP.toRingHom]
    letI : IsLocalHom (algebraMap P A) := hfP_surj.isLocalHom
    letI : Algebra.FormallyEtale (MvPolynomial (Fin n) L) P :=
      .of_isLocalization p.primeCompl
    letI : Algebra.FormallySmooth L P :=
      .comp L (MvPolynomial (Fin n) L) P
    letI : Module.Free P Ω[P⁄L] :=
      .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        L (MvPolynomial (Fin n) L) P)
    letI : Module.Finite P Ω[P⁄L] :=
      .of_surjective
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
          L (MvPolynomial (Fin n) L) P).toLinearMap
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
          L (MvPolynomial (Fin n) L) P).surjective
    rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
      (P := P) hfP_surj hkerFG]
    letI : IsRegularLocalRing A := hAregular
    letI : IsRegularLocalRing P := inferInstance
    have hreg := regularLocalConormalToCotangentBaseChange_injective
      (P := P) (R := A) hfP_surj
    have hkerA : RingHom.ker (algebraMap A L) = maximalIdeal A :=
      IsLocalRing.ker_eq_maximalIdeal (algebraMap A L) hevA_surj
    let eResA : ResidueField A ≃ₐ[L] L :=
      (Ideal.quotientEquivAlgOfEq L hkerA.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective hevA_surj)
    letI : Algebra.FormallySmooth L (ResidueField A) :=
      Algebra.FormallySmooth.of_equiv eResA.symm
    have hPRes_surj : Function.Surjective
        (algebraMap P (ResidueField A)) := by
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      obtain ⟨p, rfl⟩ := hfP_surj a
      exact ⟨p, rfl⟩
    have hkerCot_inj : Function.Injective
        (KaehlerDifferential.kerCotangentToTensor L P (ResidueField A)) :=
      (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
        (R := L) (P := P) (A := ResidueField A) hPRes_surj).mpr
        (Algebra.FormallySmooth.subsingleton_h1Cotangent
          (R := L) (A := ResidueField A))
    have hkerPRes : RingHom.ker (algebraMap P (ResidueField A)) =
        maximalIdeal P :=
      IsLocalRing.ker_eq_maximalIdeal (algebraMap P (ResidueField A)) hPRes_surj
    let cPA : CotangentSpace P →ₗ[P]
        (ResidueField A) ⊗[P] Ω[P⁄L] :=
      (KaehlerDifferential.kerCotangentToTensor L P (ResidueField A)).comp
        (Ideal.Cotangent.equivOfEq (maximalIdeal P)
          (RingHom.ker (algebraMap P (ResidueField A))) hkerPRes.symm).toLinearMap
    have hcPA_inj : Function.Injective cPA :=
      hkerCot_inj.comp
        (Ideal.Cotangent.equivOfEq (maximalIdeal P)
          (RingHom.ker (algebraMap P (ResidueField A))) hkerPRes.symm).injective
    have hres_surj : Function.Surjective
        (algebraMap (ResidueField P) (ResidueField A)) := by
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      obtain ⟨p, rfl⟩ := hfP_surj a
      exact ⟨residue P p, rfl⟩
    let cPK : CotangentSpace P →ₗ[ResidueField P]
        (ResidueField A) ⊗[P] Ω[P⁄L] :=
      { cPA with
        map_smul' := by
          intro c x
          obtain ⟨p, rfl⟩ := residue_surjective c
          change cPA ((algebraMap P (ResidueField P) p) • x) =
            (algebraMap (ResidueField P) (ResidueField A) (residue P p)) • cPA x
          rw [IsScalarTower.algebraMap_smul (ResidueField P)]
          rw [show algebraMap (ResidueField P) (ResidueField A) (residue P p) =
            residue A (algebraMap P A p) by simp]
          change cPA (p • x) =
            (algebraMap A (ResidueField A) (algebraMap P A p)) • cPA x
          rw [IsScalarTower.algebraMap_smul (ResidueField A)]
          exact (cPA.map_smul p x).trans
            (IsScalarTower.algebraMap_smul A p (cPA x)).symm }
    let j : (ResidueField A) ⊗[ResidueField P] CotangentSpace P →ₗ[ResidueField A]
        (ResidueField A) ⊗[P] Ω[P⁄L] :=
      cPK.liftBaseChange (ResidueField A)
    have hj_inj : Function.Injective j := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective
        (ResidueField P) (CotangentSpace P) (ResidueField A) hres_surj x
      obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective
        (ResidueField P) (CotangentSpace P) (ResidueField A) hres_surj y
      change (LinearMap.liftBaseChange (ResidueField A) cPK)
          (1 ⊗ₜ[ResidueField P] x) =
        (LinearMap.liftBaseChange (ResidueField A) cPK)
          (1 ⊗ₜ[ResidueField P] y) at hxy
      rw [LinearMap.liftBaseChange_one_tmul,
        LinearMap.liftBaseChange_one_tmul] at hxy
      change cPA x = cPA y at hxy
      rw [hcPA_inj hxy]
    have hfactor :
        KaehlerDifferential.cotangentComplexBaseChange L A P (ResidueField A) =
          j ∘ₗ regularLocalConormalToCotangentBaseChange (P := P) (R := A) := by
      ext a
      simp [j, cPK, cPA,
        KaehlerDifferential.cotangentComplexBaseChange_tmul]
    rw [hfactor]
    exact hj_inj.comp hreg
  have hmunder : m.under S = q := by
    ext s
    change rationalPointBaseChangeEval k S q (1 ⊗ₜ[k] s) = 0 ↔ s ∈ q
    rw [rationalPointBaseChangeEval_tmul, one_mul]
    simp
  letI : m.LiesOver q := ⟨hmunder.symm⟩
  letI : SMul R A :=
    (Localization.AtPrime.algebraOfLiesOver q m).toSMul
  letI : Algebra R A := Localization.AtPrime.algebraOfLiesOver q m
  letI : Module R A := Algebra.toModule
  letI : Localization.AtPrime.IsLiesOverAlgebra q m := inferInstance
  letI : IsScalarTower S R A :=
    Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra (R := S) q m
  letI : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hTflat : Module.Flat S T := by
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight k S L).symm.toLinearEquiv
  have hSTflat : (algebraMap S T).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact hTflat
  letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp
    (RingHom.Flat.localRingHom hSTflat m q hmunder.symm)
  letI : IsLocalHom (algebraMap R A) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom q m (algebraMap S T) hmunder.symm
  letI : Module.FaithfullyFlat R A :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Algebra.FormallySmooth L A := hAformallySmooth
  let eOmegaLeft : Ω[A⁄L] ≃ₗ[A] A ⊗[S] Ω[S⁄k] :=
    eA.symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl A A) eT.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S T A A Ω[S⁄k]
  let eOmegaRight : A ⊗[R] Ω[R⁄k] ≃ₗ[A] A ⊗[S] Ω[S⁄k] :=
    AlgebraTensorModule.congr (.refl A A) eR.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S R A A Ω[S⁄k]
  let eOmega : A ⊗[R] Ω[R⁄k] ≃ₗ[A] Ω[A⁄L] :=
    eOmegaRight ≪≫ₗ eOmegaLeft.symm
  letI : Module.Flat A (A ⊗[R] Ω[R⁄k]) :=
    Module.Flat.of_linearEquiv eOmega
  letI : Module.Flat R Ω[R⁄k] :=
    Module.Flat.of_flat_tensorProduct R Ω[R⁄k] A
  letI : Module.Finite R Ω[R⁄k] := inferInstance
  letI : Module.FinitePresentation R Ω[R⁄k] :=
    Module.finitePresentation_of_finite R Ω[R⁄k]
  have hprojective : Module.Projective R Ω[R⁄k] :=
    Module.Flat.projective_of_finitePresentation
  let eHT : L ⊗[k] Algebra.H1Cotangent k S ≃ₗ[L]
      Algebra.H1Cotangent L T :=
    Algebra.tensorH1CotangentOfFlat k S L
  let ePush : T ⊗[S] Algebra.H1Cotangent k S ≃ₗ[L]
      L ⊗[k] Algebra.H1Cotangent k S :=
    Algebra.IsPushout.cancelBaseChange k L S T (Algebra.H1Cotangent k S)
  let hMap : Algebra.H1Cotangent k S →ₗ[S] Algebra.H1Cotangent L T :=
    Algebra.H1Cotangent.map k L S T
  letI : TensorProduct.CompatibleSMul S S T (Algebra.H1Cotangent k S) :=
    ⟨fun s x y ↦ Quotient.sound' <| AddConGen.Rel.of _ _ <|
      TensorProduct.Eqv.of_smul s x y⟩
  let hBaseMap : T ⊗[S] Algebra.H1Cotangent k S →ₗ[T]
      Algebra.H1Cotangent L T := hMap.liftBaseChange T
  have hBaseMap_eq (x : T ⊗[S] Algebra.H1Cotangent k S) :
      hBaseMap x = eHT (ePush x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul t x =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add t₁ t₂ ht₁ ht₂ => simp [TensorProduct.add_tmul, ht₁, ht₂]
      | tmul l s =>
        have hePush : ePush ((l ⊗ₜ[k] s) ⊗ₜ[S] x) =
            l ⊗ₜ[k] (s • x) := by
          apply ePush.symm.injective
          rw [ePush.symm_apply_apply]
          change (l ⊗ₜ[k] s) ⊗ₜ[S] x =
            (Algebra.IsPushout.cancelBaseChange k L S T
              (Algebra.H1Cotangent k S)).symm (l ⊗ₜ[k] (s • x))
          rw [Algebra.IsPushout.cancelBaseChange_symm_tmul,
            ← TensorProduct.smul_tmul]
          congr 1
          rw [Algebra.smul_def]
          change l ⊗ₜ[k] s = (1 ⊗ₜ[k] s) * (l ⊗ₜ[k] 1)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        change (LinearMap.liftBaseChange T hMap)
            ((l ⊗ₜ[k] s) ⊗ₜ[S] x) = eHT (ePush ((l ⊗ₜ[k] s) ⊗ₜ[S] x))
        rw [LinearMap.liftBaseChange_tmul, hePush]
        rw [show eHT (l ⊗ₜ[k] (s • x)) = l • hMap (s • x) by
          exact Algebra.tensorH1CotangentOfFlat_tmul k S L l (s • x)]
        rw [hMap.map_smul]
        rw [show l ⊗ₜ[k] s = algebraMap L T l * algebraMap S T s by
          change l ⊗ₜ[k] s = (l ⊗ₜ[k] 1) * (1 ⊗ₜ[k] s)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
          mul_smul, IsScalarTower.algebraMap_smul T,
          IsScalarTower.algebraMap_smul T]
  have hBaseMap_bijective : Function.Bijective hBaseMap := by
    constructor
    · intro x y hxy
      apply ePush.injective
      apply eHT.injective
      simpa only [← hBaseMap_eq] using hxy
    · intro y
      obtain ⟨z, rfl⟩ := eHT.surjective y
      obtain ⟨x, rfl⟩ := ePush.surjective z
      exact ⟨x, hBaseMap_eq x⟩
  let eBaseH : T ⊗[S] Algebra.H1Cotangent k S ≃ₗ[T]
      Algebra.H1Cotangent L T :=
    LinearEquiv.ofBijective hBaseMap hBaseMap_bijective
  let eHA : A ⊗[T] Algebra.H1Cotangent L T ≃ₗ[A]
      Algebra.H1Cotangent L A :=
    Algebra.tensorH1CotangentOfIsLocalization L A m.primeCompl
  let eHR : R ⊗[S] Algebra.H1Cotangent k S ≃ₗ[R]
      Algebra.H1Cotangent k R :=
    Algebra.tensorH1CotangentOfIsLocalization k R q.primeCompl
  let eHLeft : Algebra.H1Cotangent L A ≃ₗ[A]
      A ⊗[S] Algebra.H1Cotangent k S :=
    eHA.symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl A A) eBaseH.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S T A A (Algebra.H1Cotangent k S)
  let eHRight : A ⊗[R] Algebra.H1Cotangent k R ≃ₗ[A]
      A ⊗[S] Algebra.H1Cotangent k S :=
    AlgebraTensorModule.congr (.refl A A) eHR.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S R A A (Algebra.H1Cotangent k S)
  let eH : A ⊗[R] Algebra.H1Cotangent k R ≃ₗ[A]
      Algebra.H1Cotangent L A :=
    eHRight ≪≫ₗ eHLeft.symm
  have hAH1 : Subsingleton (A ⊗[R] Algebra.H1Cotangent k R) :=
    eH.toEquiv.subsingleton_congr.mpr
      (Algebra.FormallySmooth.subsingleton_h1Cotangent
        (R := L) (A := A))
  have hH1 : Subsingleton (Algebra.H1Cotangent k R) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R A).mp hAH1
  exact {
    projective_kaehlerDifferential := hprojective
    subsingleton_h1Cotangent := hH1 }

end Theory.AlgebraicGroup
