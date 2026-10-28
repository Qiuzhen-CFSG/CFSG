module

public import Theory.AlgebraicGroup.Jordan.FiniteOrder
public import Theory.AlgebraicGroup.Jordan.LocallyFinite
public import Theory.AlgebraicGroup.Jordan.LocallyFiniteEndomorphism
public import Theory.AlgebraicGroup.Jordan.Translation

universe u

/-!
Semisimplicity and local finiteness of inner automorphisms.  Pullback by
conjugation is the commuting product of left and inverse right translation.
Translation orbit spans give local finiteness, while semisimplicity of a point
gives semisimplicity on every finite invariant submodule.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## Inner automorphisms -/

omit [IsAlgClosed k] in
/-- On a finite-dimensional invariant subspace, two-sided inverse
endomorphisms have the same invariant subspaces. -/
private lemma mem_invtSubmodule_iff_of_inverse
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hTS : T.comp S = 1) (hST : S.comp T = 1)
    (P : Submodule k M) [Module.Finite k P] :
    P ∈ T.invtSubmodule ↔ P ∈ S.invtSubmodule := by
  have forward {A B : Module.End k M} (hBA : B.comp A = 1)
      (hPA : P ∈ A.invtSubmodule) : P ∈ B.invtSubmodule := by
    let AP : Module.End k P := A.restrict hPA
    have hAinj : Function.Injective A := by
      intro x y hxy
      calc
        x = B (A x) := by
          have hx := LinearMap.congr_fun hBA x
          simpa using hx.symm
        _ = B (A y) := congrArg B hxy
        _ = y := by
          have hy := LinearMap.congr_fun hBA y
          simpa using hy
    have hAPinj : Function.Injective AP := by
      intro x y hxy
      apply Subtype.ext
      apply hAinj
      exact congrArg Subtype.val hxy
    have hAPsurj : Function.Surjective AP :=
      LinearMap.surjective_of_injective hAPinj
    intro x hx
    rcases hAPsurj ⟨x, hx⟩ with ⟨y, hy⟩
    have hAy : A y.1 = x := congrArg Subtype.val hy
    have hBx : B x = y.1 := by
      calc
        B x = B (A y.1) := by rw [hAy]
        _ = y.1 := by
          have hy' := LinearMap.congr_fun hBA y.1
          simpa using hy'
    change B x ∈ P
    rw [hBx]
    exact y.2
  exact ⟨forward hST, forward hTS⟩

omit [IsAlgClosed k] in
/-- Finite semisimplicity passes from an invertible endomorphism to its
specified two-sided inverse. -/
private lemma finitelySemisimple_of_inverse
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hT : T.IsFinitelySemisimple)
    (hTS : T.comp S = 1) (hST : S.comp T = 1) :
    S.IsFinitelySemisimple := by
  intro P hPS hPfinite
  let : Module.Finite k P := hPfinite
  have hPT : P ∈ T.invtSubmodule :=
    (mem_invtSubmodule_iff_of_inverse hTS hST P).mpr hPS
  let TP : Module.End k P := T.restrict hPT
  let SP : Module.End k P := S.restrict hPS
  have hTPSP : TP.comp SP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hTS x.1
  have hSPTP : SP.comp TP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hST x.1
  have hinv : ∀ Q : Submodule k P,
      Q ∈ TP.invtSubmodule ↔ Q ∈ SP.invtSubmodule :=
    fun Q => mem_invtSubmodule_iff_of_inverse hTPSP hSPTP Q
  have hTPsem : TP.IsSemisimple := hT P hPT hPfinite
  rw [Module.End.isSemisimple_iff] at hTPsem ⊢
  intro Q hQS
  obtain ⟨R, hRT, hcompl⟩ := hTPsem Q ((hinv Q).mpr hQS)
  exact ⟨R, (hinv R).mp hRT, hcompl⟩

omit [IsAlgClosed k] in
/-- Local finiteness is preserved by conjugation with a linear equivalence. -/
private lemma locallyFinite_conj
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {T : Module.End k M}
    (hT : Module.End.IsLocallyFinite T) (e : M ≃ₗ[k] N) :
    Module.End.IsLocallyFinite (e.conj T) := by
  intro y
  obtain ⟨P, hPfinite, hPT, hy⟩ := hT (e.symm y)
  let Q : Submodule k N := P.map e.toLinearMap
  let : Module.Finite k P := hPfinite
  have hQfinite : Module.Finite k Q := Module.Finite.map P e.toLinearMap
  have hQT : Q ∈ (e.conj T).invtSubmodule := by
    simpa [Q] using (e.map_mem_invtSubmodule_conj_iff.mpr hPT)
  refine ⟨Q, hQfinite, hQT, ?_⟩
  exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

omit [IsAlgClosed k] in
/-- Finite semisimplicity is preserved by conjugation with a linear
equivalence. -/
private lemma finitelySemisimple_conj
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {T : Module.End k M}
    (hT : T.IsFinitelySemisimple) (e : M ≃ₗ[k] N) :
    (e.conj T).IsFinitelySemisimple := by
  intro P hP hPfinite
  let Q : Submodule k M := P.map e.symm.toLinearMap
  let : Module.Finite k P := hPfinite
  have hQfinite : Module.Finite k Q := Module.Finite.map P e.symm.toLinearMap
  let : Module.Finite k Q := hQfinite
  have hQ : Q ∈ T.invtSubmodule := by
    simpa [Q] using
      (e.symm.map_mem_invtSubmodule_iff (f := T) (p := P)).mpr hP
  let eP : P ≃ₗ[k] Q := e.symm.submoduleMap P
  have heP : eP.toLinearMap.comp ((e.conj T).restrict hP) =
      (T.restrict (p := Q) (q := Q) hQ).comp eP.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e.symm ((e.conj T) x.1) = T (e.symm x.1)
    simp [LinearEquiv.conj_apply]
  exact (eP.isSemisimple_iff
    ((e.conj T).restrict hP)
    (T.restrict (p := Q) (q := Q) hQ) heP).mpr
      (hT Q hQ hQfinite)

omit [IsAlgClosed k] in
/-- Pullback along group inversion, regarded as an involutive linear
equivalence of the affine algebra. -/
private noncomputable def inversionPullbackLinearEquiv (G : Variety k) [AlgebraicGroup G] :
    Variety.PolynomialFunction G ≃ₗ[k] Variety.PolynomialFunction G :=
  LinearEquiv.ofInvolutive
    (AlgebraicGroup.invMorphism G).pullbackAlgHom.toLinearMap (by
      intro f
      apply Variety.PolynomialFunction.ext
      intro x
      change f ((x⁻¹)⁻¹) = f x
      simp)

omit [IsAlgClosed k] in
/-- Inversion pullback intertwines right translation by `g⁻¹` with left
translation by `g`. -/
private lemma inversionPullback_intertwines_right_left
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    (inversionPullbackLinearEquiv G).toLinearMap.comp
        (rightTranslationPullback G g⁻¹) =
      (leftTranslationPullback G g).comp
        (inversionPullbackLinearEquiv G).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  change f (x⁻¹ * g⁻¹) = f ((g * x)⁻¹)
  rw [mul_inv_rev]

omit [IsAlgClosed k] in
/-- Consequently left translation by `g` is the linear conjugate of right
translation by `g⁻¹`. -/
private lemma inversion_conj_rightTranslation
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    (inversionPullbackLinearEquiv G).conj
        (rightTranslationPullback G g⁻¹) =
      leftTranslationPullback G g := by
  let e := inversionPullbackLinearEquiv G
  have he := inversionPullback_intertwines_right_left G g
  apply LinearMap.ext
  intro f
  have hf := LinearMap.congr_fun he (e.symm f)
  simpa [e, LinearEquiv.conj_apply] using hf

omit [IsAlgClosed k] in
/-- The pullback of conjugation by `g` is left translation by `g` followed
by right translation by `g⁻¹`. -/
private lemma conjugation_pullback_eq_left_comp_right
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom.toLinearMap =
      (leftTranslationPullback G g).comp
        (rightTranslationPullback G g⁻¹) := by
  apply LinearMap.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  change f (g * x * g⁻¹) = f (g * x * g⁻¹)
  rfl

omit [IsAlgClosed k] in
/-- Pullback by an inner automorphism is locally finite on the coordinate ring. -/
public theorem conjugationPullback_locallyFinite
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    Module.End.IsLocallyFinite
      (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom.toLinearMap := by
  let Rinv : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g⁻¹
  let L : Module.End k (Variety.PolynomialFunction G) :=
    leftTranslationPullback G g
  let e := inversionPullbackLinearEquiv G
  have hRinvloc : Module.End.IsLocallyFinite Rinv := by
    intro f
    simpa [Rinv] using rightTranslationPullback_locallyFinite G g⁻¹ f
  have hconj : e.conj Rinv = L := by
    simpa [e, Rinv, L] using inversion_conj_rightTranslation G g
  have hLloc : Module.End.IsLocallyFinite L := by
    rw [← hconj]
    exact locallyFinite_conj hRinvloc e
  have hcomm : Commute L Rinv := by
    change L.comp Rinv = Rinv.comp L
    simpa [L, Rinv] using
      leftTranslationPullback_comm_rightTranslationPullback G g g⁻¹
  have hprod : Module.End.IsLocallyFinite (L * Rinv) :=
    Module.End.IsLocallyFinite.mul_of_commute hLloc hRinvloc hcomm
  rw [conjugation_pullback_eq_left_comp_right]
  simpa [Rinv, L, Module.End.mul_eq_comp] using hprod

/-- Proposition 1.2.2(c): the inner automorphism induced by a semisimple
element is semisimple on the affine algebra. -/
public theorem conjugationBy_semisimpleElement_isSemisimple {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G) (hg : IsSemisimpleElement G g) :
    IsSemisimpleAutomorphism G (AlgebraicGroup.conjugationByMorphism G g) := by
  let R : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g
  let Rinv : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g⁻¹
  let L : Module.End k (Variety.PolynomialFunction G) :=
    leftTranslationPullback G g
  let e := inversionPullbackLinearEquiv G
  have hcompInv := rightTranslationPullback_comp_inv G g
  have hinvComp := rightTranslationPullback_inv_comp G g
  have hRsem : R.IsFinitelySemisimple := by
    simpa [R, IsSemisimpleElement] using hg
  have hRinvsem : Rinv.IsFinitelySemisimple :=
    finitelySemisimple_of_inverse hRsem
      (by simpa [R, Rinv] using hcompInv)
      (by simpa [R, Rinv] using hinvComp)
  have hRinvloc : Module.End.IsLocallyFinite Rinv := by
    intro f
    simpa [Rinv] using rightTranslationPullback_locallyFinite G g⁻¹ f
  have hconj : e.conj Rinv = L := by
    simpa [e, Rinv, L] using inversion_conj_rightTranslation G g
  have hLsem : L.IsFinitelySemisimple := by
    rw [← hconj]
    exact finitelySemisimple_conj hRinvsem e
  have hLloc : Module.End.IsLocallyFinite L := by
    rw [← hconj]
    exact locallyFinite_conj hRinvloc e
  have hcomm : Commute L Rinv := by
    change L.comp Rinv = Rinv.comp L
    simpa [L, Rinv] using
      leftTranslationPullback_comm_rightTranslationPullback G g g⁻¹
  have hprod : (L * Rinv).IsFinitelySemisimple :=
    Module.End.IsFinitelySemisimple.mul_of_commute
      hLloc hRinvloc hLsem hRinvsem hcomm
  change Module.End.IsFinitelySemisimple
    (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom.toLinearMap
  rw [conjugation_pullback_eq_left_comp_right]
  simpa [Rinv, L, Module.End.mul_eq_comp] using hprod

omit [IsAlgClosed k] in
/-- Proposition 1.2.2(c), finite-order case: the inner automorphism `i_g`
is a semisimple automorphism of `G` whenever `g` has finite order coprime to
the characteristic, since `i_g` then has order dividing the order of `g`
(clause (e) for automorphisms). -/
public theorem conjugationBy_finiteOrderElement_isSemisimple {G : Variety k}
    [AlgebraicGroup G] (g : Variety.Point G) (n : ℕ) (hn : 0 < n)
    (hchar : ¬ ringChar k ∣ n) (hg : g ^ n = 1) :
    IsSemisimpleAutomorphism G (AlgebraicGroup.conjugationByMorphism G g) := by
  let ψ := AlgebraicGroup.conjugationByMorphism G g
  have hψ : (ψ.toFun)^[n] = (_root_.id : Variety.Point G → Variety.Point G) := by
    funext x
    have hgen : ∀ m : ℕ, ∀ z : Variety.Point G, (ψ.toFun^[m]) z = g ^ m * z * (g ^ m)⁻¹ := by
      intro m
      induction m with
      | zero =>
          intro z
          simp [ψ, AlgebraicGroup.conjugationByMorphism]
      | succ m ih =>
          intro z
          rw [Function.iterate_succ_apply]
          rw [AlgebraicGroup.conjugationByMorphism_apply]
          rw [ih]
          calc
            g ^ m * (g * z * g⁻¹) * (g ^ m)⁻¹
                = (g ^ m * g) * z * (g⁻¹ * (g ^ m)⁻¹) := by group
            _ = g ^ (m + 1) * z * (g ^ (m + 1))⁻¹ := by
                rw [pow_succ]
                rw [mul_inv_rev]
    rw [hgen n x, hg]
    simp
  exact finiteOrder_coprimeChar_automorphism_isSemisimple ψ n hn hchar hψ

end Theory.AlgebraicGroup
