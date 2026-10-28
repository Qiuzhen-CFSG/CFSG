module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicNormalizer
public import Theory.SpecificGroups.GL2.DiagonalSwap

/-!
# The two marked cubic directions in the original plane complement

The original scalar cubic and a determinant-one diagonal cubic commute.
The coordinate swap inverts the latter and centralizes the former. Their
product fixes a nonzero vector of the original plane. All witnesses are
transported through the supplied complement and natural action markings.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.4.
-/

public noncomputable section
open Subgroup Matrix
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport
open scoped commutatorElement

private abbrev u : Kˣ := cubicUnits (Multiplicative.ofAdd (1 : ZMod 3))
private def b : Fˣ := Units.mk0 (u : K).re (by decide +kernel)
private def z : LinearGroup := GeneralLinearGroup.scalar (Fin 2) b
private def d : LinearGroup := GeneralLinearGroup.diagonalPair F (b, b⁻¹)
private def t : LinearGroup := GeneralLinearGroup.coordinateSwap F
private def v : Plane := Multiplicative.ofAdd ![0, 1]

private theorem cubic_scalar : cubic = scalar u := by
  change SemidirectProduct.inr (complementEquiv (Multiplicative.ofAdd (1 : ZMod 3), 1)) = _
  apply congrArg SemidirectProduct.inr
  apply Subtype.ext
  change multiplication u * dihedralHom 1 = multiplication u
  rw [map_one, mul_one]

private theorem scalar_action (x : Multiplicative K) :
    naturalAction z (rootCoordinates x) =
      rootCoordinates (Multiplicative.ofAdd ((u : K) * x.toAdd)) := by
  rw [naturalAction_apply]
  revert x
  decide +kernel

private theorem action_injective : Function.Injective naturalAction := by
  intro g h he
  apply Representation.SL2FourNatural.SemilinearNormalizer.glEquiv.injective
  apply LinearEquiv.ext
  intro x
  exact congrArg Multiplicative.toAdd
    (congrArg (fun a : MulAut Plane => a (Multiplicative.ofAdd x)) he)

private theorem cubic_coordinates {G : Type*} [Group G]
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) :
    ∃ c : C, ((c : normalizer (A : Set G)) : G) = j cubic ∧ l c = z := by
  obtain ⟨c, hc, hcv⟩ := hj.2.2.2.2.1 u
  let s : C := ⟨c, hc⟩
  have hs : ((s : normalizer (A : Set G)) : G) = j cubic := cubic_scalar ▸ hcv
  refine ⟨s, hs, ?_⟩
  apply action_injective
  apply MulEquiv.ext
  intro w
  obtain ⟨x, rfl⟩ := rootCoordinates.surjective w
  have he : A.normalizerMonoidHom s (a.symm (rootCoordinates x)) =
      a.symm (rootCoordinates (Multiplicative.ofAdd ((u : K) * x.toAdd))) := by
    apply Subtype.ext
    change (s : G) * (a.symm (rootCoordinates x) : G) * (s : G)⁻¹ = _
    rw [hs, cubic_scalar, ← hj.2.2.2.1, ← hj.2.2.2.1]
    simpa only [map_mul, map_inv] using congrArg j (scalar_conjugation u x)
  rw [← a.apply_symm_apply (rootCoordinates x), ← ha, he, a.apply_symm_apply,
    a.apply_symm_apply, scalar_action]

private theorem d_cube : d ^ 3 = 1 := by apply Units.ext; decide +kernel
private theorem d_ne : d ≠ 1 := by intro h; have := congrArg Units.val h; revert this; decide +kernel
private theorem t_square : t ^ 2 = 1 := by apply Units.ext; decide +kernel
private theorem t_ne : t ≠ 1 := by intro h; have := congrArg Units.val h; revert this; decide +kernel
private theorem t_inverts : t * d * t⁻¹ = d⁻¹ := by apply Units.ext; decide +kernel
private theorem d_commutator : ⁅d⁻¹, t⁆ = d := by apply Units.ext; decide +kernel
private theorem d_not_scalar_power (n : ℕ) : z ^ n ≠ d := by
  intro h
  have hp : z ^ n = GeneralLinearGroup.scalar (Fin 2) (b ^ n) :=
    (map_pow (GeneralLinearGroup.scalar (Fin 2)) b n).symm
  rw [hp] at h
  have h0 := congrArg (fun g : LinearGroup => g.val 0 0) h
  have h1 := congrArg (fun g : LinearGroup => g.val 1 1) h
  have he : (b : F) = (b⁻¹ : Fˣ) := h0.symm.trans h1
  exact (by decide +kernel : (b : F) ≠ (b⁻¹ : Fˣ)) he
private theorem fixed_vector : naturalAction (z * d) v = v := by
  rw [naturalAction_apply]
  decide +kernel
private theorem v_square : v ^ 2 = 1 := by decide +kernel
private theorem v_ne : v ≠ 1 := by decide +kernel

set_option maxHeartbeats 800000 in
/-- Original complement cubics and their actual plane fixed point, including
the derived-subgroup and inversion markings needed for nonfusion. -/
theorem field_cubic_nonfusion_witness
    {G : Type*} [Group G]
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) :
    ∃ σ τ : C,
      orderOf σ = 3 ∧ orderOf τ = 2 ∧ τ * σ * τ⁻¹ = σ⁻¹ ∧
      σ ∈ _root_.commutator C ∧
      Commute (j cubic) ((σ : normalizer (A : Set G)) : G) ∧
      Commute (j cubic) ((τ : normalizer (A : Set G)) : G) ∧
      ((σ : normalizer (A : Set G)) : G) ∉ zpowers (j cubic) ∧
      ∃ x : A, orderOf x = 2 ∧
        Commute (j cubic * ((σ : normalizer (A : Set G)) : G)) (x : G) := by
  classical
  obtain ⟨s, hs, hsz⟩ := cubic_coordinates A C l a ha j hj
  let σ := l.symm d
  let τ := l.symm t
  let k : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hk : Function.Injective k := Subtype.val_injective.comp Subtype.val_injective
  have hd : orderOf σ = 3 := (l.symm.orderOf_eq _).trans (orderOf_eq_prime d_cube d_ne)
  have ht : orderOf τ = 2 := (l.symm.orderOf_eq _).trans (orderOf_eq_prime t_square t_ne)
  have hi : τ * σ * τ⁻¹ = σ⁻¹ := by
    apply l.injective
    change l (l.symm t * l.symm d * (l.symm t)⁻¹) = l ((l.symm d)⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv, l.apply_symm_apply, l.apply_symm_apply]
    exact t_inverts
  have hderived : σ ∈ _root_.commutator C := by
    have he : ⁅σ⁻¹, τ⁆ = σ := by
      apply l.injective
      change l ⁅(l.symm d)⁻¹, l.symm t⁆ = l (l.symm d)
      rw [map_commutatorElement, map_inv, l.apply_symm_apply, l.apply_symm_apply]
      exact d_commutator
    rw [← he]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hcentral (c : C) : Commute s c := by
    apply l.injective
    rw [map_mul, map_mul, hsz]
    exact GeneralLinearGroup.scalar_commute b (l c)
  refine ⟨σ, τ, hd, ht, hi, hderived, ?_, ?_, ?_, ?_⟩
  · simpa only [k, MonoidHom.comp_apply, coe_subtype, hs] using (hcentral σ).map k
  · simpa only [k, MonoidHom.comp_apply, coe_subtype, hs] using (hcentral τ).map k
  · intro hσ
    have hsord : orderOf (j cubic) = 3 := (orderOf_injective j hj.1 _).trans cubic_order
    have hfin : IsOfFinOrder (j cubic) := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨3, by decide, by simpa only [hsord] using pow_orderOf_eq_one (j cubic)⟩
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, hsord] at hσ
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hσ
    have heC : s ^ n = σ := hk (by simpa only [map_pow, k, MonoidHom.comp_apply,
      coe_subtype, hs] using he)
    have hem := congrArg l heC
    rw [map_pow, hsz, l.apply_symm_apply] at hem
    exact d_not_scalar_power n hem
  · let x := a.symm v
    refine ⟨x, (a.symm.orderOf_eq _).trans (orderOf_eq_prime v_square v_ne), ?_⟩
    have he : A.normalizerMonoidHom ((s * σ : C) : normalizer (A : Set G)) x = x := by
      apply a.injective
      rw [ha (s * σ) x, map_mul, hsz]
      change naturalAction (z * l (l.symm d)) (a (a.symm v)) = a (a.symm v)
      rw [l.apply_symm_apply, a.apply_symm_apply]
      exact fixed_vector
    have heG := congrArg (fun y : A => (y : G)) he
    change (k s * k σ) * (x : G) * (k s * k σ)⁻¹ = (x : G) at heG
    have hc := mul_inv_eq_iff_eq_mul.mp heG
    change j cubic * ((σ : normalizer (A : Set G)) : G) * (x : G) =
      (x : G) * (j cubic * ((σ : normalizer (A : Set G)) : G))
    simpa only [k, MonoidHom.comp_apply, coe_subtype, hs] using hc

end Sporadic.Janko3.SourceRecognition.PlaneTransport
