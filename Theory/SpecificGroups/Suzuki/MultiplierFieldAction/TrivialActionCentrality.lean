module

public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.FixedLifts
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.RootQuotient
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas

/-!
# Centrality under trivial Suzuki multiplier field action

If the canonical lifted Frobenius fixes the covering kernel of order four,
the full preimage of the Sz(8) root center is central in the lifted root group.
The kernel, root preimage, field lift and projections are the literal maps
of `LocalCover`, `FixedLifts` and `RootQuotient`.

Entrywise squaring identifies the fixed root group with the four powers of
u(1,0). For a lift x of that generator, every conjugate of x² is field-fixed,
since its image is the fixed central element u(0,1). Thus field commutators
centralize x²; fixed elements also centralize it, because their images are
powers of u(1,0) and the covering kernel is central. Coprime generation gives
x² in the lifted root center. The actual torus conjugation formula transports
this to every nonidentity root-center image; the central kernel completes
the full inverse-image assertion.

Source: GLS3, section 6.3, Sz(8) case, printed p.337,
`refs/KGroup/GLS3/chapter6.tex`, lines 311–317; supporting Aschbacher–Smith
I.2.2(7a), printed p.412 of `refs/quasithin.pdf`. The hypothesis of trivial
kernel action remains explicit; the final multiplier contradiction is separate.
-/

open Subgroup BenderSuzuki.PFAppendixIII
noncomputable section
namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction.TrivialActionCentrality
abbrev F := BinaryGaloisField 3

def rootPoint (a b : F) : SuzukiRootSubgroup 1 :=
  ⟨⟨SuzukiRootGL 1 a b, suzukiRootClosure_le 1 (subset_closure ⟨a, b, rfl⟩)⟩,
    subset_closure ⟨a, b, rfl⟩⟩

theorem rootPoint_mul (a b c d : F) :
    rootPoint a b * rootPoint c d = rootPoint (a + c) (b + d + a * suzukiTits 1 c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 1 (by decide) (suzukiTits 1)
    (suzukiTits_sq 1)).2.2.2.2.2.2.2.2.1 a b c d

theorem rootPoint_sq (a b : F) :
    rootPoint a b ^ 2 = rootPoint 0 (a * suzukiTits 1 a) := by
  simp only [pow_two, rootPoint_mul, CharTwo.add_self_eq_zero, zero_add]

theorem rootPoint_zero : rootPoint 0 0 = 1 :=
  Subtype.ext (Subtype.ext (External.suzukiRootGL_zero_zero 1))

theorem rootPoint_surjective (x : SuzukiRootSubgroup 1) :
    ∃ a b, x = rootPoint a b := by
  obtain ⟨a, b, h⟩ := (mem_suzukiRootSubgroup_iff 1 x.val).mp x.property
  exact ⟨a, b, Subtype.ext (Subtype.ext h)⟩

theorem field_rootPoint (a b : F) :
    suzukiFieldAutomorphism 1 (rootPoint a b).val = (rootPoint (a ^ 2) (b ^ 2)).val := by
  apply Subtype.ext
  exact map_suzukiRootGL (d := 1) (n := 1) (dvd_refl _)
    (frobenius F 2) a b

theorem rootPoint_one_sq : rootPoint 1 0 ^ 2 = rootPoint 0 1 := by
  simp only [rootPoint_sq, map_one, mul_one]

theorem rootPoint_one_cube : rootPoint 1 0 ^ 3 = rootPoint 1 1 := by
  rw [pow_succ _ 2, rootPoint_one_sq, rootPoint_mul]
  simp

theorem fixed_root_iff (x : SuzukiRootSubgroup 1) :
    suzukiFieldAutomorphism 1 x.val = x.val ↔ ∃ n : ℕ, x = rootPoint 1 0 ^ n := by
  constructor
  · obtain ⟨a,b,rfl⟩ := rootPoint_surjective x
    intro h
    have ha : a ^ 2 = a := by
      have hh := congrArg (fun y : SuzukiMatrixGroup 1 => y.val (0 : Fin 4) (1 : Fin 4)) h
      rw [suzukiFieldAutomorphism_entry] at hh
      exact hh
    have hb : b ^ 2 = b := by
      have hh := congrArg (fun y : SuzukiMatrixGroup 1 => y.val (0 : Fin 4) (2 : Fin 4)) h
      rw [suzukiFieldAutomorphism_entry] at hh
      exact hh
    rcases eq_zero_or_one_of_sq_eq_self ha with rfl | rfl <;>
      rcases eq_zero_or_one_of_sq_eq_self hb with rfl | rfl
    · exact ⟨0, rootPoint_zero⟩
    · exact ⟨2, rootPoint_one_sq.symm⟩
    · exact ⟨1, (pow_one _).symm⟩
    · exact ⟨3, rootPoint_one_cube.symm⟩
  · rintro ⟨n,rfl⟩
    change suzukiFieldAutomorphism 1 ((rootPoint 1 0).val ^ n) = (rootPoint 1 0).val ^ n
    rw [map_pow, field_rootPoint]
    simp

def torusPoint (t : Fˣ) : SuzukiMatrixGroup 1 :=
  ⟨SuzukiTorusGL 1 t, suzukiSplitTorusClosure_le 1 (subset_closure ⟨t,rfl⟩)⟩

theorem torusPoint_mem (t : Fˣ) : torusPoint t ∈ SuzukiSplitTorus 1 :=
  subset_closure ⟨t,rfl⟩

theorem torusPoint_conj (t : Fˣ) (a b : F) :
    torusPoint t * (rootPoint a b).val * (torusPoint t)⁻¹ =
      (rootPoint ((t : F) * a) ((t : F) * suzukiTits 1 t * b)).val := by
  apply Subtype.ext
  exact External.suzukiTorusGL_conj_root 1 (suzukiTits 1) (suzukiTits_sq 1)
    (suzukiTits_apply 1) a b t

theorem center_torus_orbit (z : SuzukiRootSubgroup 1) (hz : z ∈ center _) :
    z = 1 ∨ ∃ t : Fˣ,
      z.val = torusPoint t * (rootPoint 0 1).val * (torusPoint t)⁻¹ := by
  obtain ⟨x,hx⟩ := suzukiRootSubgroup_square_surjective 1 (by decide) ⟨z,hz⟩
  obtain ⟨a,b,rfl⟩ := rootPoint_surjective x
  rw [rootPoint_sq] at hx
  by_cases ha : a = 0
  · left
    simpa only [ha, zero_mul, rootPoint_zero] using hx.symm
  · right
    refine ⟨Units.mk0 a ha, ?_⟩
    simp only [torusPoint_conj, mul_zero, mul_one, Units.val_mk0]
    exact congrArg Subtype.val hx.symm
end BenderSuzuki.MatrixGroups.MultiplierFieldAction.TrivialActionCentrality

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction.TrivialActionCentrality
open Subgroup

/-- Coprime generation reduces centrality to fixed conjugates and the fixed subgroup. -/
private lemma central_of_coprime_fixed_conjugates {G : Type*} [Group G] [Finite G]
    (a : MulAut G) (hsolv : Group.IsSolvable G)
    (hcop : Nat.Coprime (orderOf a) (Nat.card G)) (z : G)
    (hconj : ∀ g : G, a (g * z * g⁻¹) = g * z * g⁻¹)
    (hfixed : ∀ g : G, a g = g → Commute g z) : z ∈ center G := by
  let A := zpowers a
  have hfix (b : A) (g : G) : b • (g * z * g⁻¹) = g * z * g⁻¹ := by
    have hle : A ≤ MulAction.stabilizer (MulAut G) (g * z * g⁻¹) :=
      zpowers_le.mpr (hconj g)
    exact hle b.property
  have hz (b : A) : b • z = z := by simpa using hfix b 1
  have hC : fixedPointSubgroup A G ≤ centralizer ({z} : Set G) := by
    intro g hg
    exact mem_centralizer_singleton_iff.mpr (hfixed g (hg ⟨a,mem_zpowers a⟩)).eq
  have hD : commutatorAction A G ≤ centralizer ({z} : Set G) := by
    rw [commutatorAction_eq_closure, closure_le]
    rintro x ⟨b,g,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := hfix b g
    simp only [smul_mul', smul_inv', hz] at he
    calc
      (g⁻¹ * (b • g)) * z = g⁻¹ * ((b • g) * z * (b • g)⁻¹) * (b • g) := by group
      _ = g⁻¹ * (g * z * g⁻¹) * (b • g) := by rw [he]
      _ = z * (g⁻¹ * (b • g)) := by group
  have htop := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := G) (A := A) hsolv (by simpa only [A, Nat.card_zpowers] using hcop)
  have hle : (⊤ : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [← htop]
    exact sup_le hC hD
  exact mem_center_iff.mpr (fun g => mem_centralizer_singleton_iff.mp (hle (mem_top g)))

end BenderSuzuki.MatrixGroups.MultiplierFieldAction.TrivialActionCentrality

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory TrivialActionCentrality
universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

noncomputable def rootField (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) : MulAut (rootPreimage e f) where
  toFun x := ⟨liftedField e f hf x, (liftedField_mem_rootPreimage_iff e f hf x).mpr x.property⟩
  invFun x := ⟨(liftedField e f hf).symm x, (liftedField_mem_rootPreimage_iff e f hf _).mp (by
    simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext ((liftedField e f hf).symm_apply_apply x)
  right_inv x := Subtype.ext ((liftedField e f hf).apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul (liftedField e f hf) (x : U) (y : U))

theorem rootField_cube (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) : rootField e f hf ^ 3 = 1 := by
  ext x
  exact congrArg (fun a : MulAut U => a (x : U)) (liftedField_cube e f hf)

theorem rootField_fixed_iff (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U))
    (x : rootPreimage e f) : rootField e f hf x = x ↔
      suzukiFieldAutomorphism 1 (rootProjection e f x).val = (rootProjection e f x).val := by
  rw [Subtype.ext_iff]
  exact liftedField_fixed_iff e f hf hfour hfixed x

/-- The source subgroup generated by the lifted square and the kernel is central. -/
private theorem fixed_generator_square_central
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U))
    (x : rootPreimage e f) (hx : rootProjection e f x = rootPoint 1 0) :
    x ^ 2 ∈ center (rootPreimage e f) := by
  let q := rootProjection e f
  change q x = rootPoint 1 0 at hx
  have hs : Group.IsSolvable (rootPreimage e f) := by
    let : Group.IsNilpotent (rootPreimage e f) :=
      (IsPGroup.of_card (p := 2) (n := 8) (rootPreimage_card e f hfour)).isNilpotent
    infer_instance
  apply central_of_coprime_fixed_conjugates (rootField e f hf) hs
    (Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one (rootField_cube e f hf))
      (by rw [rootPreimage_card e f hfour]; decide))
  · intro g
    apply (rootField_fixed_iff e f hf hfour hfixed _).mpr
    have hcent : q x ^ 2 ∈ center (SuzukiRootSubgroup 1) :=
      suzukiRootSubgroup_square_mem_center 1 (by decide) (q x)
    have he : q (g * x ^ 2 * g⁻¹) = rootPoint 0 1 := by
      rw [map_mul, map_mul, map_inv, map_pow, mem_center_iff.mp hcent (q g)]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      rw [hx, rootPoint_one_sq]
    change suzukiFieldAutomorphism 1 (q (g * x ^ 2 * g⁻¹)).val = _
    rw [he, field_rootPoint]
    simp
  · intro g hg
    obtain ⟨n,hn⟩ := (fixed_root_iff (q g)).mp
      ((rootField_fixed_iff e f hf hfour hfixed g).mp hg)
    have hk : g * (x ^ n)⁻¹ ∈ q.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hx, hn, mul_inv_cancel]
    have hc : Commute (g * (x ^ n)⁻¹) (x ^ 2) :=
      (mem_center_iff.mp (rootProjection_ker_le_center e f hk) (x ^ 2)).symm
    have hpow : Commute (x ^ n) (x ^ 2) := (Commute.refl x).pow_pow n 2
    simpa only [inv_mul_cancel_right] using hc.mul_left hpow

/-- Trivial action on the covering kernel makes the full preimage of the actual
root center central in the lifted root group. This is the centrality branch of
GLS3 section 6.3, p.337; the contradiction is assembled by the caller. -/
public theorem rootCenterPreimage_le_center_of_liftedField_fixed
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U)) :
    rootCenterPreimage e f ≤ center (rootPreimage e f) := by
  obtain ⟨x,hx⟩ := rootProjection_surjective e f (rootPoint 1 0)
  have hxcent := fixed_generator_square_central e f hf hfour hfixed x hx
  intro z hz
  change rootProjection e f z ∈ center (SuzukiRootSubgroup 1) at hz
  rcases center_torus_orbit _ hz with hone | ⟨t,ht⟩
  · exact rootProjection_ker_le_center e f hone
  · obtain ⟨g,hg⟩ := matrixProjection_surjective e f (torusPoint t)
    have hgn : g ∈ normalizer (rootPreimage e f : Set U) := by
      intro y
      change matrixProjection e f y ∈ SuzukiRootSubgroup 1 ↔
        matrixProjection e f (g * y * g⁻¹) ∈ SuzukiRootSubgroup 1
      simp only [map_mul, map_inv, hg]
      exact suzukiSplitTorus_le_normalizer_root 1 (torusPoint_mem t) _
    let c := (rootPreimage e f).normalizerMonoidHom ⟨g,hgn⟩
    have hc : c (x ^ 2) ∈ center (rootPreimage e f) :=
      (centerCongr c ⟨x ^ 2,hxcent⟩).property
    have he : rootProjection e f (c (x ^ 2)) = rootProjection e f z := by
      apply Subtype.ext
      change matrixProjection e f (g * (x.val ^ 2) * g⁻¹) = _
      simp only [map_mul, map_inv, map_pow, hg]
      have hh := congrArg Subtype.val hx
      change matrixProjection e f x = (rootPoint 1 0).val at hh
      rw [hh, ← Subgroup.coe_pow, rootPoint_one_sq]
      exact ht.symm
    have hk : z * (c (x ^ 2))⁻¹ ∈ (rootProjection e f).ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hprod := (center (rootPreimage e f)).mul_mem (rootProjection_ker_le_center e f hk) hc
    simpa only [inv_mul_cancel_right] using hprod
end BenderSuzuki.MatrixGroups.MultiplierFieldAction

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory
universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- Under trivial kernel action, the actual lifted root group has class at most two. -/
public theorem rootPreimage_commutator_le_center_of_liftedField_fixed
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U)) :
    _root_.commutator (rootPreimage e f) ≤ center (rootPreimage e f) := by
  rw [rootPreimage_commutator_eq e f hfour]
  exact rootCenterPreimage_le_center_of_liftedField_fixed e f hf hfour hfixed

/-- The literal canonical multiplier action supplies the pointwise kernel hypothesis. -/
public theorem rootCenterPreimage_le_center_of_multiplierAction_eq_one
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (htrivial : Covering.multiplierAction f hf
      (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) = 1) :
    rootCenterPreimage e f ≤ center (rootPreimage e f) := by
  apply rootCenterPreimage_le_center_of_liftedField_fixed e f hf hfour
  intro k
  exact congrArg (fun a : MulAut f.toMonoidHom.ker => (a k : U)) htrivial
end BenderSuzuki.MatrixGroups.MultiplierFieldAction
