module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.GenerationContract

/-!
# Three conjugate involutions generate the binary natural component

Choose a generator a of the multiplicative group of the coefficient field.
The transvections in positions (0,1), (1,2), (2,0), with coefficients 1, 1, a,
generate SL₃: elementary commutators first give every power of a in position
(0,1), then give every coefficient in all six root positions. Elementary
matrix generation finishes this intrinsic group argument.

For odd binary field degree the scalar center of SL₃ is trivial. The actual
projective Sylow subgroup therefore places every involution in the concrete
unitriangular group, where the existing determinant-one conjugators send it
to the highest-root transvection. Conjugating the generating triple proves
`ThreeInvolutionGeneration`; the seed application transports it through the
same group equivalence that marks the natural action, to the literal component.

Source motivation: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed p.108, the chief-factor fixed-codimension estimate before (!).
This supplies the intrinsic generation prerequisite for the conditional
consumers in `FixedCodimension`, without importing that assembly module.
The elementary identities reuse the attributed ATLAS port `Elementary`.
-/

public section

open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups commutatorElement
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.EvenInnerCentralizers
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
variable {F : Type*} [Field F]

private theorem comm_mem (H : Subgroup SL(3,F)) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) {a b : F}
    (ha : transvection hik a ∈ H) (hb : transvection hkj b ∈ H) :
    transvection hij (a * b) ∈ H := by
  rw [← Atlas.elementary_commutator hij hik hkj]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem cyclic_root_generation [Finite F] :
    ∃ a : F, a ≠ 0 ∧
      zpowers (transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)) ⊔
      zpowers (transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F)) ⊔
      zpowers (transvection (show (2 : Fin 3) ≠ 0 by decide) a) = ⊤ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  refine ⟨a, a.ne_zero, ?_⟩
  let H : Subgroup SL(3,F) :=
    zpowers (transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)) ⊔
    zpowers (transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F)) ⊔
    zpowers (transvection (show (2 : Fin 3) ≠ 0 by decide) (a : F))
  have h01 : transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) ∈ H :=
    mem_sup_left (mem_sup_left (mem_zpowers _))
  have h12 : transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) ∈ H :=
    mem_sup_left (mem_sup_right (mem_zpowers _))
  have h20 : transvection (show (2 : Fin 3) ≠ 0 by decide) (a : F) ∈ H :=
    mem_sup_right (mem_zpowers _)
  have h21 : transvection (show (2 : Fin 3) ≠ 1 by decide) (a : F) ∈ H := by
    simpa using comm_mem H (by decide) (by decide) (by decide) h20 h01
  have hp (n : ℕ) : transvection (show (0 : Fin 3) ≠ 1 by decide) ((a : F)^n) ∈ H := by
    induction n with
    | zero => simpa using h01
    | succ n ih =>
      have h02n : transvection (show (0 : Fin 3) ≠ 2 by decide) ((a : F)^n) ∈ H := by
        simpa using comm_mem H (by decide) (by decide) (by decide) ih h12
      simpa [pow_succ] using comm_mem H (by decide) (by decide) (by decide) h02n h21
  have hall01 (b : F) : transvection (show (0 : Fin 3) ≠ 1 by decide) b ∈ H := by
    by_cases hb : b = 0
    · subst b
      simp
    · obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (ha (Units.mk0 b hb))
      have hn' : (a : F) ^ n = b := by simpa using congrArg Units.val hn
      rw [← hn']
      exact hp n
  have hall21 (b : F) : transvection (show (2 : Fin 3) ≠ 1 by decide) b ∈ H := by
    simpa using comm_mem H (by decide) (by decide) (by decide) h20 (hall01 ((a : F)⁻¹ * b))
  have hall12 (b : F) : transvection (show (1 : Fin 3) ≠ 2 by decide) b ∈ H := by
    have h10 : transvection (show (1 : Fin 3) ≠ 0 by decide) (a : F) ∈ H := by
      simpa using comm_mem H (by decide) (by decide) (by decide) h12 h20
    have h02b : transvection (show (0 : Fin 3) ≠ 2 by decide) ((a : F)⁻¹ * b) ∈ H := by
      simpa using comm_mem H (by decide) (by decide) (by decide)
        (hall01 ((a : F)⁻¹ * b)) h12
    simpa using comm_mem H (by decide) (by decide) (by decide) h10 h02b
  have hall10 (b : F) : transvection (show (1 : Fin 3) ≠ 0 by decide) b ∈ H := by
    simpa using comm_mem H (by decide) (by decide) (by decide) (hall12 (b * (a : F)⁻¹)) h20
  have hall20 (b : F) : transvection (show (2 : Fin 3) ≠ 0 by decide) b ∈ H := by
    simpa using comm_mem H (by decide) (by decide) (by decide) (hall21 b) (hall10 1)
  have hall02 (b : F) : transvection (show (0 : Fin 3) ≠ 2 by decide) b ∈ H := by
    simpa using comm_mem H (by decide) (by decide) (by decide) (hall01 b) h12
  change H = ⊤
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij b
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | exact hall01 b | exact hall02 b |
    exact hall10 b | exact hall12 b | exact hall20 b | exact hall21 b

private theorem involution_isConj_root (F : BinaryField) (hodd : Odd F.degree)
    (t : SL(3,F.Carrier)) (ht2 : t ^ 2 = 1) (ht : t ≠ 1) :
    IsConj t (rootSL F.Carrier) := by
  have hZ : center SL(3,F.Carrier) = ⊥ := by
    rw [← Subgroup.card_eq_one, Atlas.ExceptionalSupport.card_sl_center,
      Fintype.card_fin, F.card_eq]
    obtain ⟨k, hk⟩ := hodd
    have hm : 2 ^ F.degree % 3 = 2 := by
      rw [hk, pow_add, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    apply Nat.Coprime.gcd_eq_one
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    have hp : 0 < 2 ^ F.degree := pow_pos (by decide) _
    omega
  let e := Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier hZ
  have he : Function.Injective (Matrix.PSL3.projection F.Carrier) := by
    intro a b hab
    apply e.injective
    simpa only [e, Matrix.SL3.equivProjectiveOfCenterEqBot_apply] using hab
  have hpt : Matrix.PSL3.projection F.Carrier t ≠ 1 := by
    intro h
    exact ht (he (h.trans (map_one _).symm))
  have hpt2 : (Matrix.PSL3.projection F.Carrier t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  let S := Matrix.PSL3.LinearThree.unipotentSylow F.Carrier F.degree_pos F.card_eq
  obtain ⟨y, hty⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
    (by simpa only [pow_one] using orderOf_eq_prime hpt2 hpt)
  have hy : (y : PSL(3,F.Carrier)) ∈ (projective F.Carrier).range :=
    (Matrix.PSL3.LinearThree.projective_range F.Carrier).ge y.property
  obtain ⟨u, hu⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp hty
  obtain ⟨k, hk⟩ := Matrix.PSL3.projection_surjective F.Carrier g
  have hc : MulAut.conj k t = specialLinear F.Carrier u := by
    apply he
    change Matrix.PSL3.projection F.Carrier (k * t * k⁻¹) = projective F.Carrier u
    simpa only [map_mul, map_inv, hk] using hg.trans hu.symm
  have hu2 : u ^ 2 = 1 := by
    apply specialLinear_injective F.Carrier
    rw [map_pow, ← hc, ← map_pow, ht2, map_one, map_one]
  have hun : u ≠ 1 := by
    intro hu1
    apply ht
    apply (MulAut.conj k).injective
    rw [hc, hu1, map_one, map_one]
  exact (isConj_iff.mpr ⟨k, hc⟩).trans
    (specialLinear_isConj_root F.Carrier u hun hu2)

private theorem transvection_sq {F : Type*} [Field F] [CharP F 2]
    {i j : Fin 3} (hij : i ≠ j) (a : F) :
    (SpecialLinearGroup.transvection hij a) ^ 2 = 1 := by
  rw [pow_two, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

private theorem transvection_ne {F : Type*} [Field F]
    {i j : Fin 3} (hij : i ≠ j) {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.transvection hij a ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(3,F) => g.val i j) h
  exact ha (by simpa [SpecialLinearGroup.transvection_coe, hij] using hh)

private theorem generation_by_conjugates {G : Type*} [Group G]
    {t x y z : G} (hgen : zpowers x ⊔ zpowers y ⊔ zpowers z = ⊤)
    (hx : IsConj t x) (hy : IsConj t y) (hz : IsConj t z) :
    ∃ g h, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hx
  obtain ⟨b, hb⟩ := isConj_iff.mp hy
  obtain ⟨c, hc⟩ := isConj_iff.mp hz
  let e := MulAut.conj a⁻¹
  have hex : e x = t := by
    rw [← ha]
    dsimp [e]
    group
  have hey : e y = (a⁻¹ * b) * t * (a⁻¹ * b)⁻¹ := by
    rw [← hb]
    dsimp [e]
    group
  have hez : e z = (a⁻¹ * c) * t * (a⁻¹ * c)⁻¹ := by
    rw [← hc]
    dsimp [e]
    group
  refine ⟨a⁻¹ * b, a⁻¹ * c, ?_⟩
  have hh := congrArg (Subgroup.map e.toMonoidHom) hgen
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    hex, hey, hez, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hh

/-- Three conjugates of each nonidentity involution generate the actual SL₃
of a binary field of odd degree. No module or codimension input is used. -/
theorem threeInvolutionGeneration (F : BinaryField) (hodd : Odd F.degree) :
    ThreeInvolutionGeneration F := by
  intro t ht2 ht
  obtain ⟨a, ha, hgen⟩ := cyclic_root_generation (F := F.Carrier)
  apply generation_by_conjugates hgen
  all_goals
    apply (involution_isConj_root F hodd t ht2 ht).trans
    apply IsConj.symm
    apply involution_isConj_root F hodd
    · exact transvection_sq _ _
    · apply transvection_ne
      first | exact one_ne_zero | exact ha

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The published natural seed discharges the field and odd-degree hypotheses
of the intrinsic matrix-generation theorem. -/
theorem seed_threeInvolutionGeneration {A L : Subgroup G} (s : NaturalSeed ρ A L) :
    ThreeInvolutionGeneration s.field :=
  threeInvolutionGeneration s.field s.odd_degree

/-- Three conjugates in the literal component L generate L, transported along
the same group equivalence that marks the seed's natural action. -/
theorem seed_component_three_involutions {A L : Subgroup G} (s : NaturalSeed ρ A L)
    (t : L) (ht2 : t ^ 2 = 1) (ht : t ≠ 1) :
    ∃ g h : L, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  let e := s.natural.groupEquiv
  obtain ⟨g, h, hgen⟩ := seed_threeInvolutionGeneration ρ s (e t)
    (by rw [← map_pow, ht2, map_one])
    (fun ht0 => ht (e.injective (ht0.trans e.map_one.symm)))
  refine ⟨e.symm g, e.symm h, ?_⟩
  have hh := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv, e.symm_apply_apply,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using hh

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
