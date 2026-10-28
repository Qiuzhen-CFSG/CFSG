module

public import Theory.Representation.SL3OddNaturalNormalizer.PointFixers
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.G2NaturalNormalizerOffenders
public import Theory.Representation.CentralCoverOriginalAction.Quadratic

/-!
# Two-power point fixers in the three natural models

A binary normalizer fixing a nonzero field subspace has trivial coefficient
field action. In the SL₃ model its determinant has two-power order and is one.
In Sp₄ and G₂ the operator is a scalar times a natural group element;
centerlessness and the two-power order force that scalar to be one.
Thus the original operator, and not only its conjugation automorphism,
is an actual natural group operator. Arbitrary two-power order is retained.

The chosen-flag consumer is in PointFixer. This is the natural-action step
used to eliminate the outer witness on L₁/O₂(L₁); it does not classify
relative-component embeddings or construct the field-four triangle.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762. The imported octonion and automorphism
calculations retain their ATLAS attribution; no new ATLAS source is copied.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.PointFixer

private theorem two_power_eq_one {F : Type*} [Field F] [CharP F 2]
    (c : F) (k : ℕ) (hc : c ^ (2 ^ k) = 1) : c = 1 := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    apply ih
    apply CharTwo.sq_injective
    simpa only [← pow_mul, ← pow_succ, one_pow] using hc

private theorem intertwines_pow {F A W : Type*} [Field F] [Group A]
    [AddCommGroup W] [Module F W] [Module (ZMod 2) W]
    (ρ : Representation F A W) (a : MulAut A) (e : W ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = ρ (a g) (e v)) (n : ℕ) (g : A) (v : W) :
    (e ^ n) (ρ g v) = ρ ((a ^ n) g) ((e ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change e ((e ^ n) (ρ g v)) = ρ (a ((a ^ n) g)) (e ((e ^ n) v))
    rw [ih, he]

private theorem automorphism_pow_eq_one {F A W : Type*} [Field F] [Group A]
    [AddCommGroup W] [Module F W] [Module (ZMod 2) W]
    (ρ : Representation F A W) (hf : Function.Injective ρ)
    (a : MulAut A) (e : W ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = ρ (a g) (e v)) {n : ℕ} (hn : e ^ n = 1) :
    a ^ n = 1 := by
  ext g : 1
  apply hf
  apply LinearMap.ext
  intro v
  have hh := intertwines_pow ρ a e he n g v
  rw [hn] at hh
  exact hh.symm

private theorem scalar_eq_one {F A W : Type*} [Field F] [CharP F 2] [Group A]
    [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [Nontrivial W]
    (ρ : Representation F A W) (e : W ≃ₗ[ZMod 2] W)
    (c : F) (g : A) (he : ∀ v, e v = c • ρ g v)
    {k : ℕ} (hp : e ^ (2 ^ k) = 1) (hg : g ^ (2 ^ k) = 1) : c = 1 := by
  have hpow (n : ℕ) (v : W) : (e ^ n) v = c ^ n • ρ (g ^ n) v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ', pow_succ']
      change e ((e ^ n) v) = _
      rw [ih, he, map_smul, smul_smul, map_mul]
      rfl
  obtain ⟨v,hv⟩ := exists_ne (0 : W)
  have hh := hpow (2 ^ k) v
  rw [hp, hg, map_one] at hh
  have hc : c ^ (2 ^ k) = 1 := by
    apply smul_left_injective F hv
    simpa using hh.symm
  exact two_power_eq_one c k hc

private theorem linear_of_fixes {F W : Type*} [Field F] [AddCommGroup W]
    [Module F W] [Module (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] W) (σ : F ≃+* F)
    (hσ : ∀ c v, e (c • v) = σ c • e v)
    (P : Submodule F W) (hP : P ≠ ⊥) (hfix : ∀ v ∈ P, e v = v) :
    σ = 1 := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  ext c
  apply smul_left_injective F hv0
  have hh := hσ c v
  rw [hfix v hv, hfix (c • v) (P.smul_mem c hv)] at hh
  exact hh.symm

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A two-power point fixer is an actual determinant-one natural operator. -/
theorem sl3_operator (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F))
    (e : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F))
    (he : ∀ g v, e (specialLinearNatural 3 g v) = specialLinearNatural 3 (a g) (e v))
    (P : Submodule F (Fin 3 → F)) (hP : P ≠ ⊥)
    (hfix : ∀ v ∈ P, e v = v) {k : ℕ} (hp : e ^ (2 ^ k) = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ v, e v = specialLinearNatural 3 g v := by
  obtain ⟨σ,hσ⟩ := OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (specialLinearNatural (k := F) 3) (fun f hf => SL3OddNaturalNormalizer.centralizer_scalar f hf) a e he
  have hs := linear_of_fixes e σ hσ P hP hfix
  let d : Module.End F (Fin 3 → F) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by intro c v; simpa only [hs, RingAut.one_apply, RingHom.id_apply] using hσ c v }
  have hd : d ^ (2 ^ k) = 1 := by
    apply LinearMap.ext
    intro v
    have heq (n : ℕ) : (d ^ n) v = (e ^ n) v := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ',pow_succ']
        change e ((d ^ n) v) = e ((e ^ n) v)
        rw [ih]
    rw [heq,hp]
    rfl
  have hm : (LinearMap.toMatrix' d) ^ (2 ^ k) = 1 := by
    have heq (n : ℕ) : LinearMap.toMatrix' (d ^ n) = (LinearMap.toMatrix' d) ^ n := by
      induction n with
      | zero => exact LinearMap.toMatrix'_one
      | succ n ih => rw [pow_succ, LinearMap.toMatrix'_mul, ih, pow_succ]
    rw [← heq, hd, LinearMap.toMatrix'_one]
  have hdet : (LinearMap.toMatrix' d).det = 1 :=
    two_power_eq_one _ k (by rw [← Matrix.det_pow,hm,Matrix.det_one])
  exact ⟨⟨LinearMap.toMatrix' d,hdet⟩,fun v => (LinearMap.toMatrix'_mulVec d v).symm⟩

open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer

/-- A two-power point fixer is an actual symplectic natural operator. -/
theorem sp4_operator (hq : 2 < Nat.card F) (a : MulAut (Sp F))
    (e : Vector F ≃ₗ[ZMod 2] Vector F)
    (he : ∀ g v, e (symplecticNatural 2 g v) = symplecticNatural 2 (a g) (e v))
    (P : Submodule F (Vector F)) (hP : P ≠ ⊥)
    (hfix : ∀ v ∈ P, e v = v) {k : ℕ} (hp : e ^ (2 ^ k) = 1) :
    ∃ g : Sp F, ∀ v, e v = symplecticNatural 2 g v := by
  let : Finite (Vector F ≃ₗ[ZMod 2] Vector F) :=
    Finite.of_injective (fun u : Vector F ≃ₗ[ZMod 2] Vector F => (u : Vector F → Vector F))
      DFunLike.coe_injective
  have hn : e ∈ naturalNormalizer := by
    apply mem_normalizer_fintype
    rintro _ ⟨g,rfl⟩
    have heq : e * linearAction naturalDerivedAction g * e⁻¹ =
        SymplecticNaturalNormalizer.naturalHom (a g.val) := by
      apply LinearEquiv.ext
      intro v
      change e (symplecticNatural 2 g.val (e.symm v)) = _
      rw [he, e.apply_symm_apply]
      rfl
    rw [heq]
    exact SymplecticNaturalNormalizer.naturalHom_mem hq _
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨c,g,hg⟩ := SymplecticNaturalNormalizer.scalar_symplectic_of_fixes_field_line
    ⟨e,hn⟩ v hv0 (fun b => hfix _ (P.smul_mem b hv))
  have ha : a = MulAut.conj g := by
    apply (SymplecticNaturalNormalizer.conjugation_eq_of_intertwines hq ⟨e,hn⟩ a he).symm.trans
    apply SymplecticNaturalNormalizer.conjugation_eq_of_intertwines
    intro x w
    change e (symplecticNatural 2 x w) = symplecticNatural 2 (g*x*g⁻¹) (e w)
    have hg' : ∀ v, e v = c.val • symplecticNatural 2 g v := hg
    rw [hg',hg',map_smul]
    change c.val • symplecticNatural 2 g (symplecticNatural 2 x w) =
      c.val • symplecticNatural 2 (g*x*g⁻¹) (symplecticNatural 2 g w)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have hgp : g ^ (2 ^ k) = 1 := by
    apply DiagramAutomorphisms.InvolutionNormalForms.inner_injective
    have hfaith : Function.Injective (symplecticNatural (k := F) 2) := by
      intro x y h
      apply SymplecticNaturalNormalizer.naturalHom_injective
      exact LinearEquiv.ext (fun v => LinearMap.congr_fun h v)
    rw [map_pow,← ha,automorphism_pow_eq_one (symplecticNatural 2)
      hfaith a e he hp,map_one]
  have hc := scalar_eq_one (symplecticNatural 2) e c.val g hg hp hgp
  exact ⟨g,fun v => by simpa only [hc,one_smul] using hg v⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.PointFixer

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.PointFixer
open Atlas.G2 Atlas.G2.Natural Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-- A two-power point fixer is an actual octonion natural operator. -/
theorem g2_operator (hq : 2 < Nat.card F) (a : MulAut (Model F))
    (e : Space F ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, e (Natural.action F g v) = Natural.action F (a g) (e v))
    (P : Submodule F (Space F)) (hP : P ≠ ⊥)
    (hfix : ∀ v ∈ P, e v = v) {k : ℕ} (hp : e ^ (2 ^ k) = 1) :
    ∃ g : Model F, ∀ v, e v = Natural.action F g v := by
  let : Finite (BinaryOffender.actionImage (Normalizer.binary F)) :=
    Finite.of_surjective _ (Normalizer.binary F).asGroupHom.rangeRestrict_surjective
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv e
  have hn : u ∈ BinaryOffender.linearNormalizer (Normalizer.binary F) := by
    apply mem_normalizer_fintype
    rintro _ ⟨g,rfl⟩
    refine ⟨a g,?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    change Normalizer.binary F (a g) v = e (Normalizer.binary F g (e.symm v))
    rw [Normalizer.binary_apply,Normalizer.binary_apply]
    change Natural.action F (a g) v = e (Natural.action F g (e.symm v))
    rw [he,e.apply_symm_apply]
  let t : BinaryOffender.linearNormalizer (Normalizer.binary F) := ⟨u,hn⟩
  have ht : Normalizer.normalizerAutomorphism F t = a := by
    ext g : 1
    apply Natural.action_injective F
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := e.surjective v
    exact (Normalizer.normalizerAutomorphism_intertwines F t g v).symm.trans (he g v)
  obtain ⟨g,σ,ha⟩ := LieAutomorphismExtensions.exists_inner_field hq a
  obtain ⟨c,hc⟩ := Normalizer.normalizer_scalar_factor F t g σ (ht.trans ha)
  have hsemi (b : F) (v : Space F) : e (b • v) = σ b • e v := by
    change t.val.val (b • v) = σ b • t.val.val v
    rw [hc,hc,Normalizer.field_smul,map_smul,smul_comm]
  have hs := linear_of_fixes e σ hsemi P hP hfix
  have hformula (v : Space F) : e v = c • Natural.action F g v := by
    have hfield : BinarySemilinear.fieldEquivalence F σ v = v := by
      rw [hs]
      apply (BinarySemilinear.coordinatesEquiv F).injective
      exact (BinarySemilinear.coordinatesEquiv F).apply_symm_apply _
    have hh := hc v
    rw [hfield] at hh
    exact hh
  have ha' : a = MulAut.conj g := by simpa only [hs,map_one,mul_one] using ha
  have hgp : g ^ (2 ^ k) = 1 := by
    apply conj_injective_of_center_eq_bot (LieAutomorphismExtensions.model_center_eq_bot hq)
    rw [map_pow,← ha',automorphism_pow_eq_one (Natural.action F)
      (Natural.action_injective F) a e he hp,map_one]
  let : Nontrivial (Space F) := Module.nontrivial_of_finrank_pos
    (by rw [Natural.finrank_space]; decide : 0 < Module.finrank F (Space F))
  have hc1 := scalar_eq_one (Natural.action F) e c g hformula hp hgp
  exact ⟨g,fun v => by simpa only [hc1,one_smul] using hformula v⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.PointFixer
