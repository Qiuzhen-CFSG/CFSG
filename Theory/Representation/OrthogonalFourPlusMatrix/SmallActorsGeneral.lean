module
public import Theory.Representation.OrthogonalFourPlusMatrix.NaturalTensor
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActors
public import Theory.Representation.ScalarCoinvariants

/-!
# Small elementary actors on determinant tensors over binary fields

An elementary subgroup of the full binary normalizer moving fewer than twice
its coefficient-field degree has rank at most one. Small displacement first
kills the field action. Restriction of scalars then makes its common fixed
space a hyperplane over that field. Invariant quadratic forms show that the
involutions preserve the determinant, and the pointwise stabilizer of a
quadratic hyperplane has at most two elements.

The coefficient field, the marked two-factor representation and its full
normalizer are retained. The original Chapter 10 higher-Thompson actor uses
this result on its literal seed image, without assuming that image is faithful
on the full module.
Source: Aschbacher--Smith H.1.1(2) and 9.2.1, printed pp.378,730,
refs/quasithin.pdf.
-/

public noncomputable section
open Module Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.NaturalTensor
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem exists_scalar (hF : 2 < Nat.card F) : ∃ a : F, a ≠ 0 ∧ a*a ≠ 1 := by
  have hex : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! h
    let f : Bool → F := fun b => if b then 1 else 0
    have hs : Function.Surjective f := by
      intro a
      by_cases ha : a = 0
      · exact ⟨false,ha.symm⟩
      · exact ⟨true,(h a ha).symm⟩
    have hc := Nat.card_le_card_of_surjective f hs
    have hb : Nat.card Bool = 2 := by simp
    rw [hb] at hc
    omega
  obtain ⟨a,ha,h1⟩ := hex
  refine ⟨a,ha,fun h => h1 ?_⟩
  exact CharTwo.sq_injective (by simpa only [pow_two,one_mul] using h)

omit [Finite F] [Algebra (ZMod 2) F] in
/-- A field-linear normalizer involution preserves the determinant over any finite
binary field with more than two elements. -/
theorem field_involution_preserves_determinant (hF : 2 < Nat.card F)
    (t : Mat (F := F) ≃ₗ[F] Mat (F := F))
    (hconj : ∀ g : PairSL (F := F), ∃ h : PairSL (F := F),
      ∀ v, t (representation g v) = representation h (t v))
    (h2 : ∀ v, t (t v) = v) : ∀ v, (t v).det = v.det := by
  let q := determinantForm.comp t.toLinearMap
  have hq (g : PairSL (F := F)) (v : Mat (F := F)) :
      q (matrixAction g v) = q v := by
    obtain ⟨h,hh⟩ := hconj g
    simp only [q, QuadraticMap.comp_apply, determinantForm_apply]
    change (t (representation g v)).det = (t v).det
    rw [hh]
    exact matrixAction_det h (t v)
  obtain ⟨a,ha,ha2⟩ := exists_scalar hF
  obtain ⟨c,hc⟩ := invariant_quadratic_eq_det a ha ha2 q hq
  have hc' (v : Mat (F := F)) : (t v).det = c*v.det := by
    simpa only [q, QuadraticMap.comp_apply, LinearEquiv.coe_coe, determinantForm_apply] using hc v
  have hc1 : (t (1 : Mat (F := F))).det = c := by simpa using hc' 1
  have hcc : c*c = 1 := by
    have hh := hc' (t 1)
    rw [h2,hc1,Matrix.det_one] at hh
    exact hh.symm
  have he : c = 1 := CharTwo.sq_injective (by simpa only [pow_two,one_mul] using hcc)
  simpa only [he,one_mul] using hc'

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem card_le_two_of_fixed_hyperplane
    {K W : Type*} [Group K] [AddCommGroup W] [Module F W] [Module.Finite F W]
    (ρ : Representation F K W) (hfaith : Function.Injective ρ)
    (q : QuadraticForm F W) (hq : q.polarBilin.SeparatingLeft)
    (hiso : ∀ a v, q (ρ a v) = q v)
    (hsmall : finrank F (W ⧸ ρ.invariants) ≤ 1) : Nat.card K ≤ 2 := by
  classical
  by_cases ht : ∀ t : K, t = 1
  · have hs : Function.Surjective (fun _ : Unit => (1 : K)) := fun t => ⟨(),(ht t).symm⟩
    have hh := Nat.card_le_card_of_surjective _ hs
    simp only [Nat.card_unique] at hh
    omega
  push Not at ht
  obtain ⟨t,ht⟩ := ht
  let et := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  have het : et ≠ 1 := by
    intro hh
    apply ht
    apply hfaith
    exact (congrArg LinearEquiv.toLinearMap hh).trans ρ.map_one.symm
  have hle : ρ.invariants ≤ LinearMap.ker (et.toLinearMap - LinearMap.id) := by
    intro v hv
    exact sub_eq_zero.mpr (hv t)
  have hrt : finrank F (et.toLinearMap - LinearMap.id).range ≤ 1 := by
    have hm := Submodule.finrank_mono hle
    have hnull := (et.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
    have hc := Submodule.finrank_quotient_add_finrank ρ.invariants
    omega
  have hpos : 0 < finrank F (et.toLinearMap - LinearMap.id).range := by
    by_contra! hz
    have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
    exact het (LinearEquiv.toLinearMap_injective (sub_eq_zero.mp he))
  have hfixed : ρ.invariants = LinearMap.ker (et.toLinearMap - LinearMap.id) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have hnull := (et.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
    have hc := Submodule.finrank_quotient_add_finrank ρ.invariants
    omega
  have hall (s : K) : s = 1 ∨ s = t := by
    let es := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom s)
    have hfix (v : W) (hv : et v = v) : es v = v := by
      have hh : v ∈ ρ.invariants := hfixed.symm ▸ sub_eq_zero.mpr hv
      exact hh s
    rcases QuadraticForm.eq_one_or_eq_of_fixed_rank_one q hq et es
      (hiso t) (hiso s) hrt het hfix with hs | hs
    · exact Or.inl (hfaith ((congrArg LinearEquiv.toLinearMap hs).trans ρ.map_one.symm))
    · exact Or.inr (hfaith (congrArg LinearEquiv.toLinearMap hs))
  let b : Bool → K := fun x => if x then t else 1
  have hb : Function.Surjective b := by
    intro s
    rcases hall s with hs | hs
    · exact ⟨false,hs.symm⟩
    · exact ⟨true,hs.symm⟩
  have he : Nat.card Bool = 2 := by simp
  simpa only [he] using Nat.card_le_card_of_surjective b hb

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- An elementary subgroup of the full tensor normalizer with common fixed
codimension below twice the field degree has at most one binary generator. -/
theorem rank_le_one_of_fixedCodim_lt_twice_degree (hF : 2 < Nat.card F)
    (σ : Representation (ZMod 2) (PairSL (F := F)) V) (hσ : Function.Injective σ)
    (e : MulAut (PairSL (F := F))) (f : V ≃ₗ[ZMod 2] Mat (F := F))
    (hf : ∀ g v, f (σ g v) = representation (e g) (f v))
    (A : Subgroup (linearNormalizer σ)) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation σ) A < 2*finrank (ZMod 2) F) :
    rank A ≤ 1 := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.equiv f.symm
  obtain ⟨φ,hφ⟩ := normalizer_semilinear σ hσ e f hf
  let ρb : Representation (ZMod 2) A (Mat (F := F)) :=
    f.conjRingEquiv.toMonoidHom.comp ((normalizerRepresentation σ).comp A.subtype)
  have hcoord (a : A) (v : V) : ρb a (f v) = f (normalizerRepresentation σ a.val v) := by
    change f (a.val.val.val (f.symm (f v))) = _
    rw [f.symm_apply_apply]
    rfl
  have hsem (a : A) (c : F) (v : Mat (F := F)) :
      ρb a (c • v) = φ a.val c • ρb a v := by
    have hh := hφ a.val c (f.symm v)
    change f (normalizerRepresentation σ a.val (f.symm (c • v))) =
      φ a.val c • f (normalizerRepresentation σ a.val (f.symm v))
    simpa only [f.apply_symm_apply] using hh
  have hfield (a : A) (c : F) : φ a.val c = c := by
    by_contra hc
    have hh := finrank_le_twice_operatorFixedCodim (ρb a) (φ a.val).toRingHom ⟨c,hc⟩ (hsem a)
    have hd : finrank (ZMod 2) (Mat (F := F)) = 4*finrank (ZMod 2) F := by
      rw [←Module.finrank_mul_finrank (ZMod 2) F]
      have he : finrank F (Mat (F := F)) = 4 := by
        change finrank F (Matrix (Fin 2) (Fin 2) F) = 4
        rw [Module.finrank_matrix]
        norm_num
      rw [he,Nat.mul_comm]
    have he := operatorFixedCodim_eq_of_equiv
      (normalizerRepresentation σ a.val) (ρb a) f (fun v => (hcoord a v).symm)
    have hb := operatorFixedCodim_le_fixedCodim (normalizerRepresentation σ) A a.property
    rw [hd,←he] at hh
    omega
  let ρ : Representation F A (Mat (F := F)) := {
    toFun := fun a => {
      toFun := ρb a
      map_add' := (ρb a).map_add
      map_smul' := fun c v => by simpa only [hfield, RingHom.id_apply] using hsem a c v }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρb.map_one v
    map_mul' a b := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρb.map_mul a b) v }
  have hfaith : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply f.injective
    have he := LinearMap.congr_fun hab (f v)
    change ρb a (f v) = ρb b (f v) at he
    change f (normalizerRepresentation σ a.val v) = f (normalizerRepresentation σ b.val v)
    simpa only [hcoord] using he
  have hdet (a : A) (v : Mat (F := F)) : (ρ a v).det = v.det := by
    let t := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
    apply field_involution_preserves_determinant hF t
    · intro g
      obtain ⟨h,hh⟩ := (mem_normalizer_iff.mp a.val.property (σ.asGroupHom (e.symm g))).mp ⟨_,rfl⟩
      have hmul : a.val.val * σ.asGroupHom (e.symm g) = σ.asGroupHom h * a.val.val :=
        mul_inv_eq_iff_eq_mul.mp hh.symm
      have hact (w : V) : normalizerRepresentation σ a.val (σ (e.symm g) w) =
          σ h (normalizerRepresentation σ a.val w) :=
        congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val w) hmul
      refine ⟨e h,fun w => ?_⟩
      obtain ⟨v,rfl⟩ := f.surjective w
      change ρb a (representation g (f v)) = representation (e h) (ρb a (f v))
      rw [←e.apply_symm_apply g,←hf,hcoord,hact,hf,hcoord]
    · intro w
      have ha : a*a = 1 := by
        simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
      change ρ a (ρ a w) = w
      rw [←Module.End.mul_apply,←map_mul,ha,map_one,Module.End.one_apply]
  have hc : fixedCodim ρb ⊤ = fixedCodim (normalizerRepresentation σ) A := by
    have hh := fixedCodim_map_equivariant
      ((normalizerRepresentation σ).comp A.subtype) ρb (MonoidHom.id A) f
      (fun a v => (hcoord a v).symm) ⊤
    have hm : (⊤ : Subgroup A).map A.subtype = A := by
      ext a
      constructor
      · rintro ⟨b,_,rfl⟩; exact b.property
      · intro ha; exact ⟨⟨a,ha⟩,mem_top _,rfl⟩
    have hid : (⊤ : Subgroup A).map (MonoidHom.id A) = ⊤ := Subgroup.map_id _
    rw [hid] at hh
    rw [←hh,fixedCodim,fixedSpace_comp_map,hm]
    rfl
  have hcod : finrank F ((Mat (F := F)) ⧸ ρ.invariants) ≤ 1 := by
    have hh := fixedCodim_restrictScalars ρ ⊤
    have hinv : invariants (ρ.comp (⊤ : Subgroup A).subtype) = ρ.invariants := by
      ext v
      exact ⟨fun h a => h ⟨a,mem_top _⟩,fun h a => h a⟩
    rw [hinv] at hh
    change fixedCodim ρb ⊤ = _ at hh
    rw [hc] at hh
    have hprod : finrank (ZMod 2) F * finrank F ((Mat (F := F)) ⧸ ρ.invariants) <
        finrank (ZMod 2) F * 2 := by omega
    have hlt := Nat.lt_of_mul_lt_mul_left hprod
    omega
  have hcard := card_le_two_of_fixed_hyperplane ρ hfaith determinantForm
    determinant_polar_separating (fun a v => by simpa only [determinantForm_apply] using hdet a v) hcod
  exact Nat.log_mono_right hcard
end ClassicalOrthogonal.FourPlusMatrix.NaturalTensor
