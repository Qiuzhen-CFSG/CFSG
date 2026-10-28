module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesActions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldAction
public import Theory.Representation.SL2NaturalOffenders.FixedField.Stabilizer
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The natural fixed-space module in 6.1.14

The field witness and the original natural marking may use different fields
and quotient coordinates. Transporting the quotient actor between these
markings preserves its outer involution. Its nonzero fixed space forces the
actual vector action to be involutory, without lifting an involution through
the action kernel.

The literal N_L(U) maps onto the fixed actors with a two-group kernel. Fixed
field descent supplies compatible natural coordinates on U, and core lifting
identifies the kernel with O₂(N_L(U)). For n>2 the fixed-field SL₂ is perfect,
so the embedded residual O²(N_L(U)) has the same natural action, with its own
intrinsic two-core. This proves the opening module calculation of 6.1.14.
The Sylow arrangement, quotient B/U calculation, and action on a conjugate
of Z_S remain separate steps of the same contained-branch owner.

Source: Aschbacher--Smith, 6.1.14, printed pp.670--671 (PDF pp.687--688).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] {L B : Subgroup G}

/-- Quotient actor markings change by the same group equivalence. -/
theorem quotientActor_change_field
    {F K : Type} [Field F] [Field K]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (d : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (t : normalizer (L : Set G)) :
    MulAut.congr (e.symm.trans d) (quotientActor e t) = quotientActor d t := by
  ext x
  obtain ⟨q, rfl⟩ := d.surjective x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, quotientActor_mk,
    MulEquiv.symm_apply_apply]

/-- The field witness gives an outer involution in any natural marking. -/
theorem field_quotientActor
    {F K : Type} [Field F] [Field K]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (d : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (t : normalizer (L : Set G))
    (σ : K ≃+* K) (hne : σ ≠ 1) (hsq : σ ^ 2 = 1)
    (hσ : ∀ l : L,
      d (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
        Theory.PSL2.sl2FieldAut σ (d (QuotientGroup.mk' (pCore 2 L) l))) :
    quotientActor e t ^ 2 = 1 ∧ ¬ ∃ g, quotientActor e t = MulAut.conj g := by
  have hd : quotientActor d t = Theory.PSL2.sl2FieldAut σ := by
    ext x
    obtain ⟨q, rfl⟩ := d.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    rw [quotientActor_mk, hσ]
  have hchange := quotientActor_change_field e d t
  rw [hd] at hchange
  constructor
  · apply (MulAut.congr (e.symm.trans d)).injective
    rw [map_pow, hchange, map_one]
    ext x i j
    exact congrArg (fun τ : K ≃+* K => τ (x.val i j)) hsq
  · rintro ⟨g, hg⟩
    rw [hg, MulAut.congr_conj] at hchange
    exact hne (Theory.PSL2.sl2FieldAut_eq_conj_implies_refl σ _ hchange.symm)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L B U : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The inverse coordinates identify the fixed additive subgroup with U. -/
noncomputable def fixedModuleEquiv
    (f : B ≃* Multiplicative (Fin 2 → F))
    (t : normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G)) :
    U ≃* Multiplicative (fixedVectors (vectorActor f t)) where
  toFun u := Multiplicative.ofAdd ⟨(f ⟨u, (hU.le u.property).1⟩).toAdd, by
    change vectorActor f t _ = _
    apply (vectorActor_fixed_iff f t _).mpr
    simpa using (hU.le u.property).2⟩
  invFun v := ⟨f.symm (Multiplicative.ofAdd v.toAdd.val), by
    rw [hU]
    exact ⟨(f.symm _).property, (vectorActor_fixed_iff f t _).mp v.toAdd.property⟩⟩
  left_inv u := by apply Subtype.ext; simp
  right_inv v := by
    apply Multiplicative.ofAdd.injective
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Multiplicative.ofAdd.injective
    apply Subtype.ext
    change (f ((⟨u, (hU.le u.property).1⟩ : B) *
      ⟨v, (hU.le v.property).1⟩)).toAdd = _
    rw [map_mul]
    rfl

omit [Finite F] [CharP F 2] in
/-- The inverse fixed-space coordinates, as an ambient group element. -/
@[simp] theorem fixedModuleEquiv_symm_coe
    (f : B ≃* Multiplicative (Fin 2 → F))
    (t : normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G))
    (v : Multiplicative (fixedVectors (vectorActor f t))) :
    ((fixedModuleEquiv f t hU).symm v : G) =
      (f.symm (Multiplicative.ofAdd (v.toAdd : Fin 2 → F)) : G) := by
  rfl

/-- The literal normalizer of U is the inverse image of the fixed quotient
actors, under the original natural-module marking. -/
theorem mem_normalizer_fixed_iff
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (t : normalizer (L : Set G)) (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G))
    (hi : Function.Involutive (vectorActor f ⟨t, htB⟩))
    (hsq : quotientActor e t ^ 2 = 1)
    (hout : ¬ ∃ g, quotientActor e t = MulAut.conj g)
    (l : L) :
    (l : G) ∈ normalizer (U : Set G) ↔
      quotientActor e t (e (QuotientGroup.mk' (pCore 2 L) l)) =
        e (QuotientGroup.mk' (pCore 2 L) l) := by
  let E := vectorActor f ⟨t, htB⟩
  let a := quotientActor e t
  have he := vectorActor_intertwines e f hf t htB
  have hpres (k : L) :
      (∀ u : G, u ∈ U → (k : G) * u * (k : G)⁻¹ ∈ U) ↔
      a (e (QuotientGroup.mk' (pCore 2 L) k)) =
        e (QuotientGroup.mk' (pCore 2 L) k) := by
    rw [← preserves_fixed_iff a E hi he hsq hout]
    constructor
    · intro hk v hv
      have hvU : (f.symm (Multiplicative.ofAdd v) : G) ∈ U := by
        rw [hU]
        exact ⟨(f.symm _).property, (vectorActor_fixed_iff f ⟨t, htB⟩ v).mp hv⟩
      have hh := hk _ hvU
      have hkf := hf k (f.symm (Multiplicative.ofAdd v))
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hkf
      rw [← hkf, hU] at hh
      exact (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr hh.2
    · intro hk u hu
      let v : B := ⟨u, (hU.le hu).1⟩
      have hv : E (f v).toAdd = (f v).toAdd := by
        apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
        simpa [v] using (hU.le hu).2
      have hh := (vectorActor_fixed_iff f ⟨t, htB⟩ _).mp (hk _ hv)
      rw [← hf k v, hU]
      exact ⟨(f.symm _).property, hh⟩
  constructor
  · intro hl
    apply (hpres l).mp
    intro u hu
    exact (mem_normalizer_iff.mp hl u).mp hu
  · intro hl
    have hli : a (e (QuotientGroup.mk' (pCore 2 L) l⁻¹)) =
        e (QuotientGroup.mk' (pCore 2 L) l⁻¹) := by
      simpa only [map_inv] using congrArg Inv.inv hl
    apply mem_normalizer_iff.mpr
    intro u
    constructor
    · exact (hpres l).mpr hl u
    · intro hu
      have hh := (hpres l⁻¹).mpr hli _ hu
      have hcancel : (l : G)⁻¹ * ((l : G) * u * (l : G)⁻¹) * (l : G) = u := by group
      simpa only [coe_inv, inv_inv, hcancel] using hh

/-- The original normalizer has the fixed-field natural action, with a
surjective actor map and a two-group kernel. -/
theorem fixedNormalizer_marking
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (t : normalizer (L : Set G)) (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G))
    (hi : Function.Involutive (vectorActor f ⟨t, htB⟩))
    (hsq : quotientActor e t ^ 2 = 1)
    (hout : ¬ ∃ g, quotientActor e t = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃ p : (L ⊓ normalizer (U : Set G) : Subgroup G) →*
          Matrix.SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ),
        Function.Surjective p ∧ IsPGroup 2 p.ker ∧
        ∃ fU : U ≃* Multiplicative (Fin 2 → FixedBy.subfield F σ),
          ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
            (fU.symm (Multiplicative.ofAdd ((p l).val.mulVec (fU u).toAdd)) : G) =
              (l : G) * (u : G) * (l : G)⁻¹ := by
  let E := vectorActor f ⟨t, htB⟩
  let a := quotientActor e t
  have he := vectorActor_intertwines e f hf t htB
  obtain ⟨σ, hσ, hσi, ea, ev, hev⟩ := outer_involution_fixed_natural a E hi he hsq hout
  let N := L ⊓ normalizer (U : Set G)
  let q : N →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).comp (inclusion inf_le_left)
  have hq (l : N) : q l ∈ a.fixedSubgroup :=
    (MulAut.mem_fixedSubgroup _ _).mpr
      ((mem_normalizer_fixed_iff e f hf t htB hU hi hsq hout
        (inclusion inf_le_left l)).mp l.property.2)
  let qf : N →* a.fixedSubgroup := q.codRestrict _ hq
  have hqfs : Function.Surjective qf := by
    intro x
    obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) x.val
    change e (QuotientGroup.mk' (pCore 2 L) l) = x.val at hl
    have hlN : (l : G) ∈ normalizer (U : Set G) := by
      apply (mem_normalizer_fixed_iff e f hf t htB hU hi hsq hout l).mpr
      rw [hl]
      exact (MulAut.mem_fixedSubgroup _ _).mp x.property
    exact ⟨⟨l, l.property, hlN⟩, Subtype.ext hl⟩
  let p := ea.toMonoidHom.comp qf
  have hp : Function.Surjective p := ea.surjective.comp hqfs
  have hpk : IsPGroup 2 p.ker := by
    have hk : p.ker = (pCore 2 L).comap (inclusion (show N ≤ L from inf_le_left)) := by
      ext l
      change ea (qf l) = 1 ↔ inclusion inf_le_left l ∈ pCore 2 L
      rw [← ea.map_one, ea.injective.eq_iff]
      change qf l = 1 ↔ _
      rw [Subtype.ext_iff]
      change e (QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left l)) = 1 ↔ _
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff _
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let ffix := fixedModuleEquiv f ⟨t, htB⟩ hU
  let fU := ffix.trans ev.toMultiplicative
  refine ⟨σ, hσ, hσi, p, hp, hpk, fU, ?_⟩
  intro l u
  let v : fixedVectors E := (ffix u).toAdd
  have hv := hev (qf l) v
  have heq : (fU.symm (Multiplicative.ofAdd ((p l).val.mulVec (fU u).toAdd)) : G) =
      (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f ⟨u, (hU.le u.property).1⟩).toAdd)) : G) := by
    change ((ffix.symm (Multiplicative.ofAdd (ev.symm
      ((ea (qf l)).val.mulVec (ev v))))) : G) = _
    rw [← hv, ev.symm_apply_apply]
    rfl
  rw [heq]
  exact hf (inclusion inf_le_left l) ⟨u, (hU.le u.property).1⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] [Finite G] {L B U : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem binary_model_core (hF : 2 < Nat.card F) :
    pCore 2 (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  let S := Matrix.SpecialLinearGroup (Fin 2) F
  let : Group.IsPerfect S :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let : IsSimpleGroup S :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  rcases (inferInstance : (pCore 2 S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hp : IsPGroup 2 S := pCore_isPGroup.of_equiv
      ((MulEquiv.subgroupCongr ht).trans topEquiv)
    let := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable S inferInstance).elim

/-- A surjection with two-group kernel gives the literal natural quotient. -/
theorem natural_of_two_kernel
    {K V : Subgroup G} {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (p : K →* Matrix.SpecialLinearGroup (Fin 2) F) (hp : Function.Surjective p)
    (hk : IsPGroup 2 p.ker) (f : V ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (k : K) (v : V),
      (f.symm (Multiplicative.ofAdd ((p k).val.mulVec (f v).toAdd)) : G) =
        (k : G) * (v : G) * (k : G)⁻¹) : IsNaturalModule K V m := by
  have hsize : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ m from pow_lt_pow_right₀ (by decide) hm)
  have hker := p.comap_pCore_of_ker_isPGroup hp hk
  rw [binary_model_core hsize, MonoidHom.comap_bot] at hker
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p hp)
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, e, f, hf⟩

/-- A natural action of degree greater than one remains the same natural
action on the embedded two-residual, with its own intrinsic two-core. -/
theorem natural_on_two_residual
    {K V : Subgroup G} {m : ℕ} (h : IsNaturalModule K V m) (hm : 1 < m) :
    IsNaturalModule ((pResidual 2 K).map K.subtype) V m := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := h
  let S := Matrix.SpecialLinearGroup (Fin 2) F
  have hsize : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ m from pow_lt_pow_right₀ (by decide) hm)
  let : Group.IsPerfect S :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hsize
  have hres : pResidual 2 S = ⊤ := by
    apply (pResidual_eq_top_iff 2 S).mpr
    intro H hH hq
    let := hH
    by_contra hne
    let : Nontrivial (S ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (S ⧸ H) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
    let := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (S ⧸ H) inferInstance
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have him : (pResidual 2 K).map q = ⊤ :=
    (map_pResidual_of_surjective 2 q hq).trans hres
  let R := (pResidual 2 K).map K.subtype
  have hRK : R ≤ K := map_subtype_le _
  let p := q.comp (inclusion hRK)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨k, hk, hx⟩ := show x ∈ (pResidual 2 K).map q from him ▸ mem_top x
    exact ⟨⟨k, mem_map.mpr ⟨k, hk, rfl⟩⟩, hx⟩
  have hk : IsPGroup 2 p.ker := by
    have heq : p.ker = (pCore 2 K).comap (inclusion hRK) := by
      ext r
      change e (QuotientGroup.mk' (pCore 2 K) (inclusion hRK r)) = 1 ↔ _
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff _
    rw [heq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  exact natural_of_two_kernel hF hm p hp hk f (fun k v => hf (inclusion hRK k) v)

/-- The opening natural-module calculation of source 6.1.14. The same
half-degree applies to the actual fixed space under both its L-normalizer
and the literal embedded two-residual of that normalizer. -/
theorem field_fixedSpace_natural
    {M : Subgroup G} {n : ℕ} (hn : 2 < n)
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    ∃ m : ℕ, n = 2 * m ∧
      IsNaturalModule (L ⊓ normalizer (U : Set G)) U m ∧
      IsNaturalModule (fieldLocalResidual L U) U m := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, d, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := ConjugateFixedSpaces.field_quotientActor e d t σ hσ hσsq hσact
  let E := ConjugateFixedSpaces.vectorActor f ⟨t, htB⟩
  have hi : Function.Involutive E := by
    apply intertwiner_involutive_of_fixed (ConjugateFixedSpaces.quotientActor e t) E
      (ConjugateFixedSpaces.vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hu := u.property
    let v : B := ⟨u, (hU.le hu).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (ConjugateFixedSpaces.vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le hu).2
  obtain ⟨τ, hτ, hτi, p, hp, hk, fU, hfU⟩ :=
    ConjugateFixedSpaces.fixedNormalizer_marking e f hf t htB hU hi hasq haout
  let K₀ := FixedBy.subfield F τ
  let : Fintype K₀ := Fintype.ofFinite K₀
  obtain ⟨m, _, hm⟩ := FiniteField.card K₀ 2
  have hK : Nat.card K₀ = 2 ^ (m : ℕ) := (Nat.card_eq_fintype_card).trans hm
  have hnm : n = 2 * (m : ℕ) := by
    have hc := FiniteField.card_involution_fixed_sq τ hτi hτ
    change Nat.card K₀ ^ 2 = Nat.card F at hc
    rw [hK, ← pow_mul, hF] at hc
    have hh := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
    omega
  have hNU := natural_of_two_kernel hK (by omega) p hp hk fU hfU
  exact ⟨m, hnm, hNU, natural_on_two_residual hNU (by omega)⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
