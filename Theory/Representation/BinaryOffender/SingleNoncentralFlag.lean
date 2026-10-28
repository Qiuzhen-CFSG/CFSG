module

public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Mathlib.GroupTheory.IsPerfect

/-!
# A central cover from one noncentral flag factor

A perfect normal subgroup acting nontrivially on exactly one literal section of
an invariant flag yields its literal commutator subrepresentation as a central
cover of that section.  The construction keeps the original section carrier,
identifies the quotient by the central kernel with it, and proves the cover is
indecomposable on restriction to the perfect subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, B.3.3,
printed p.84, and 13.8.25, printed p.960 (1 March 2004 manuscript).
-/

set_option linter.style.haveILetI false

public section

open Representation
namespace Representation.BinaryOffender
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem central_prefix
    (K : Subgroup H) [Group.IsPerfect K] (c : ℕ → Subrepresentation ρ) (i n : ℕ)
    (hzero : c 0 = ⊥)
    (hcentral : ∀ j < n, j ≠ i → ∀ k ∈ K, ∀ v,
      sectionRepresentation ρ (c j) (c (j + 1)) k v = v)
    (hi : i < n) :
    (c i).toSubmodule ≤ fixedSpace ρ K := by
  exact le_fixedSpace_of_central_flag ρ K c hzero i
    (fun j hj => hcentral j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hi)) (by omega))

omit [FiniteDimensional (ZMod 2) V] in
private theorem commutator_stable_under_normal
    (K : Subgroup H) [K.Normal] :
    (⊤ : Subgroup H) ≤ subspaceStabilizer ρ (subspaceCommutator ρ (⊤ : Submodule (ZMod 2) V) K) := by
  apply subspaceCommutator_invariant_normalizer ρ
  · exact le_subspaceStabilizer ρ ⊤ (by simp)
  · exact (show (⊤ : Subgroup H) ≤ Subgroup.normalizer K from by
      intro h _
      apply Subgroup.mem_normalizer_iff.mpr
      intro k
      constructor
      · intro hk
        exact (inferInstance : K.Normal).conj_mem k hk h
      · intro hk
        have hh := (inferInstance : K.Normal).conj_mem'
          (h * k * h⁻¹) hk h
        simpa [mul_assoc] using hh)

omit [FiniteDimensional (ZMod 2) V] in
private theorem quotient_image_section_trivial
    (U A B : Subrepresentation ρ) (_hUA : U ≤ A) (_hAB : A ≤ B)
    (k : H)
    (htriv : ∀ s, sectionRepresentation ρ A B k s = s) :
    ∀ s, sectionRepresentation U.quotientRepresentation
      (U.quotientImage A) (U.quotientImage B) k s = s := by
  intro s
  apply (sectionRepresentation_trivial_iff U.quotientRepresentation
    (U.quotientImage A) (U.quotientImage B) k).mpr
  intro w hw
  obtain ⟨b, hb, rfl⟩ := hw
  have hdisp := (sectionRepresentation_trivial_iff ρ A B k).mp htriv
    b hb
  refine ⟨ρ k b - b, hdisp, ?_⟩
  rw [Subrepresentation.quotientRepresentation_mk]
  exact (map_sub U.toSubmodule.mkQ (ρ k b) b).symm

omit [FiniteDimensional (ZMod 2) V] in
private theorem central_tail_commutator_le
    (K : Subgroup H) [Group.IsPerfect K]
    (c : ℕ → Subrepresentation ρ) (i n : ℕ)
    (hc : Monotone c) (hstop : c n = ⊤) (hi : i < n)
    (hcentral : ∀ j < n, j ≠ i → ∀ k ∈ K, ∀ v,
      sectionRepresentation ρ (c j) (c (j + 1)) k v = v) :
    subspaceCommutator ρ ⊤ K ≤ (c (i + 1)).toSubmodule := by
  let U := c (i + 1)
  let d : ℕ → Subrepresentation U.quotientRepresentation := fun m =>
    match m with
    | 0 => ⊥
    | m + 1 => U.quotientImage (c (i + 1 + m))
  have hdmono : Monotone d := by
    intro a b hab
    cases a with
    | zero => exact bot_le
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        change (c (i + 1 + a)).toSubmodule.map U.toSubmodule.mkQ ≤
          (c (i + 1 + b)).toSubmodule.map U.toSubmodule.mkQ
        exact Submodule.map_mono (hc (by omega))
  have hdcentral : ∀ j < n - i, ∀ k ∈ K, ∀ v,
      sectionRepresentation U.quotientRepresentation (d j) (d (j + 1)) k v = v := by
    intro j hj k hk
    cases j with
    | zero =>
      intro v
      apply (sectionRepresentation_trivial_iff U.quotientRepresentation (d 0) (d 1) k).mpr
      intro w hw
      have hw0 : w = 0 := by
        change w ∈ (U.quotientImage U).toSubmodule at hw
        have hbot : U.quotientImage U = ⊥ :=
          (Subrepresentation.quotientImage_eq_bot_iff U U).mpr le_rfl
        rw [hbot] at hw
        exact (Submodule.mem_bot (ZMod 2)).mp hw
      subst w
      simp
    | succ j =>
      intro v
      have hidx : i + (j + 1) < n := by omega
      change sectionRepresentation U.quotientRepresentation
        (U.quotientImage (c (i + 1 + j)))
        (U.quotientImage (c (i + 1 + j + 1))) k v = v
      exact quotient_image_section_trivial ρ U (c (i + 1 + j))
        (c (i + 1 + j + 1)) (hc (by omega)) (hc (by omega)) k
        (hcentral (i + 1 + j) (by omega) (by omega) k hk) v
  have htop : d (n - i) = ⊤ := by
    have heq : n - i = (n - i - 1) + 1 := by omega
    rw [heq]
    dsimp [d]
    have hi' : i + 1 + (n - i - 1) = n := by omega
    rw [hi']
    apply (Subrepresentation.quotientImage_eq_top_iff U (c n)).mpr
    rw [hstop]
    exact top_unique le_sup_right
  have hfix := le_fixedSpace_of_central_flag U.quotientRepresentation K d rfl
    (n - i) hdcentral
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, v, hv, rfl⟩
  have hmem : U.toSubmodule.mkQ v ∈ (d (n - i)).toSubmodule := by
    rw [htop]
    trivial
  have hqk := hfix hmem
  have hqk' := hqk ⟨k, hk⟩
  change U.toSubmodule.mkQ (ρ k v) = U.toSubmodule.mkQ v at hqk'
  apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
  change U.toSubmodule.mkQ (ρ k v - v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hqk'


omit [FiniteDimensional (ZMod 2) V] in
private theorem perfect_commutator_eq
    (K : Subgroup H) [K.Normal] [Group.IsPerfect K]
    (J : Subrepresentation ρ)
    (hJ : J.toSubmodule = subspaceCommutator ρ ⊤ K) :
    subspaceCommutator J.toRepresentation ⊤ K = ⊤ := by
  let D := subspaceCommutator ρ J.toSubmodule K
  have hJstab : K ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact J.apply_mem_toSubmodule k hv
  have hDstab : K ≤ subspaceStabilizer ρ D :=
    subspaceCommutator_invariant ρ J.toSubmodule K
  have hDle : D ≤ J.toSubmodule :=
    subspaceCommutator_le_of_invariant ρ hJstab
  let Drep : Subrepresentation (ρ.comp K.subtype) :=
    ⟨D, by
      intro k v hv
      exact (hDstab k.property v).2 hv⟩
  let qρ := Drep.quotientRepresentation
  have hqC : subspaceCommutator qρ ⊤ (⊤ : Subgroup K) ≤ fixedSpace qρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, v, _, rfl⟩
    intro k
    induction v using Submodule.Quotient.induction_on with
    | _ w =>
      change qρ k (qρ x (Drep.toSubmodule.mkQ w) - Drep.toSubmodule.mkQ w) =
        qρ x (Drep.toSubmodule.mkQ w) - Drep.toSubmodule.mkQ w
      rw [map_sub, Subrepresentation.quotientRepresentation_mk,
        Subrepresentation.quotientRepresentation_mk]
      apply (Submodule.Quotient.eq D).mpr
      have hdJ : ρ x.val w - w ∈ J.toSubmodule := by
        rw [hJ]
        exact Submodule.subset_span ⟨x.val, x.property, w, Submodule.mem_top, rfl⟩
      exact Submodule.subset_span
        ⟨k.val, k.val.property, ρ x.val w - w, hdJ, by
          simp only [map_sub, ← Module.End.mul_apply]
          rfl⟩
  have hqfix : (⊤ : Submodule (ZMod 2) (V ⧸ D)) ≤ fixedSpace qρ (⊤ : Subgroup K) :=
    le_fixedSpace_of_commutator_le_fixedSpace qρ (⊤ : Subgroup K) ⊤
      (le_subspaceStabilizer qρ ⊤ (by simp)) hqC
  have hJleD : J.toSubmodule ≤ D := by
    rw [hJ]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, hv, rfl⟩
    have hfix := hqfix (show Drep.toSubmodule.mkQ v ∈ (⊤ : Submodule (ZMod 2) (V ⧸ D)) from by trivial)
    have hfixx := hfix ⟨⟨x, hx⟩, by simp⟩
    change Drep.toSubmodule.mkQ (ρ x v) = Drep.toSubmodule.mkQ v at hfixx
    apply (Submodule.Quotient.mk_eq_zero D).mp
    change Drep.toSubmodule.mkQ (ρ x v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hfixx
  have hD : D = J.toSubmodule := le_antisymm hDle hJleD
  apply Submodule.map_injective_of_injective J.toSubmodule.subtype_injective
  rw [Submodule.map_top, Submodule.range_subtype]
  apply le_antisymm
  · have hmapleD : Submodule.map J.toSubmodule.subtype
        (subspaceCommutator J.toRepresentation ⊤ K) ≤ D := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, v, hv, rfl⟩
      exact Submodule.subset_span ⟨k, hk, v.val, v.property, rfl⟩
    exact hmapleD.trans hDle
  · have hsecond : D ≤ Submodule.map J.toSubmodule.subtype
        (subspaceCommutator J.toRepresentation ⊤ K) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, v, hv, rfl⟩
      have hjd : ρ k v - v ∈ J.toSubmodule :=
        J.toSubmodule.sub_mem (J.apply_mem_toSubmodule k (show v ∈ J.toSubmodule from hv)) hv
      change (ρ k v - v) ∈ Submodule.map J.toSubmodule.subtype
        (subspaceCommutator J.toRepresentation ⊤ K)
      rw [Submodule.mem_map]
      refine ⟨⟨ρ k v - v, hjd⟩, ?_, rfl⟩
      exact Submodule.subset_span ⟨k, hk, ⟨v, hv⟩, by trivial, rfl⟩
    simpa [hD] using hsecond

structure SingleNoncentralFlagWitness
    (K : Subgroup H) (c : ℕ → Subrepresentation ρ) (i n : ℕ) where
  J : Subrepresentation ρ
  J_eq_commutator : J.toSubmodule = subspaceCommutator ρ ⊤ K
  nonzero : J.toSubmodule ≠ ⊥
  map : J.toSubmodule →ₗ[ZMod 2]
    ((c (i + 1)).toSubmodule ⧸
      (sectionLower ρ (c i) (c (i + 1))).toSubmodule)
  map_surjective : Function.Surjective map
  map_equivariant : ∀ h v,
    map (J.toRepresentation h v) =
      sectionRepresentation ρ (c i) (c (i + 1)) h (map v)
  map_kernel_central : map.ker ≤ fixedSpace J.toRepresentation K
  commutator_eq_top : subspaceCommutator J.toRepresentation ⊤ K = ⊤
  quotient_equiv :
    (J.toSubmodule ⧸ map.ker) ≃ₗ[ZMod 2]
      ((c (i + 1)).toSubmodule ⧸
        (sectionLower ρ (c i) (c (i + 1))).toSubmodule)
  quotient_equiv_apply : ∀ v,
    quotient_equiv (map.ker.mkQ v) = map v
  quotient_equiv_equivariant : ∀ h v,
    quotient_equiv (map.ker.mkQ (J.toRepresentation h v)) =
      sectionRepresentation ρ (c i) (c (i + 1)) h
        (quotient_equiv (map.ker.mkQ v))
  indecomposable : ∀ A B : Submodule (ZMod 2) J.toSubmodule,
    K ≤ subspaceStabilizer J.toRepresentation A →
    K ≤ subspaceStabilizer J.toRepresentation B →
    IsCompl A B → A = ⊥ ∨ B = ⊥

private theorem image_eq_bot_or_top
    {K X W : Type*} [Group K]
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K W)
    [IsIrreducible σ]
    {A : Submodule (ZMod 2) X}
    (f : A →ₗ[ZMod 2] W)
    (act : ∀ _k : K, A → A)
    (hf : ∀ k a, f (act k a) =
      σ k (f a)) :
    LinearMap.range f = ⊥ ∨ LinearMap.range f = ⊤ := by
  let R : Subrepresentation σ :=
    ⟨LinearMap.range f, by
      intro k v hv
      obtain ⟨a, ha, rfl⟩ := hv
      rw [LinearMap.mem_range]
      exact ⟨act k a, hf k a⟩⟩
  rcases (inferInstance : IsIrreducible σ).eq_bot_or_eq_top R with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

set_option linter.unusedSectionVars false in
theorem singleNoncentralFlag
    (K : Subgroup H) [K.Normal] [Group.IsPerfect K]
    (c : ℕ → Subrepresentation ρ) (i n : ℕ)
    (hc : Monotone c) (hzero : c 0 = ⊥) (hstop : c n = ⊤)
    (hi : i < n)
    (hcentral : ∀ j < n, j ≠ i → ∀ k ∈ K, ∀ v,
      sectionRepresentation ρ (c j) (c (j + 1)) k v = v)
    (hirr : IsIrreducible
      ((sectionRepresentation ρ (c i) (c (i + 1))).comp K.subtype))
    (hnoncentral : ∃ k ∈ K, ∃ s,
      sectionRepresentation ρ (c i) (c (i + 1)) k s ≠ s) :
    Nonempty (SingleNoncentralFlagWitness ρ K c i n) := by
  let U := c (i + 1)
  have hupper := central_tail_commutator_le ρ K c i n hc hstop hi hcentral
  have hJstab : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ
      (subspaceCommutator ρ (⊤ : Submodule (ZMod 2) V) K) :=
    commutator_stable_under_normal ρ K
  let J : Subrepresentation ρ :=
    ⟨subspaceCommutator ρ (⊤ : Submodule (ZMod 2) V) K, by
      intro h v hv
      exact (hJstab (show h ∈ (⊤ : Subgroup H) from by trivial) v).2 hv⟩
  have hJ_eq : J.toSubmodule = subspaceCommutator ρ ⊤ K := rfl
  have hJU : J.toSubmodule ≤ U.toSubmodule := by
    rw [hJ_eq]
    exact hupper
  let τ := sectionRepresentation ρ (c i) (c (i + 1))
  let p : J.toSubmodule →ₗ[ZMod 2]
      ((c (i + 1)).toSubmodule ⧸
        (sectionLower ρ (c i) (c (i + 1))).toSubmodule) :=
    { toFun := fun v => (sectionLower ρ (c i) (c (i + 1))).toSubmodule.mkQ
        ⟨v, hJU v.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hp_equiv (h : H) (v : J.toSubmodule) :
      p (J.toRepresentation h v) = τ h (p v) := by
    change (sectionLower ρ (c i) (c (i + 1))).toSubmodule.mkQ
        ⟨ρ h v, hJU (J.apply_mem_toSubmodule h v.property)⟩ =
      τ h ((sectionLower ρ (c i) (c (i + 1))).toSubmodule.mkQ
        ⟨v, hJU v.property⟩)
    rw [sectionRepresentation_mk]
    rfl
  have hp_kernel : p.ker ≤ fixedSpace J.toRepresentation K := by
    intro v hv k
    have hv0 : (⟨v, hJU v.property⟩ : U.toSubmodule) ∈
        (sectionLower ρ (c i) (c (i + 1))).toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact hv
    change (v : V) ∈ (c i).toSubmodule at hv0
    have hci := central_prefix ρ K c i n hzero hcentral hi hv0
    apply Subtype.ext
    change ρ k (v : V) = (v : V)
    exact hci ⟨k, k.property⟩
  let τK := τ.comp K.subtype
  let pK : Representation.IntertwiningMap (J.toRepresentation.comp K.subtype) τK :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun k v => hp_equiv k v)
  letI : IsIrreducible τK := hirr
  have hp_surj : Function.Surjective p := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero pK with hs | hz
    · exact hs
    · exfalso
      obtain ⟨k, hk, s, hs⟩ := hnoncentral
      have hp0 : p = 0 := by
        apply LinearMap.ext
        intro v
        have hv := congrArg
          (fun f : Representation.IntertwiningMap (J.toRepresentation.comp K.subtype) τK => f v) hz
        exact hv
      have hkci : ∀ u ∈ U.toSubmodule, ρ k u - u ∈ (c i).toSubmodule := by
        intro u hu
        have hj : ρ k u - u ∈ J.toSubmodule := by
          rw [hJ_eq]
          exact Submodule.subset_span ⟨k, hk, u, by trivial, rfl⟩
        have hpj : p ⟨ρ k u - u, hj⟩ = 0 := by
          rw [hp0]
          rfl
        have hl : (⟨ρ k u - u, hJU hj⟩ : U.toSubmodule) ∈
            (sectionLower ρ (c i) (c (i + 1))).toSubmodule := by
          apply (Submodule.Quotient.mk_eq_zero _).mp
          exact hpj
        change ρ k u - u ∈ (c i).toSubmodule at hl
        exact hl
      have htriv := (sectionRepresentation_trivial_iff ρ (c i) U k).mpr hkci
      exact hs (htriv s)
  have hJne : J.toSubmodule ≠ ⊥ := by
    intro hbot
    obtain ⟨k, hk, s, hs⟩ := hnoncentral
    obtain ⟨v, hv⟩ := hp_surj s
    have hv0 : v = 0 := by
      apply Subtype.ext
      apply (Submodule.mem_bot (ZMod 2)).mp
      rw [← hbot]
      exact v.property
    subst v
    have hs0 : s = 0 := by simpa using hv.symm
    subst s
    apply hs
    simp [hs0]
  have hcomm := perfect_commutator_eq ρ K J hJ_eq
  let N : Subrepresentation J.toRepresentation :=
    ⟨p.ker, by
      intro h v hv
      change p (J.toRepresentation h v) = 0
      rw [hp_equiv, hv, map_zero]⟩
  let qeq : (J.toSubmodule ⧸ p.ker) ≃ₗ[ZMod 2]
      ((c (i + 1)).toSubmodule ⧸
        (sectionLower ρ (c i) (c (i + 1))).toSubmodule) :=
    LinearEquiv.ofBijective (p.ker.liftQ p le_rfl)
      ⟨by
        apply LinearMap.ker_eq_bot.mp
        exact Submodule.ker_liftQ_eq_bot p.ker p le_rfl le_rfl,
        by
          intro y
          obtain ⟨v, hv⟩ := hp_surj y
          exact ⟨p.ker.mkQ v, hv⟩⟩
  have qeq_apply (v : J.toSubmodule) : qeq (p.ker.mkQ v) = p v := rfl
  have qeq_equiv (h : H) (v : J.toSubmodule) :
      qeq (p.ker.mkQ (J.toRepresentation h v)) =
        τ h (qeq (p.ker.mkQ v)) := by
    rw [qeq_apply, qeq_apply, hp_equiv]
  have indecomp : ∀ A B : Submodule (ZMod 2) J.toSubmodule,
      K ≤ subspaceStabilizer J.toRepresentation A →
      K ≤ subspaceStabilizer J.toRepresentation B →
      IsCompl A B → A = ⊥ ∨ B = ⊥ := by
    intro A B hA hB hAB
    let pA : A →ₗ[ZMod 2]
        ((c (i + 1)).toSubmodule ⧸
          (sectionLower ρ (c i) (c (i + 1))).toSubmodule) := p.comp A.subtype
    let pB : B →ₗ[ZMod 2]
        ((c (i + 1)).toSubmodule ⧸
          (sectionLower ρ (c i) (c (i + 1))).toSubmodule) := p.comp B.subtype
    have hpA (k : K) (a : A) :
        pA ⟨J.toRepresentation k.val (A.subtype a), (hA k.property _).2 a.property⟩ =
          τK k (pA a) := by
      change p (J.toRepresentation k.val (A.subtype a)) = τ k.val (p (A.subtype a))
      exact hp_equiv k.val (A.subtype a)
    have hpB (k : K) (b : B) :
        pB ⟨J.toRepresentation k.val (B.subtype b), (hB k.property _).2 b.property⟩ =
          τK k (pB b) := by
      change p (J.toRepresentation k.val (B.subtype b)) = τ k.val (p (B.subtype b))
      exact hp_equiv k.val (B.subtype b)
    have hA' : (⊤ : Subgroup K) ≤
        subspaceStabilizer (J.toRepresentation.comp K.subtype) A := by
      intro k hk
      exact (hA k.property)
    have hB' : (⊤ : Subgroup K) ≤
        subspaceStabilizer (J.toRepresentation.comp K.subtype) B := by
      intro k hk
      exact (hB k.property)
    let actA : ∀ k : K, A → A := fun k a =>
      ⟨J.toRepresentation k.val (A.subtype a), (hA k.property _).2 a.property⟩
    let actB : ∀ k : K, B → B := fun k b =>
      ⟨J.toRepresentation k.val (B.subtype b), (hB k.property _).2 b.property⟩
    obtain hA0 | hAt := image_eq_bot_or_top τK pA actA (by
      intro k a
      simpa [actA] using hpA k a)
    · left
      apply bot_unique
      intro a ha
      have hpa : p (a) = 0 := by
        have := (LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩ : p a ∈ LinearMap.range pA)
        rw [hA0] at this
        exact (Submodule.mem_bot (ZMod 2)).mp this
      have hfix : ∀ k : K, J.toRepresentation k a = a := by
        intro k
        exact hp_kernel hpa k
      have hleB : subspaceCommutator J.toRepresentation ⊤ K ≤ B := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, hk, v, hv, rfl⟩
        obtain ⟨aa, haa, bb, hbb, hvsum⟩ := Submodule.mem_sup.mp (hAB.sup_eq_top.ge hv)
        have hpa' : p aa = 0 := by
          have hmem := (LinearMap.mem_range.mpr ⟨⟨aa, haa⟩, rfl⟩ :
            p aa ∈ LinearMap.range pA)
          rw [hA0] at hmem
          exact (Submodule.mem_bot (ZMod 2)).mp hmem
        have hfix' : J.toRepresentation k aa = aa := by
          exact hp_kernel hpa' ⟨k, hk⟩
        rw [← hvsum, map_add, hfix', add_sub_add_left_eq_sub]
        exact B.sub_mem ((hB hk bb).2 hbb) hbb
      have : a ∈ B := by
        apply hleB
        rw [hcomm]
        trivial
      exact hAB.disjoint.le_bot ⟨ha, this⟩
    · obtain hB0 | hBt := image_eq_bot_or_top τK pB actB (by
        intro k b
        simpa [actB] using hpB k b)
      · right
        apply bot_unique
        intro b hb
        have hpb : p (b) = 0 := by
          have := (LinearMap.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩ : p b ∈ LinearMap.range pB)
          rw [hB0] at this
          exact (Submodule.mem_bot (ZMod 2)).mp this
        have hfix : ∀ k : K, J.toRepresentation k b = b := by
          intro k
          exact hp_kernel hpb k
        have hleA : subspaceCommutator J.toRepresentation ⊤ K ≤ A := by
          apply Submodule.span_le.mpr
          rintro _ ⟨k, hk, v, hv, rfl⟩
          obtain ⟨aa, haa, bb, hbb, hvsum⟩ := Submodule.mem_sup.mp (hAB.sup_eq_top.ge hv)
          have hpb' : p bb = 0 := by
            have hmem := (LinearMap.mem_range.mpr ⟨⟨bb, hbb⟩, rfl⟩ :
              p bb ∈ LinearMap.range pB)
            rw [hB0] at hmem
            exact (Submodule.mem_bot (ZMod 2)).mp hmem
          have hfix' : J.toRepresentation k bb = bb := by
            exact hp_kernel hpb' ⟨k, hk⟩
          rw [← hvsum, map_add, hfix', add_sub_add_right_eq_sub]
          exact A.sub_mem ((hA hk aa).2 haa) haa
        have : b ∈ A := by
          apply hleA
          rw [hcomm]
          trivial
        exact hAB.disjoint.le_bot ⟨this, hb⟩
      · have hAtop : LinearMap.range pA = ⊤ := hAt
        have hBtop : LinearMap.range pB = ⊤ := hBt
        obtain ⟨k, hk, s, hs⟩ := hnoncentral
        have hsrange : s ∈ LinearMap.range pA := by
          rw [hAtop]
          trivial
        obtain ⟨a, hpa⟩ := LinearMap.mem_range.mp hsrange
        have harange : pA a ∈ LinearMap.range pB := by
          rw [hBtop]
          trivial
        obtain ⟨b, hpb⟩ := LinearMap.mem_range.mp harange
        have hker : p (A.subtype a - B.subtype b) = 0 := by
          rw [map_sub]
          change pA a - pB b = 0
          rw [hpb, hpa]
          exact sub_self _
        have hfixed := hp_kernel hker
        have heq (x : K) :
            J.toRepresentation x (A.subtype a) - A.subtype a =
              J.toRepresentation x (B.subtype b) - B.subtype b := by
          have hx := hfixed x
          change J.toRepresentation x (A.subtype a - B.subtype b) =
            A.subtype a - B.subtype b at hx
          rw [map_sub] at hx
          exact sub_eq_sub_iff_sub_eq_sub.mp hx
        have ha_fixed : J.toRepresentation k (A.subtype a) = A.subtype a := by
          have hia := (hA hk _).2 a.property
          have hib := (hB hk _).2 b.property
          have hz : J.toRepresentation k (A.subtype a) - A.subtype a = 0 := by
            apply (Submodule.mem_bot (ZMod 2)).mp
            have hia' := A.sub_mem hia a.property
            have hib' := B.sub_mem hib b.property
            have hib'' : J.toRepresentation k (A.subtype a) - A.subtype a ∈ B := by
              rw [heq ⟨k, hk⟩]
              exact hib'
            exact hAB.disjoint.le_bot ⟨hia', hib''⟩
          exact sub_eq_zero.mp hz
        have := hp_equiv k (A.subtype a)
        change p (A.subtype a) = s at hpa
        rw [ha_fixed, hpa] at this
        exact (hs this.symm).elim
  exact ⟨⟨J, hJ_eq, hJne, p, hp_surj, hp_equiv, hp_kernel, hcomm, qeq,
    qeq_apply, qeq_equiv, indecomp⟩⟩

end Representation.BinaryOffender
