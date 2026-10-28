module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Counting
public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.ExtendScalars
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Tactic

/-!
# Elementary abelian hyperplane decomposition

For an elementary abelian odd-order group acting on a binary vector space,
the dimensions fixed by its hyperplanes, after subtracting the common fixed
dimension, sum to the moving dimension. No faithfulness or nontriviality of
the acting subgroup is required.

Extend scalars to the algebraic closure and decompose into simultaneous
character spaces. The coordinates of an H-fixed vector vanish outside the
characters trivial on H. Every nontrivial character has a cyclic elementary
abelian image of order p, so its kernel is a unique hyperplane. Summing the
independent character dimensions counts each nontrivial weight once; the
trivial weight is exactly the common fixed space. Fixed-space dimensions
are preserved by scalar extension, giving the binary identity.

This is the decomposition input for Aschbacher--Smith, *The Classification
of Quasithin Groups*, G.7.1(3), printed p.347 (PDF p.358). The argument uses
the elementary abelian hypothesis throughout the character-kernel count.
-/

open scoped DirectSum IsMulCommutative TensorProduct
open DirectSum
open Classical

namespace Representation.BinaryCoprimeDegree

private theorem finrank_iSup_of_isInternal
    {E M : Type*} [DivisionRing E] [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Submodule E M) (hA : DirectSum.IsInternal A) :
    Module.finrank E M = ∑ i, Module.finrank E (A i) := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  calc
    Module.finrank E M = Module.finrank E (⨁ i, A i) := e.finrank_eq.symm
    _ = ∑ i, Module.finrank E (A i) := by
      apply Module.finrank_directSum

private theorem diagonal_weight_action
    {E K W : Type*} [Field E] [IsAlgClosed E] [Group K] [IsMulCommutative K]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (sigma : Representation E K W) [Fintype sigma.CharacterWeight]
    [DecidableEq sigma.CharacterWeight]
    (hdec : DirectSum.IsInternal
      (fun chi : sigma.CharacterWeight => sigma.characterWeightSpace chi.val))
    (h : K) :
    let A := fun chi : sigma.CharacterWeight => sigma.characterWeightSpace chi.val
    let hAB : Function.Bijective (DirectSum.coeLinearMap A) := hdec
    let e : (⨁ chi, A chi) ≃ₗ[E] W :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hAB
    let d : (⨁ chi, A chi) →ₗ[E] (⨁ chi, A chi) :=
      DFinsupp.mapRange.linearMap (fun chi : sigma.CharacterWeight =>
        (chi.val h : E) • (LinearMap.id : A chi →ₗ[E] A chi))
    e.symm.toLinearMap.comp ((sigma h).comp e.toLinearMap) = d := by
  dsimp
  let A := fun chi : sigma.CharacterWeight => sigma.characterWeightSpace chi.val
  have hAB : Function.Bijective (DirectSum.coeLinearMap A) := hdec
  let e : (⨁ chi, A chi) ≃ₗ[E] W :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hAB
  let d : (⨁ chi, A chi) →ₗ[E] (⨁ chi, A chi) :=
    DFinsupp.mapRange.linearMap (fun chi : sigma.CharacterWeight =>
      (chi.val h : E) • (LinearMap.id : A chi →ₗ[E] A chi))
  apply DirectSum.linearMap_ext E
  intro chi
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change e.symm (sigma h (e (DirectSum.lof E _ _ chi x))) =
      DFinsupp.mapRange.linearMap (fun chi : sigma.CharacterWeight =>
        (chi.val h : E) • (LinearMap.id : A chi →ₗ[E] A chi))
      (DirectSum.lof E _ (fun chi => A chi) chi x)
  simp only [e, LinearEquiv.ofBijective_apply, DirectSum.coeLinearMap_lof]
  rw [show sigma h (x : W) = (chi.val h : E) • (x : W) from
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp x.property h)]
  rw [map_smul]
  have he : e.symm (x : W) = DirectSum.lof E _ (fun chi => A chi) chi x := by
    apply e.injective
    simp [e, DirectSum.coeLinearMap_lof]
  rw [he]
  change (chi.val h : E) • (DFinsupp.lsingle (M := fun chi : sigma.CharacterWeight => A chi) chi x) =
    DFinsupp.mapRange (fun i z => (i.val h : E) • z) (fun i => by simp)
      (DFinsupp.single (β := fun i : sigma.CharacterWeight => A i) chi x)
  rw [DFinsupp.mapRange_single, DFinsupp.lsingle_apply, ← DFinsupp.single_smul]

set_option linter.style.haveILetI false in
private theorem character_kernel_index
    {p : ℕ} {P E : Type*} [Group P] [Field E] [Fact (Nat.Prime p)]
    [IsElementaryAbelian p P] [Finite P]
    (chi : P →* Eˣ) (hchi : chi ≠ 1) : chi.ker.index = p := by
  letI := (show IsElementaryAbelian p (⊤ : Subgroup P) from {
    toIsMulCommutative := ⟨⟨fun x y => by
      apply Subtype.ext
      exact (IsElementaryAbelian.toIsMulCommutative p).is_comm.comm x.1 y.1⟩⟩
    exponent_dvd_p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p P) x.1 })
  have hrange : Subgroup.map chi (⊤ : Subgroup P) = chi.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, by simp, rfl⟩
  letI := (show IsElementaryAbelian p chi.range from by
    rw [← hrange]
    exact IsElementaryAbelian.map (A := (⊤ : Subgroup P)) chi)
  have hne : chi.range ≠ ⊥ := by
    intro hr
    apply hchi
    exact MonoidHom.range_eq_bot_iff.mp hr
  letI := (Subgroup.nontrivial_iff_ne_bot chi.range).mpr hne
  letI := Finite.of_surjective chi.rangeRestrict chi.rangeRestrict_surjective
  letI := isCyclic_subgroup_units chi.range
  rw [Subgroup.index_ker, (IsCyclic.exponent_eq_card (α := chi.range)).symm]
  exact IsElementaryAbelian.exponent_eq_prime

-- An independent subfamily is an internal direct sum inside its span.
private theorem finrank_selected
    {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι]
    (A : ι → Submodule E W) (hA : iSupIndep A) (q : ι → Prop)
    [DecidablePred q] :
    Module.finrank E ↥(⨆ i, ⨆ (_ : q i), A i) =
      ∑ i, if q i then Module.finrank E (A i) else 0 := by
  classical
  let S : Submodule E W := ⨆ i, ⨆ (_ : q i), A i
  let B : {i // q i} → Submodule E S := fun i => (A i.val).comap S.subtype
  have hB : DirectSum.IsInternal B :=
    DirectSum.isInternal_biSup_submodule_of_iSupIndep {i | q i}
      (hA.comp Subtype.val_injective)
  rw [finrank_iSup_of_isInternal B hB]
  have heq (i : {i // q i}) : Module.finrank E (B i) = Module.finrank E (A i.val) :=
    (Submodule.comapSubtypeEquivOfLe (le_biSup A i.property)).finrank_eq
  simp_rw [heq]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := q) (Finset.univ.filter q) (by simp)
    (fun i => Module.finrank E (A i))).symm

-- Fixed vectors have precisely the coordinates whose characters kill H.
private theorem fixed_finrank_weights
    {E K W : Type*} [Field E] [IsAlgClosed E] [Group K] [IsMulCommutative K]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (sigma : Representation E K W) [Fintype sigma.CharacterWeight]
    (horder : (Nat.card K : E) ≠ 0) (H : Subgroup K) :
    Module.finrank E (Representation.invariants (sigma.comp H.subtype)) =
      ∑ chi : sigma.CharacterWeight,
        if H ≤ chi.val.ker then Module.finrank E (sigma.characterWeightSpace chi.val) else 0 := by
  classical
  let A : sigma.CharacterWeight → Submodule E W :=
    fun chi => sigma.characterWeightSpace chi.val
  have hA : iSupIndep A :=
    (sigma.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hdec : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hA
      (sigma.iSup_characterWeightSpace_eq_top horder)
  let e : (⨁ chi, A chi) ≃ₗ[E] W :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hdec
  have hdiag (h : K) := diagonal_weight_action sigma hdec h
  let I : Submodule E W := (Representation.invariants (sigma.comp H.subtype))
  let q : sigma.CharacterWeight → Prop := fun chi => ∀ h : H, chi.val h = 1
  let S : Submodule E W := ⨆ chi, ⨆ (_ : q chi), A chi
  have hle : I ≤ S := by
    intro v hv
    let f := e.symm v
    have hcoord (chi : sigma.CharacterWeight) (h : H) :
        (chi.val h : E) • f chi = f chi := by
      have hh := congrArg (fun z => z chi) (DFunLike.congr_fun (hdiag h) f)
      have hvh : sigma h v = v := hv h
      change (e.symm (sigma h (e f))) chi =
        (DFinsupp.mapRange (fun i z => (i.val h : E) • z) (fun i => by simp) f) chi at hh
      rw [e.apply_symm_apply, hvh] at hh
      simpa only [DFinsupp.mapRange_apply, f] using hh.symm
    have hfzero (chi : sigma.CharacterWeight) (hn : ¬ q chi) : f chi = 0 := by
      obtain ⟨h, hh⟩ := not_forall.mp hn
      have hc := hcoord chi h
      have hs : (chi.val h : E) - 1 ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        apply hh
        exact Units.ext heq
      have hz : ((chi.val h : E) - 1) • f chi = 0 := by
        rw [sub_smul, hc, one_smul, sub_self]
      exact (smul_eq_zero.mp hz).resolve_left hs
    have hfilter : f.filter q = f := by
      ext chi
      by_cases hh : q chi
      · simp [DFinsupp.filter_apply, hh]
      · simp [DFinsupp.filter_apply, hh, hfzero chi hh]
    rw [Submodule.mem_biSup_iff_exists_dfinsupp q A]
    refine ⟨f, ?_⟩
    rw [hfilter]
    exact e.apply_symm_apply v
  have hIS : I = S := le_antisymm hle (by
    refine iSup_le fun chi => iSup_le fun hc => ?_
    intro v hv h
    have he := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv h.val)
    simpa [hc h] using he)
  change Module.finrank E I = _
  rw [hIS, finrank_selected A hA q]
  apply Finset.sum_congr rfl
  intro chi _
  have hq : q chi ↔ H ≤ chi.val.ker := by
    constructor
    · intro hc h hh
      exact hc ⟨h, hh⟩
    · intro hc h
      exact hc h.property
  simp only [hq, A]

private theorem common_finrank_weights
    {E K W : Type*} [Field E] [IsAlgClosed E] [Group K] [IsMulCommutative K]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (sigma : Representation E K W) [Fintype sigma.CharacterWeight]
    (horder : (Nat.card K : E) ≠ 0) :
    Module.finrank E sigma.invariants =
      ∑ chi : sigma.CharacterWeight,
        if chi.val = 1 then Module.finrank E (sigma.characterWeightSpace chi.val) else 0 := by
  have heq : Representation.invariants (sigma.comp (⊤ : Subgroup K).subtype) =
      sigma.invariants := by
    ext v
    constructor
    · intro hv k
      exact hv ⟨k, Subgroup.mem_top k⟩
    · intro hv k
      exact hv k.val
  rw [← heq, fixed_finrank_weights sigma horder]
  simp only [top_le_iff, MonoidHom.ker_eq_top_iff]

private theorem character_kernel_eq_of_hyperplane
    {p : ℕ} {P E : Type*} [Group P] [Field E] [Fact (Nat.Prime p)]
    [IsElementaryAbelian p P] [Finite P]
    (chi : P →* Eˣ) (hchi : chi ≠ 1) (H : Subgroup P) (hH : H.index = p) :
    H ≤ chi.ker ↔ chi.ker = H := by
  refine ⟨fun hle => ?_, fun heq => heq ▸ le_rfl⟩
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle (Ne.symm hne))
  rw [hH, character_kernel_index (p := p) chi hchi] at hlt
  exact (lt_irrefl p) hlt

set_option linter.style.haveILetI false in
/-- Removing the common fixed dimension leaves one contribution for each
nontrivial character, assigned to its unique hyperplane kernel. -/
public theorem hyperplane_dimension_sum
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (P : Subgroup G) [IsElementaryAbelian p P] :
    hyperplaneDimensionSum rho P p +
        Module.finrank (ZMod 2) (Representation.invariants (rho.comp P.subtype)) =
      Module.finrank (ZMod 2) V := by
  classical
  let E := AlgebraicClosure (ZMod 2)
  let W := E ⊗[ZMod 2] V
  let sigma : Representation E P W :=
    Representation.extendScalars E (rho.comp P.subtype)
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p P).exists_card_eq
    rw [hn]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have horder : (Nat.card P : E) ≠ 0 := by
    rintro hzero
    obtain ⟨k, hk⟩ := hodd
    have hzero' : ((2 * k + 1 : ℕ) : E) = 0 := hk ▸ hzero
    have hdvd : 2 ∣ (2 * k + 1) := (CharP.cast_eq_zero_iff E 2 _).mp hzero'
    omega
  letI := (sigma.characterWeightSpace_independent horder).fintypeNeBotOfFiniteDimensional
  let A : sigma.CharacterWeight → Submodule E W :=
    fun chi => sigma.characterWeightSpace chi.val
  let d : sigma.CharacterWeight → ℕ := fun chi => Module.finrank E (A chi)
  have htotal : Module.finrank E W = ∑ chi, d chi :=
    finrank_iSup_of_isInternal A
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        ((sigma.characterWeightSpace_independent horder).comp Subtype.val_injective)
        (sigma.iSup_characterWeightSpace_eq_top horder))
  have hcommon : Module.finrank (ZMod 2) (Representation.invariants (rho.comp P.subtype)) =
      ∑ chi, if chi.val = 1 then d chi else 0 := by
    rw [← finrank_invariants_extendScalars_eq_of_finite (E := E)]
    exact common_finrank_weights sigma horder
  have hfixed (H : Subgroup P) :
      Module.finrank (ZMod 2) (Representation.invariants (rho.comp (P.subtype.comp H.subtype))) =
        ∑ chi, if H ≤ chi.val.ker then d chi else 0 := by
    rw [← finrank_invariants_extendScalars_eq_of_finite (E := E)]
    exact fixed_finrank_weights sigma horder H
  have hmult (H : Subgroup P) (hH : H ∈ hyperplanes P p) :
      hyperplaneMultiplicity rho P H =
        ∑ chi, if chi.val.ker = H ∧ chi.val ≠ 1 then d chi else 0 := by
    have hidx := (mem_hyperplanes P p H).mp hH
    have hsplit : (∑ chi, if H ≤ chi.val.ker then d chi else 0) =
        (∑ chi, if chi.val.ker = H ∧ chi.val ≠ 1 then d chi else 0) +
          ∑ chi, if chi.val = 1 then d chi else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro chi _
      by_cases hc : chi.val = 1
      · simp [hc]
      · simp [hc, character_kernel_eq_of_hyperplane chi.val hc H hidx]
    rw [hyperplaneMultiplicity, hfixed, hcommon, hsplit, Nat.add_sub_cancel_right]
  have hsum : hyperplaneDimensionSum rho P p =
      ∑ chi, if chi.val ≠ 1 then d chi else 0 := by
    unfold hyperplaneDimensionSum
    rw [Finset.sum_congr rfl hmult, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro chi _
    by_cases hc : chi.val = 1
    · simp [hc]
    · rw [if_pos hc]
      have hk : chi.val.ker ∈ hyperplanes P p :=
        (mem_hyperplanes P p chi.val.ker).mpr (character_kernel_index chi.val hc)
      rw [Finset.sum_eq_single chi.val.ker]
      · simp [hc]
      · intro H _ hne
        simp [Ne.symm hne]
      · exact fun hn => False.elim (hn hk)
  rw [hsum, hcommon, ← Finset.sum_add_distrib]
  calc
    _ = ∑ chi, d chi := by
      apply Finset.sum_congr rfl
      intro chi _
      by_cases hc : chi.val = 1 <;> simp [hc]
    _ = Module.finrank E W := htotal.symm
    _ = Module.finrank (ZMod 2) V := Module.finrank_baseChange

end Representation.BinaryCoprimeDegree
