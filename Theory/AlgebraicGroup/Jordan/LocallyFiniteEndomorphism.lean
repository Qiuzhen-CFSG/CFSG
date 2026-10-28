module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Finiteness.Nilpotent
public import Theory.AlgebraicGroup.Jordan.Linear

universe u v

/-! Jordan components of locally finite endomorphisms. -/

namespace Theory.AlgebraicGroup

open Algebra LinearMap Submodule
open _root_.Module.End

namespace Submodule

variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]

public lemma moduleFinite_sup (P Q : Submodule K M)
    [Module.Finite K P] [Module.Finite K Q] :
    Module.Finite K (show Submodule K M from P ⊔ Q) := by
  let f : (↥P × ↥Q) →ₗ[K] M :=
    P.subtype.comp (LinearMap.fst K P Q) + Q.subtype.comp (LinearMap.snd K P Q)
  have hf : LinearMap.range f = (P ⊔ Q : Submodule K M) := by
    ext x
    constructor
    · rintro ⟨⟨p, q⟩, rfl⟩
      exact Submodule.add_mem_sup p.property q.property
    · intro hx
      rcases Submodule.mem_sup.mp hx with ⟨p, hp, q, hq, hpq⟩
      refine ⟨(⟨p, hp⟩, ⟨q, hq⟩), ?_⟩
      simpa [f] using hpq
  have hfinite : Module.Finite K (LinearMap.range f) := Module.Finite.range f
  exact hf ▸ hfinite

end Submodule

namespace Module.End

variable {K : Type u} [Field K] [PerfectField K]
variable {M : Type v} [AddCommGroup M] [Module K M]

/-- Every vector is contained in a finite-dimensional invariant submodule. -/
@[expose]
public def IsLocallyFinite (T : _root_.Module.End K M) : Prop :=
  ∀ x : M, ∃ P : Submodule K M,
    Module.Finite K P ∧ P ∈ T.invtSubmodule ∧ x ∈ P

namespace IsLocallyFinite

variable {T : _root_.Module.End K M} (hT : IsLocallyFinite T)

public noncomputable def submodule (x : M) : Submodule K M :=
  Classical.choose (hT x)

omit [PerfectField K] in
public lemma finite (x : M) : Module.Finite K (submodule hT x) :=
  (Classical.choose_spec (hT x)).1

omit [PerfectField K] in
public lemma invariant (x : M) : submodule hT x ∈ T.invtSubmodule :=
  (Classical.choose_spec (hT x)).2.1

omit [PerfectField K] in
public lemma mem (x : M) : x ∈ submodule hT x :=
  (Classical.choose_spec (hT x)).2.2

omit [PerfectField K] in
/-- Every finite submodule is contained in a finite-dimensional invariant
submodule for a locally finite endomorphism. -/
public lemma exists_finite_invariant_extension (hT : IsLocallyFinite T)
    (P : Submodule K M) [Module.Finite K P] :
    ∃ Q : Submodule K M,
      Module.Finite K Q ∧ P ≤ Q ∧ Q ∈ T.invtSubmodule := by
  obtain ⟨n, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.Finite.iff_fg.mp (inferInstance : Module.Finite K P))
  let Q : Submodule K M :=
    Finset.univ.sup (fun i : Fin n =>
      Theory.AlgebraicGroup.Module.End.cyclicSubmodule T (s i))
  let : ∀ i : Fin n, Module.Finite K
      (Theory.AlgebraicGroup.Module.End.cyclicSubmodule T (s i)) := fun i => by
    let W : Submodule K M := submodule hT (s i)
    let : Module.Finite K W := finite hT (s i)
    have hle : Theory.AlgebraicGroup.Module.End.cyclicSubmodule T (s i) ≤ W :=
      cyclicSubmodule_le_of_mem
        (invariant hT (s i))
        (mem hT (s i))
    exact Module.Finite.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  let : Module.Finite K Q := inferInstance
  refine ⟨Q, inferInstance, ?_, ?_⟩
  · rw [← hs, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (Finset.le_sup
      (f := fun j : Fin n =>
        Theory.AlgebraicGroup.Module.End.cyclicSubmodule T (s j))
      (Finset.mem_univ i))
        (Theory.AlgebraicGroup.Module.End.mem_cyclicSubmodule T (s i))
  · rw [Module.End.mem_invtSubmodule]
    dsimp [Q]
    refine Finset.sup_le ?_
    intro i hi
    exact
      (Theory.AlgebraicGroup.Module.End.cyclicSubmodule_mem_invtSubmodule T (s i)).trans
        (Submodule.comap_mono
          (Finset.le_sup
            (f := fun j : Fin n =>
              Theory.AlgebraicGroup.Module.End.cyclicSubmodule T (s j)) hi))

omit [PerfectField K] in
/-- Two commuting locally finite endomorphisms admit a common finite-dimensional
invariant extension of every finite submodule. -/
public lemma exists_common_finite_invariant_extension
    {U : _root_.Module.End K M} (hT : IsLocallyFinite T) (hU : IsLocallyFinite U)
    (hcomm : Commute T U) (P : Submodule K M) [Module.Finite K P] :
    ∃ Q : Submodule K M,
      Module.Finite K Q ∧ P ≤ Q ∧
        Q ∈ T.invtSubmodule ∧ Q ∈ U.invtSubmodule := by
  obtain ⟨P', hP'finite, hPP', hTP'⟩ :=
    exists_finite_invariant_extension hT P
  let : Module.Finite K P' := hP'finite
  obtain ⟨n, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.Finite.iff_fg.mp hP'finite)
  let Q : Submodule K M :=
    Finset.univ.sup (fun i : Fin n =>
      Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s i))
  let : ∀ i : Fin n, Module.Finite K
      (Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s i)) := fun i => by
    let W : Submodule K M := submodule hU (s i)
    let : Module.Finite K W := finite hU (s i)
    have hle : Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s i) ≤ W :=
      cyclicSubmodule_le_of_mem
        (invariant hU (s i))
        (mem hU (s i))
    exact Module.Finite.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  let : Module.Finite K Q := inferInstance
  have hP'Q : P' ≤ Q := by
    rw [← hs, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (Finset.le_sup
      (f := fun j : Fin n =>
        Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s j))
      (Finset.mem_univ i))
        (Theory.AlgebraicGroup.Module.End.mem_cyclicSubmodule U (s i))
  have hUQ : Q ∈ U.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    dsimp [Q]
    refine Finset.sup_le ?_
    intro i hi
    exact
      (Theory.AlgebraicGroup.Module.End.cyclicSubmodule_mem_invtSubmodule U (s i)).trans
        (Submodule.comap_mono
          (Finset.le_sup
            (f := fun j : Fin n =>
              Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s j)) hi))
  have hfun : Function.Commute (fun x : M => T x) (fun x : M => U x) := by
    intro x
    exact LinearMap.congr_fun hcomm.eq x
  have hTQ : Q ∈ T.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    dsimp [Q]
    refine Finset.sup_le ?_
    intro i hi
    change Theory.AlgebraicGroup.Module.End.cyclicSubmodule U (s i) ≤
      Submodule.comap T Q
    rw [Theory.AlgebraicGroup.Module.End.cyclicSubmodule, Submodule.span_le]
    rintro y ⟨m, rfl⟩
    change T (((fun x : M => U x)^[m]) (s i)) ∈ Q
    rw [(hfun.iterate_right m).eq]
    have hsiP' : s i ∈ P' := by
      rw [← hs]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hTsiQ : T (s i) ∈ Q := hP'Q (hTP' hsiP')
    induction m with
    | zero => simpa using hTsiQ
    | succ m ih =>
        have h := hUQ ih
        change U (((fun x : M => U x)^[m]) (T (s i))) ∈ Q at h
        rw [Function.iterate_succ_apply']
        exact h
  exact ⟨Q, inferInstance, hPP'.trans hP'Q, hTQ, hUQ⟩

omit [PerfectField K] in
/-- The product of commuting locally finite endomorphisms is locally finite. -/
public lemma mul_of_commute {U : _root_.Module.End K M}
    (hT : IsLocallyFinite T) (hU : IsLocallyFinite U)
    (hcomm : Commute T U) : IsLocallyFinite (T * U) := by
  intro x
  let P : Submodule K M := submodule hT x
  let : Module.Finite K P := finite hT x
  obtain ⟨Q, hQfinite, hPQ, hTQ, hUQ⟩ :=
    exists_common_finite_invariant_extension hT hU hcomm P
  refine ⟨Q, hQfinite, ?_, hPQ (mem hT x)⟩
  intro y hy
  change (T * U) y ∈ Q
  rw [Module.End.mul_apply]
  exact hTQ (hUQ hy)

public noncomputable def semisimpleValue (x : M) : M := by
  let : Module.Finite K (submodule hT x) := finite hT x
  exact (submodule hT x).subtype
    ((invariantJordanDecomposition T (submodule hT x) (invariant hT x)).semisimplePart
      ⟨x, mem hT x⟩)

public lemma semisimpleValue_eq (P : Submodule K M) (hP : P ∈ T.invtSubmodule)
    [Module.Finite K P] (x : M) (hx : x ∈ P) :
    semisimpleValue hT x =
      P.subtype ((invariantJordanDecomposition T P hP).semisimplePart ⟨x, hx⟩) := by
  let Q : Submodule K M := submodule hT x ⊔ P
  let : Module.Finite K (submodule hT x) := finite hT x
  let : Module.Finite K Q := Submodule.moduleFinite_sup (submodule hT x) P
  have hQ : Q ∈ T.invtSubmodule :=
    Module.End.invtSubmodule.sup_mem (invariant hT x) hP
  have hleft := invariantJordanDecomposition_semisimple_mono_apply
    T (submodule hT x) Q (invariant hT x) hQ
      (show submodule hT x ≤ Q from le_sup_left) x (mem hT x)
  have hright := invariantJordanDecomposition_semisimple_mono_apply
    T P Q hP hQ (show P ≤ Q from le_sup_right) x hx
  exact hleft.trans hright.symm

@[expose]
public noncomputable def semisimplePart : _root_.Module.End K M where
  toFun := semisimpleValue hT
  map_add' := by
    intro x y
    let P : Submodule K M := submodule hT x ⊔ submodule hT y
    let : Module.Finite K (submodule hT x) := finite hT x
    let : Module.Finite K (submodule hT y) := finite hT y
    let : Module.Finite K P := Submodule.moduleFinite_sup _ _
    have hP : P ∈ T.invtSubmodule :=
      Module.End.invtSubmodule.sup_mem (invariant hT x) (invariant hT y)
    have hxP : x ∈ P := Submodule.mem_sup_left (mem hT x)
    have hyP : y ∈ P := Submodule.mem_sup_right (mem hT y)
    have hxyP : x + y ∈ P := P.add_mem hxP hyP
    rw [semisimpleValue_eq hT P hP (x + y) hxyP,
      semisimpleValue_eq hT P hP x hxP,
      semisimpleValue_eq hT P hP y hyP]
    exact congrArg Subtype.val
      (map_add (invariantJordanDecomposition T P hP).semisimplePart
        (⟨x, hxP⟩ : P) (⟨y, hyP⟩ : P))
  map_smul' := by
    intro c x
    let P : Submodule K M := submodule hT x
    let : Module.Finite K P := finite hT x
    have hP : P ∈ T.invtSubmodule := invariant hT x
    have hxP : x ∈ P := mem hT x
    have hcxP : c • x ∈ P := P.smul_mem c hxP
    rw [semisimpleValue_eq hT P hP (c • x) hcxP,
      semisimpleValue_eq hT P hP x hxP]
    exact congrArg Subtype.val
      (map_smul (invariantJordanDecomposition T P hP).semisimplePart c
        (⟨x, hxP⟩ : P))

public lemma semisimplePart_apply (x : M) :
    hT.semisimplePart x = semisimpleValue hT x := by rfl

public lemma semisimplePart_mem_invtSubmodule (P : Submodule K M)
    (hP : P ∈ T.invtSubmodule) [Module.Finite K P] :
    P ∈ hT.semisimplePart.invtSubmodule := by
  intro x hx
  change hT.semisimplePart x ∈ P
  rw [semisimplePart_apply hT, semisimpleValue_eq hT P hP x hx]
  exact Subtype.property _

public lemma semisimplePart_restrict (P : Submodule K M)
    (hP : P ∈ T.invtSubmodule) [Module.Finite K P] :
    hT.semisimplePart.restrict (hT.semisimplePart_mem_invtSubmodule P hP) =
      (invariantJordanDecomposition T P hP).semisimplePart := by
  ext x
  exact semisimpleValue_eq hT P hP x x.property

public lemma semisimplePart_isFinitelySemisimple :
    hT.semisimplePart.IsFinitelySemisimple := by
  intro P hP hfinite
  let : Module.Finite K P := hfinite
  obtain ⟨n, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.Finite.iff_fg.mp hfinite)
  let Q : Submodule K M :=
    Finset.univ.sup (fun i : Fin n => submodule hT (s i))
  let : ∀ i : Fin n, Module.Finite K (submodule hT (s i)) :=
    fun i => finite hT (s i)
  let : Module.Finite K Q := inferInstance
  have hQ : Q ∈ T.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    dsimp [Q]
    refine Finset.sup_le ?_
    intro i hi
    exact (invariant hT (s i)).trans
      (Submodule.comap_mono
        (Finset.le_sup (f := fun j : Fin n => submodule hT (s j)) hi))
  have hPQ : P ≤ Q := by
    rw [← hs, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (Finset.le_sup (f := fun j : Fin n => submodule hT (s j))
      (Finset.mem_univ i)) (mem hT (s i))
  have hSQ : Q ∈ hT.semisimplePart.invtSubmodule :=
    hT.semisimplePart_mem_invtSubmodule Q hQ
  let S_Q : _root_.Module.End K Q := hT.semisimplePart.restrict hSQ
  have hsQ : Module.End.IsSemisimple S_Q := by
    change Module.End.IsSemisimple
      (hT.semisimplePart.restrict hSQ : _root_.Module.End K Q)
    rw [semisimplePart_restrict hT Q hQ]
    exact (invariantJordanDecomposition T Q hQ).semisimple
  let P' : Submodule K Q := P.comap Q.subtype
  have hP' : P' ∈ S_Q.invtSubmodule := by
    intro x hx
    change hT.semisimplePart x.1 ∈ P
    exact hP hx
  have hsP' : Module.End.IsSemisimple
      (LinearMap.restrict S_Q hP' : _root_.Module.End K P') :=
    hsQ.restrict hP'
  let e : P' ≃ₗ[K] P := Submodule.comapSubtypeEquivOfLe hPQ
  have he : e.toLinearMap.comp
        (LinearMap.restrict S_Q hP' : _root_.Module.End K P') =
      (hT.semisimplePart.restrict hP).comp e.toLinearMap := by
    ext x
    rfl
  exact (e.isSemisimple_iff
    (LinearMap.restrict S_Q hP' : _root_.Module.End K P')
    (hT.semisimplePart.restrict hP) he).mp hsP'

public lemma semisimplePart_commute : Commute T hT.semisimplePart := by
  change T.comp hT.semisimplePart = hT.semisimplePart.comp T
  apply LinearMap.ext
  intro x
  let P : Submodule K M := submodule hT x
  let : Module.Finite K P := finite hT x
  have hP : P ∈ T.invtSubmodule := invariant hT x
  let d := invariantJordanDecomposition T P hP
  have hcomm := d.toJordanPair.commute_semisimplePart
  change (T.restrict hP).comp d.semisimplePart =
    d.semisimplePart.comp (T.restrict hP) at hcomm
  have hx := LinearMap.congr_fun hcomm (⟨x, mem hT x⟩ : P)
  have hSx := semisimpleValue_eq hT P hP x (mem hT x)
  change T (semisimpleValue hT x) = semisimpleValue hT (T x)
  rw [hSx]
  have hTxP : T x ∈ P := hP (mem hT x)
  rw [semisimpleValue_eq hT P hP (T x) hTxP]
  exact congrArg Subtype.val hx

public lemma semisimplePart_injective (hTin : Function.Injective T) :
    Function.Injective hT.semisimplePart := by
  intro x y hxy
  have hz : hT.semisimplePart (x - y) = 0 := by
    simpa using sub_eq_zero.mpr hxy
  let P : Submodule K M := submodule hT (x - y)
  let : Module.Finite K P := finite hT (x - y)
  have hP : P ∈ T.invtSubmodule := invariant hT (x - y)
  let d := invariantJordanDecomposition T P hP
  have hTPinj : Function.Injective (T.restrict hP : _root_.Module.End K P) := by
    intro a b hab
    apply Subtype.ext
    exact hTin (congrArg Subtype.val hab)
  have hdSinj : Function.Injective d.semisimplePart :=
    d.toJordanPair.semisimplePart_injective hTPinj
  have hlocal : d.semisimplePart (⟨x - y, mem hT (x - y)⟩ : P) = 0 := by
    have hvalue := semisimpleValue_eq hT P hP (x - y) (mem hT (x - y))
    have hv0 : semisimpleValue hT (x - y) = 0 := by
      simpa [semisimplePart_apply] using hz
    apply Subtype.ext
    exact hvalue.symm.trans hv0
  have hxy0 : x - y = 0 := by
    have := hdSinj (hlocal.trans (map_zero d.semisimplePart).symm)
    exact congrArg Subtype.val this
  exact sub_eq_zero.mp hxy0

public lemma semisimplePart_surjective (hTin : Function.Injective T) :
    Function.Surjective hT.semisimplePart := by
  intro y
  let P : Submodule K M := submodule hT y
  let : Module.Finite K P := finite hT y
  have hP : P ∈ T.invtSubmodule := invariant hT y
  let d := invariantJordanDecomposition T P hP
  have hTPinj : Function.Injective (T.restrict hP : _root_.Module.End K P) := by
    intro a b hab
    apply Subtype.ext
    exact hTin (congrArg Subtype.val hab)
  have hdSinj : Function.Injective d.semisimplePart :=
    d.toJordanPair.semisimplePart_injective hTPinj
  have hdSsurj : Function.Surjective d.semisimplePart :=
    LinearMap.injective_iff_surjective.mp hdSinj
  rcases hdSsurj (⟨y, mem hT y⟩ : P) with ⟨x, hx⟩
  refine ⟨x.1, ?_⟩
  rw [semisimplePart_apply, semisimpleValue_eq hT P hP x.1 x.2]
  exact congrArg Subtype.val hx

public noncomputable def semisimpleEquiv (hTin : Function.Injective T) : M ≃ₗ[K] M :=
  LinearEquiv.ofBijective hT.semisimplePart
    ⟨hT.semisimplePart_injective hTin, semisimplePart_surjective hT hTin⟩

public noncomputable def unipotentPart (hTin : Function.Injective T) : _root_.Module.End K M :=
  (hT.semisimpleEquiv hTin).symm.toLinearMap.comp T

public lemma semisimplePart_comp_unipotentPart (hTin : Function.Injective T) :
    hT.semisimplePart.comp (hT.unipotentPart hTin) = T := by
  ext x
  change (hT.semisimpleEquiv hTin)
      ((hT.semisimpleEquiv hTin).symm (T x)) = T x
  exact (hT.semisimpleEquiv hTin).apply_symm_apply (T x)

public lemma unipotentPart_comp_semisimplePart (hTin : Function.Injective T) :
    (hT.unipotentPart hTin).comp hT.semisimplePart = T := by
  ext x
  change (hT.semisimpleEquiv hTin).symm (T (hT.semisimplePart x)) = T x
  have hcomm := hT.semisimplePart_commute
  change T.comp hT.semisimplePart = hT.semisimplePart.comp T at hcomm
  have hcommx : T (hT.semisimplePart x) = hT.semisimplePart (T x) := by
    simpa using LinearMap.congr_fun hcomm x
  rw [hcommx]
  change (hT.semisimpleEquiv hTin).symm
      ((hT.semisimpleEquiv hTin) (T x)) = T x
  exact (hT.semisimpleEquiv hTin).symm_apply_apply (T x)

public lemma semisimplePart_commute_unipotentPart (hTin : Function.Injective T) :
    Commute hT.semisimplePart (hT.unipotentPart hTin) := by
  change hT.semisimplePart.comp (hT.unipotentPart hTin) =
    (hT.unipotentPart hTin).comp hT.semisimplePart
  rw [hT.semisimplePart_comp_unipotentPart hTin,
    unipotentPart_comp_semisimplePart hT hTin]

public lemma semisimpleEquiv_symm_mem_invtSubmodule (hTin : Function.Injective T)
    (P : Submodule K M) (hP : P ∈ T.invtSubmodule) [Module.Finite K P] :
    P ∈ Module.End.invtSubmodule
      ((hT.semisimpleEquiv hTin).symm.toLinearMap : _root_.Module.End K M) := by
  intro x hx
  let d := invariantJordanDecomposition T P hP
  have hTPinj : Function.Injective (T.restrict hP : _root_.Module.End K P) := by
    intro a b hab
    apply Subtype.ext
    exact hTin (congrArg Subtype.val hab)
  have hdSinj : Function.Injective d.semisimplePart :=
    d.toJordanPair.semisimplePart_injective hTPinj
  have hdSsurj : Function.Surjective d.semisimplePart :=
    LinearMap.injective_iff_surjective.mp hdSinj
  rcases hdSsurj (⟨x, hx⟩ : P) with ⟨y, hy⟩
  have hglobal : hT.semisimplePart y.1 = x := by
    rw [semisimplePart_apply, semisimpleValue_eq hT P hP y.1 y.2]
    exact congrArg Subtype.val hy
  have hinv : (hT.semisimpleEquiv hTin).symm x = y.1 := by
    apply (hT.semisimpleEquiv hTin).symm_apply_eq.mpr
    exact hglobal.symm
  change (hT.semisimpleEquiv hTin).symm x ∈ P
  rw [hinv]
  exact y.2

public lemma unipotentPart_mem_invtSubmodule (hTin : Function.Injective T)
    (P : Submodule K M) (hP : P ∈ T.invtSubmodule) [Module.Finite K P] :
    P ∈ (hT.unipotentPart hTin).invtSubmodule := by
  intro x hx
  exact semisimpleEquiv_symm_mem_invtSubmodule hT hTin P hP (hP hx)

omit [PerfectField K] in
public lemma restrict_injective (hTin : Function.Injective T)
    (P : Submodule K M) (hP : P ∈ T.invtSubmodule) :
    Function.Injective (T.restrict hP : _root_.Module.End K P) := by
  intro a b hab
  apply Subtype.ext
  exact hTin (congrArg Subtype.val hab)

public lemma unipotentPart_restrict (hTin : Function.Injective T)
    (P : Submodule K M) (hP : P ∈ T.invtSubmodule) [Module.Finite K P] :
    (hT.unipotentPart hTin).restrict
        (hT.unipotentPart_mem_invtSubmodule hTin P hP) =
      (invariantJordanDecomposition T P hP).toJordanPair.unipotentPart
        (restrict_injective hTin P hP) := by
  let d := invariantJordanDecomposition T P hP
  let hTPinj : Function.Injective (T.restrict hP : _root_.Module.End K P) :=
    restrict_injective hTin P hP
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply hT.semisimplePart_injective hTin
  calc
    hT.semisimplePart
        (((hT.unipotentPart hTin).restrict
          (hT.unipotentPart_mem_invtSubmodule hTin P hP)) x).1 =
        T x.1 :=
      LinearMap.congr_fun (hT.semisimplePart_comp_unipotentPart hTin) x.1
    _ = ((T.restrict hP) x).1 := rfl
    _ = (d.toJordanPair.semisimplePart
        ((d.toJordanPair.unipotentPart hTPinj) x)).1 :=
      congrArg Subtype.val
        (LinearMap.congr_fun
          (d.toJordanPair.semisimple_comp_unipotentPart hTPinj) x).symm
    _ = hT.semisimplePart
        ((d.toJordanPair.unipotentPart hTPinj) x).1 := by
      symm
      rw [semisimplePart_apply hT]
      change semisimpleValue hT
          ((d.toJordanPair.unipotentPart hTPinj) x).1 =
        P.subtype ((invariantJordanDecomposition T P hP).semisimplePart
          ⟨((d.toJordanPair.unipotentPart hTPinj) x).1,
            ((d.toJordanPair.unipotentPart hTPinj) x).2⟩)
      exact semisimpleValue_eq hT P hP
        ((d.toJordanPair.unipotentPart hTPinj) x).1
        ((d.toJordanPair.unipotentPart hTPinj) x).2

public lemma unipotentPart_isLocallyUnipotent (hTin : Function.Injective T) :
    ∀ x : M, ∃ n : ℕ,
      (((hT.unipotentPart hTin - 1 : _root_.Module.End K M))^[n]) x = 0 := by
  intro x
  let P : Submodule K M := submodule hT x
  let : Module.Finite K P := finite hT x
  have hP : P ∈ T.invtSubmodule := invariant hT x
  have hUP := hT.unipotentPart_mem_invtSubmodule hTin P hP
  have hWP : P ∈ (hT.unipotentPart hTin - 1 : _root_.Module.End K M).invtSubmodule := by
    intro y hy
    exact P.sub_mem (hUP hy) hy
  let d := invariantJordanDecomposition T P hP
  let hTPinj : Function.Injective (T.restrict hP : _root_.Module.End K P) :=
    restrict_injective hTin P hP
  have hrestrict :
      (hT.unipotentPart hTin - 1 : _root_.Module.End K M).restrict hWP =
        d.toJordanPair.unipotentPart hTPinj - 1 := by
    ext y
    have hU := LinearMap.congr_fun (unipotentPart_restrict hT hTin P hP) y
    have hUv := congrArg Subtype.val hU
    change hT.unipotentPart hTin y.1 =
      (d.toJordanPair.unipotentPart hTPinj y : P) at hUv
    change (hT.unipotentPart hTin y.1 - y.1) =
      (d.toJordanPair.unipotentPart hTPinj y : P) - y
    rw [hUv]
  rcases d.toJordanPair.unipotentPart_isUnipotent hTPinj with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← Module.End.pow_apply]
  have hzero :
      (((hT.unipotentPart hTin - 1 : _root_.Module.End K M).restrict hWP) ^ n)
        (⟨x, mem hT x⟩ : P) = 0 := by
    rw [hrestrict, hn]
    simp
  have hpow := Module.End.pow_restrict n hWP
  have hval := congrArg Subtype.val hzero
  rw [hpow] at hval
  exact hval

/-- A commuting locally finite multiplicative Jordan factorization has the
canonical global semisimple factor. -/
public lemma semisimplePart_eq_of_multiplicativeJordan
    {S U : _root_.Module.End K M} (hT : IsLocallyFinite T) (hS : IsLocallyFinite S)
    (hU : IsLocallyFinite U) (hTin : Function.Injective T)
    (hSsem : S.IsFinitelySemisimple)
    (hUunip : ∀ x : M, ∃ n : ℕ, (((U - 1 : _root_.Module.End K M))^[n]) x = 0)
    (hcomm : Commute S U) (hmul : T = S * U) :
    hT.semisimplePart = S := by
  apply LinearMap.ext
  intro x
  let P : Submodule K M := submodule hT x
  let : Module.Finite K P := finite hT x
  obtain ⟨Q, hQfinite, hPQ, hSQ, hUQ⟩ :=
    exists_common_finite_invariant_extension hS hU hcomm P
  let : Module.Finite K Q := hQfinite
  have hTQ : Q ∈ T.invtSubmodule := by
    intro y hy
    change T y ∈ Q
    rw [hmul, Module.End.mul_apply]
    exact hSQ (hUQ hy)
  let TQ : _root_.Module.End K Q := T.restrict hTQ
  let SQ : _root_.Module.End K Q := S.restrict hSQ
  let UQ : _root_.Module.End K Q := U.restrict hUQ
  have hUsubQ : ∀ y ∈ Q, (U - 1 : _root_.Module.End K M) y ∈ Q := by
    intro y hy
    exact Q.sub_mem (hUQ hy) hy
  have hUQsub : UQ - 1 = (U - 1 : _root_.Module.End K M).restrict hUsubQ := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rfl
  have hUQnil : IsNilpotent (UQ - 1) := by
    rw [Module.End.isNilpotent_iff_of_finite]
    intro y
    obtain ⟨n, hn⟩ := hUunip y.1
    have hn' : ((U - 1 : _root_.Module.End K M) ^ n) y.1 = 0 := by
      rw [Module.End.pow_apply]
      exact hn
    refine ⟨n, ?_⟩
    rw [hUQsub, Module.End.pow_restrict]
    apply Subtype.ext
    simpa using hn'
  have hcommQ : Commute SQ UQ := by
    change SQ * UQ = UQ * SQ
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun hcomm.eq y.1
  have hmulQ : TQ = SQ * UQ := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun hmul y.1
  let e : MultiplicativeJordanPair TQ := {
    semisimplePart := SQ
    unipotentPart := UQ
    semisimple := hSsem Q hSQ hQfinite
    unipotent := hUQnil
    commute := hcommQ
    eq_mul := hmulQ
  }
  let hTQinj : Function.Injective TQ :=
    restrict_injective hTin Q hTQ
  let d : MultiplicativeJordanPair TQ :=
    (invariantJordanDecomposition T Q hTQ).toJordanPair.toMultiplicativeJordanPair
      hTQinj
  have hunique : d.semisimplePart = e.semisimplePart :=
    d.semisimplePart_unique e
  have hxQ : x ∈ Q := hPQ (mem hT x)
  have hcanonical := LinearMap.congr_fun
    (semisimplePart_restrict hT Q hTQ) (⟨x, hxQ⟩ : Q)
  have hunique_x := LinearMap.congr_fun hunique (⟨x, hxQ⟩ : Q)
  have hcanonical_val := congrArg Subtype.val hcanonical
  have hunique_val := congrArg Subtype.val hunique_x
  change hT.semisimplePart x = S x
  calc
    hT.semisimplePart x =
        ((invariantJordanDecomposition T Q hTQ).semisimplePart
          (⟨x, hxQ⟩ : Q)).1 := hcanonical_val
    _ = S x := by
      change ((invariantJordanDecomposition T Q hTQ).semisimplePart
        (⟨x, hxQ⟩ : Q)).1 = S x at hunique_val
      exact hunique_val

variable [IsAlgClosed K]

public lemma semisimplePart_semiconj
    {N : Type*} [AddCommGroup N] [Module K N]
    {U : _root_.Module.End K N} (hU : IsLocallyFinite U)
    (L : M →ₗ[K] N) (hTU : L.comp T = U.comp L) :
    L.comp hT.semisimplePart = hU.semisimplePart.comp L := by
  apply LinearMap.ext
  intro x
  let P : Submodule K M := submodule hT x
  let : Module.Finite K P := finite hT x
  have hP : P ∈ T.invtSubmodule := invariant hT x
  let LP : P →ₗ[K] N := L.comp P.subtype
  let R : Submodule K N := LinearMap.range LP
  let : Module.Finite K R := Module.Finite.range LP
  have hR : R ∈ U.invtSubmodule := by
    rintro y ⟨z, rfl⟩
    refine ⟨(T.restrict hP) z, ?_⟩
    exact LinearMap.congr_fun hTU z.1
  let LR : P →ₗ[K] R := LP.rangeRestrict
  have hlocal : LR.comp (T.restrict hP) =
      (U.restrict (p := R) (q := R) hR).comp LR := by
    ext z
    change L (T z.1) = U (L z.1)
    exact LinearMap.congr_fun hTU z.1
  let dP := invariantJordanDecomposition T P hP
  let dR := invariantJordanDecomposition U R hR
  have hSlocal := dP.toJordanPair.semiconj dR.toJordanPair LR hlocal
  have hxS := semisimpleValue_eq hT P hP x (mem hT x)
  have hLxR : L x ∈ R := ⟨(⟨x, mem hT x⟩ : P), rfl⟩
  have hLxS := semisimpleValue_eq hU R hR (L x) hLxR
  change L (semisimpleValue hT x) = semisimpleValue hU (L x)
  rw [hxS, hLxS]
  exact congrArg Subtype.val
      (LinearMap.congr_fun hSlocal (⟨x, mem hT x⟩ : P))

variable {T U : _root_.Module.End K M}

omit [IsAlgClosed K] in
/-- The product of commuting locally finite, finitely semisimple endomorphisms
is finitely semisimple. -/
public lemma _root_.Theory.AlgebraicGroup.Module.End.IsFinitelySemisimple.mul_of_commute
    (hTloc : IsLocallyFinite T) (hUloc : IsLocallyFinite U)
    (hTsem : T.IsFinitelySemisimple) (hUsem : U.IsFinitelySemisimple)
    (hcomm : Commute T U) : (T * U).IsFinitelySemisimple := by
  intro P hP hPfinite
  let : Module.Finite K P := hPfinite
  obtain ⟨Q, hQfinite, hPQ, hTQ, hUQ⟩ :=
    hTloc.exists_common_finite_invariant_extension hUloc hcomm P
  let : Module.Finite K Q := hQfinite
  have hTUQ : Q ∈ (T * U).invtSubmodule := by
    intro x hx
    change (T * U) x ∈ Q
    rw [Module.End.mul_apply]
    exact hTQ (hUQ hx)
  let TQ : _root_.Module.End K Q := T.restrict hTQ
  let UQ : _root_.Module.End K Q := U.restrict hUQ
  let VQ : _root_.Module.End K Q := (T * U).restrict hTUQ
  have hcommQ : Commute TQ UQ := by
    change TQ * UQ = UQ * TQ
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hcomm.eq x.1
  have hprodQ : TQ * UQ = VQ := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hsemQ : Module.End.IsSemisimple VQ := by
    rw [← hprodQ]
    exact Module.End.IsSemisimple.mul_of_commute hcommQ
      (hTsem Q hTQ hQfinite) (hUsem Q hUQ hQfinite)
  let P' : Submodule K Q := P.comap Q.subtype
  have hP' : P' ∈ VQ.invtSubmodule := by
    intro x hx
    change (T * U) x.1 ∈ P
    exact hP hx
  have hsemP' : Module.End.IsSemisimple
      (LinearMap.restrict VQ hP' : _root_.Module.End K P') :=
    hsemQ.restrict hP'
  let e : P' ≃ₗ[K] P := Submodule.comapSubtypeEquivOfLe hPQ
  have he : e.toLinearMap.comp
        (LinearMap.restrict VQ hP' : _root_.Module.End K P') =
      ((T * U).restrict hP).comp e.toLinearMap := by
    ext x
    rfl
  exact (e.isSemisimple_iff
    (LinearMap.restrict VQ hP')
    ((T * U).restrict hP) he).mp hsemP'

variable {K : Type u} [Field K] [PerfectField K]
variable {A : Type v} [Ring A] [Algebra K A]
variable {T : _root_.Module.End K A} (hT : IsLocallyFinite T)

public lemma semisimplePart_one (hOne : T 1 = 1) : hT.semisimplePart 1 = 1 := by
  let P : Submodule K A := submodule hT 1
  let : Module.Finite K P := finite hT 1
  have hP : P ∈ T.invtSubmodule := invariant hT 1
  let d := invariantJordanDecomposition T P hP
  let xP : P := ⟨1, mem hT 1⟩
  have hx : xP ∈ Module.End.maxGenEigenspace
      (T.restrict (p := P) (q := P) hP : _root_.Module.End K P) 1 := by
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    simp only [pow_one, LinearMap.sub_apply, one_apply, one_smul]
    apply Subtype.ext
    change T 1 - 1 = 0
    rw [hOne]
    simp
  have hs := d.toJordanPair.semisimplePart_apply_of_mem_maxGenEigenspace 1 xP hx
  rw [semisimplePart_apply hT, semisimpleValue_eq hT P hP 1 (mem hT 1)]
  change (d.toJordanPair.semisimplePart xP).1 = 1
  simpa [xP] using congrArg Subtype.val hs

public lemma semisimplePart_mul [IsAlgClosed K]
    (hMul : ∀ x y : A, T (x * y) = T x * T y) (x y : A) :
    hT.semisimplePart (x * y) = hT.semisimplePart x * hT.semisimplePart y := by
  let P : Submodule K A := submodule hT x
  let Q : Submodule K A := submodule hT y
  let : Module.Finite K P := finite hT x
  let : Module.Finite K Q := finite hT y
  have hP : P ∈ T.invtSubmodule := invariant hT x
  have hQ : Q ∈ T.invtSubmodule := invariant hT y
  let TP : _root_.Module.End K P := T.restrict hP
  let TQ : _root_.Module.End K Q := T.restrict hQ
  let tensorT : _root_.Module.End K (TensorProduct K P Q) := TensorProduct.map TP TQ
  let m : TensorProduct K P Q →ₗ[K] A := Submodule.mulMap P Q
  have hm : m.comp tensorT = T.comp m := by
    ext a b
    change T (a : A) * T (b : A) = T (a * b)
    exact (hMul (a : A) (b : A)).symm
  let R : Submodule K A := LinearMap.range m
  let : Module.Finite K R := Module.Finite.range m
  have hR : R ∈ T.invtSubmodule := by
    rintro z ⟨w, rfl⟩
    refine ⟨tensorT w, ?_⟩
    exact LinearMap.congr_fun hm w
  let mR : TensorProduct K P Q →ₗ[K] R := m.rangeRestrict
  have hmR : mR.comp tensorT =
      (T.restrict (p := R) (q := R) hR).comp mR := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact LinearMap.congr_fun hm w
  let dP := invariantJordanDecomposition T P hP
  let dQ := invariantJordanDecomposition T Q hQ
  let dR := invariantJordanDecomposition T R hR
  let dTensor := dP.toJordanPair.tensorProduct dQ.toJordanPair
  have hS := dTensor.semiconj dR.toJordanPair mR hmR
  let xP : P := ⟨x, mem hT x⟩
  let yQ : Q := ⟨y, mem hT y⟩
  have hxyR : x * y ∈ R := ⟨TensorProduct.tmul K xP yQ, rfl⟩
  change semisimpleValue hT (x * y) =
    semisimpleValue hT x * semisimpleValue hT y
  rw [semisimpleValue_eq hT R hR (x * y) hxyR,
    semisimpleValue_eq hT P hP x (mem hT x),
    semisimpleValue_eq hT Q hQ y (mem hT y)]
  have h := congrArg Subtype.val
    (LinearMap.congr_fun hS (TensorProduct.tmul K xP yQ))
  simp only [LinearMap.comp_apply] at h
  have hmxy : mR (TensorProduct.tmul K xP yQ) = ⟨x * y, hxyR⟩ := by
    apply Subtype.ext
    rfl
  rw [hmxy] at h
  have hdTensor : dTensor.semisimplePart (TensorProduct.tmul K xP yQ) =
      TensorProduct.tmul K (dP.toJordanPair.semisimplePart xP)
        (dQ.toJordanPair.semisimplePart yQ) := by
    simp [dTensor, JordanPair.tensorProduct]
  rw [hdTensor] at h
  change
    ((dR.toJordanPair.semisimplePart ⟨x * y, hxyR⟩ : R) : A) =
      ((dP.toJordanPair.semisimplePart xP : P) : A) *
        ((dQ.toJordanPair.semisimplePart yQ : Q) : A)
  simpa [mR, m] using h.symm

@[expose]
public noncomputable def semisimpleAlgHom
    [IsAlgClosed K] (hOne : T 1 = 1)
    (hMul : ∀ x y : A, T (x * y) = T x * T y) : A →ₐ[K] A where
  toFun := hT.semisimplePart
  map_zero' := map_zero hT.semisimplePart
  map_add' := map_add hT.semisimplePart
  map_one' := semisimplePart_one hT hOne
  map_mul' := semisimplePart_mul hT hMul
  commutes' := fun r => by
    calc
      hT.semisimplePart (algebraMap K A r) =
          hT.semisimplePart (r • (1 : A)) := by
        rw [Algebra.smul_def, mul_one]
      _ = r • hT.semisimplePart 1 := map_smul hT.semisimplePart r 1
      _ = algebraMap K A r := by
        rw [semisimplePart_one hT hOne, Algebra.smul_def, mul_one]

@[expose]
public noncomputable def semisimpleAlgEquiv
    [IsAlgClosed K] (hTin : Function.Injective T) (hOne : T 1 = 1)
    (hMul : ∀ x y : A, T (x * y) = T x * T y) : A ≃ₐ[K] A :=
  AlgEquiv.ofBijective (semisimpleAlgHom hT hOne hMul)
    ⟨hT.semisimplePart_injective hTin, semisimplePart_surjective hT hTin⟩

end IsLocallyFinite

end Module.End

end Theory.AlgebraicGroup
