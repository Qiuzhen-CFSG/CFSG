module
public import Theory.Representation.PSL3Two.FanoLocalStructure.Basic

/-!
# Nontrivial quotients of the binary Fano-line permutation module

The line module splits into its augmentation core and its constant line.
The proved three-submodule classification of the core forces its nonzero
quotient to have dimension three or six. Adjoining the image of the constant
line gives dimensions three, four, six or seven.

The kernel of a quotient of dimension greater than one lies in the kernel
of the covector weighted sum. To prove this without assuming a splitting of
the quotient, a fixed image of a core vector is shown to be zero in each of
the two possible proper core kernels. The weighted sum therefore descends
to a surjective intertwiner onto the actual dual natural module. All results
allow pullback along a specified surjective actor homomorphism.

Source: Aschbacher--Smith, H.5.3, printed pp.385--386, applied in 14.3.29(1),
printed p.1002. This is the line version of the source's point-core calculation.
-/

@[expose] public noncomputable section
open Representation Module
namespace BinaryLinearThree.FanoLineQuotients
open FanoDecomposition FanoCoreStructure

local instance : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩

abbrev Full := BinaryPermutation.Full Line
abbrev lineRepresentation : Representation (ZMod 2) Group Full :=
  (BinaryPermutation.representation Line).comp linePerm

def inclusion : lineCoreRepresentation.IntertwiningMap lineRepresentation :=
  ⟨(BinaryPermutation.core Line).subtype, by intro g; rfl⟩

def projection : lineRepresentation.IntertwiningMap lineCoreRepresentation where
  toLinearMap := {
    toFun a := ⟨a - BinaryPermutation.augmentation Line a • BinaryPermutation.allOne Line, by
      change BinaryPermutation.augmentation Line _ = 0
      have h : BinaryPermutation.augmentation Line (BinaryPermutation.allOne Line) = 1 := by
        rw [BinaryPermutation.augmentation_allOne, Matrix.PSL3Two.Fano.card_line]; decide
      simp only [map_sub, map_smul, h, smul_eq_mul, mul_one, sub_self]⟩
    map_add' a b := by apply Subtype.ext; simp [add_smul]; abel
    map_smul' c a := by apply Subtype.ext; simp [smul_sub, smul_smul] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change lineRepresentation g a - BinaryPermutation.augmentation Line (lineRepresentation g a) •
      BinaryPermutation.allOne Line = lineRepresentation g (a -
        BinaryPermutation.augmentation Line a • BinaryPermutation.allOne Line)
    simp [lineRepresentation]

@[simp] theorem projection_inclusion (a : LineCore) : projection (inclusion a) = a := by
  apply Subtype.ext
  change a.val - BinaryPermutation.augmentation Line a.val • BinaryPermutation.allOne Line = a.val
  rw [show BinaryPermutation.augmentation Line a.val = 0 from a.property, zero_smul, sub_zero]

theorem decomposition (a : Full) :
    inclusion (projection a) + BinaryPermutation.augmentation Line a • BinaryPermutation.allOne Line = a :=
  sub_add_cancel _ _

def weightedSum : lineRepresentation.IntertwiningMap W.dual := lineWeightedSum.comp projection

theorem weightedSum_surjective : Function.Surjective weightedSum := by
  intro v
  obtain ⟨a, ha⟩ := lineWeightedSum_surjective v
  exact ⟨inclusion a, by simpa [weightedSum] using ha⟩

private theorem core_fixed_eq_zero (a : LineCore)
    (h : ∀ g, lineCoreRepresentation g a = a) : a = 0 := by
  have he (l : Line) : a.val l = a.val Matrix.PSL3Two.flagLine := by
    obtain ⟨g, hg⟩ := FanoLocalStructure.line_reachable l
    have hh := congrArg (fun b : LineCore => b.val l) (h g)
    change a.val ((linePerm g).symm l) = a.val l at hh
    rw [← hg, Equiv.symm_apply_apply] at hh
    simpa only [hg] using hh.symm
  have hz := a.property
  change (∑ l : Line, a.val l) = 0 at hz
  simp only [he, Finset.sum_const, Finset.card_univ, Matrix.PSL3Two.Fano.card_line] at hz
  have hc : a.val Matrix.PSL3Two.flagLine = 0 := by
    exact (by decide : ∀ c : ZMod 2, 7 • c = 0 → c = 0) _ hz
  apply Subtype.ext
  funext l
  exact (he l).trans hc

private theorem natural_fixed_eq_zero (v : Vector) (h : ∀ g, W g v = v) : v = 0 := by
  have ht : ∀ v : Vector, (∀ g : Group, W g v = v) → v = 0 := by decide +kernel
  exact ht v h

private theorem dual_fixed_eq_zero (φ : Dual) (h : ∀ g, W.dual g φ = φ) : φ = 0 := by
  let e := AutomorphismAction.graphNaturalDual
  have hv : e.symm φ = 0 := natural_fixed_eq_zero _ (by
    intro g
    have hh := LinearMap.congr_fun (e.isIntertwining' (AutomorphismAction.graph g)) (e.symm φ)
    change e (W (AutomorphismAction.graph (AutomorphismAction.graph g)) (e.symm φ)) =
      W.dual (AutomorphismAction.graph g) (e (e.symm φ)) at hh
    rw [AutomorphismAction.graph_graph, e.apply_symm_apply, h] at hh
    exact e.toLinearEquiv.injective (hh.trans (e.apply_symm_apply φ).symm))
  exact (e.apply_symm_apply φ).symm.trans (by rw [hv, map_zero])

universe u v
variable {A : Type u} [_root_.Group A] {M : Type v} [AddCommGroup M] [Module (ZMod 2) M]
variable (f : A →* Group) (hf : Function.Surjective f) (ρ : Representation (ZMod 2) A M)
  (q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ)

private def coreMap : LineCore →ₗ[ZMod 2] M := q.toLinearMap.comp inclusion.toLinearMap

private def coreKernel : Subrepresentation lineCoreRepresentation where
  toSubmodule := (coreMap f ρ q).ker
  apply_mem_toSubmodule g a ha := by
    obtain ⟨x, rfl⟩ := hf g
    change q (inclusion (lineCoreRepresentation (f x) a)) = 0
    rw [IntertwiningMap.isIntertwining lineCoreRepresentation lineRepresentation inclusion]
    change q ((lineRepresentation.comp f) x (inclusion a)) = 0
    rw [q.isIntertwining, show q (inclusion a) = 0 from ha, map_zero]

private theorem coreKernel_ne_top (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M) :
    coreKernel f hf ρ q ≠ ⊤ := by
  intro he
  have hz (a : LineCore) : q (inclusion a) = 0 := by
    have hm : a ∈ coreKernel f hf ρ q := he ▸ (show a ∈ (⊤ : Subrepresentation lineCoreRepresentation) from trivial)
    exact hm
  have hspan : (⊤ : Submodule (ZMod 2) M) ≤ Submodule.span (ZMod 2) {q (BinaryPermutation.allOne Line)} := by
    intro m _
    obtain ⟨a, rfl⟩ := hq m
    rw [← decomposition a, map_add, hz, zero_add, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hd' := Submodule.finrank_mono hspan
  rw [finrank_top] at hd'
  exact (not_le_of_gt hd) (hd'.trans (by simpa using finrank_span_le_card ({q (BinaryPermutation.allOne Line)} : Set M)))

include hf

private theorem core_fixed_image (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M)
    (a : LineCore) (ha : ∀ x : A, ρ x (q (inclusion a)) = q (inclusion a)) :
    q (inclusion a) = 0 := by
  have hdiff (g : Group) : lineCoreRepresentation g a - a ∈ coreKernel f hf ρ q := by
    obtain ⟨x, rfl⟩ := hf g
    change q (inclusion (lineCoreRepresentation (f x) a - a)) = 0
    rw [map_sub, map_sub, inclusion.isIntertwining]
    change q ((lineRepresentation.comp f) x (inclusion a)) - q (inclusion a) = 0
    rw [q.isIntertwining, ha, sub_self]
  rcases lineCore_subrepresentations (coreKernel f hf ρ q) with hn | hn | hn
  · have hz : a = 0 := core_fixed_eq_zero a (fun g => by
      have hh := hdiff g
      rw [hn] at hh
      exact sub_eq_zero.mp hh)
    rw [hz, map_zero, map_zero]
  · have hz : lineWeightedSum a = 0 := dual_fixed_eq_zero _ (by
      intro g
      have hh := hdiff g
      rw [hn] at hh
      change lineWeightedSum (lineCoreRepresentation g a - a) = 0 at hh
      rw [map_sub, lineWeightedSum.isIntertwining] at hh
      exact sub_eq_zero.mp hh)
    have hm : a ∈ lineKernel := hz
    rw [← hn] at hm
    exact hm
  · exact False.elim (coreKernel_ne_top f hf ρ q hq hd hn)

private theorem quotient_kernel (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M) :
    q.toLinearMap.ker ≤ weightedSum.toLinearMap.ker := by
  intro a ha
  have hqone (x : A) : ρ x (q (BinaryPermutation.allOne Line)) = q (BinaryPermutation.allOne Line) := by
    rw [← q.isIntertwining]
    rfl
  have hpa : q (inclusion (projection a)) =
      -(BinaryPermutation.augmentation Line a • q (BinaryPermutation.allOne Line)) := by
    have hh := congrArg q (decomposition a)
    rw [map_add, map_smul, show q a = 0 from ha] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hz : q (inclusion (projection a)) = 0 := core_fixed_image f hf ρ q hq hd _ (by
    intro x
    rw [hpa, map_neg, map_smul, hqone])
  have hm : projection a ∈ coreKernel f hf ρ q := hz
  rcases lineCore_subrepresentations (coreKernel f hf ρ q) with hn | hn | hn
  · rw [hn] at hm
    change lineWeightedSum (projection a) = 0
    rw [show projection a = 0 from hm, map_zero]
  · rw [hn] at hm
    exact hm
  · exact False.elim (coreKernel_ne_top f hf ρ q hq hd hn)

/-- A nontrivial-action quotient of the line permutation module has a literal dual-natural quotient. -/
theorem dual_quotient (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M) :
    ∃ r : ρ.IntertwiningMap (W.dual.comp f), Function.Surjective r := by
  let e := q.toLinearMap.quotKerEquivOfSurjective hq
  let z := q.toLinearMap.ker.liftQ weightedSum.toLinearMap (quotient_kernel f hf ρ q hq hd)
  let r : M →ₗ[ZMod 2] Dual := z.comp e.symm.toLinearMap
  have hr (a : Full) : r (q a) = weightedSum a := by
    change z (e.symm (q a)) = weightedSum a
    rw [show q a = e (Submodule.Quotient.mk a) from rfl, e.symm_apply_apply]
    rfl
  refine ⟨⟨r, ?_⟩, ?_⟩
  · intro x
    apply LinearMap.ext
    intro m
    obtain ⟨a, rfl⟩ := hq m
    change r (ρ x (q a)) = W.dual (f x) (r (q a))
    rw [← q.isIntertwining, hr, hr]
    exact IntertwiningMap.isIntertwining lineRepresentation W.dual weightedSum (f x) a
  · intro φ
    obtain ⟨a, ha⟩ := weightedSum_surjective φ
    exact ⟨q a, (hr a).trans ha⟩


variable [FiniteDimensional (ZMod 2) M]

/-- The only nontrivial-action quotient dimensions are three, four, six and seven. -/
theorem quotient_dimensions (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M) :
    finrank (ZMod 2) M = 3 ∨ finrank (ZMod 2) M = 4 ∨
      finrank (ZMod 2) M = 6 ∨ finrank (ZMod 2) M = 7 := by
  let r := coreMap f ρ q
  have hc : finrank (ZMod 2) LineCore = 6 := by
    rw [BinaryPermutation.finrank_core, Matrix.PSL3Two.Fano.card_line]
  have hr : finrank (ZMod 2) (LinearMap.range r) = 3 ∨
      finrank (ZMod 2) (LinearMap.range r) = 6 := by
    have he := r.finrank_range_add_finrank_ker
    rw [hc] at he
    rcases lineCore_subrepresentations (coreKernel f hf ρ q) with hn | hn | hn
    · have hk : r.ker = ⊥ := congrArg Subrepresentation.toSubmodule hn
      rw [hk, finrank_bot] at he
      exact Or.inr (by omega)
    · have hk : r.ker = lineKernel.toSubmodule := congrArg Subrepresentation.toSubmodule hn
      have hdK : finrank (ZMod 2) lineKernel.toSubmodule = 3 := by
        rw [← lineKernelEquiv.toLinearEquiv.finrank_eq]
        exact Module.finrank_fin_fun (ZMod 2)
      rw [hk] at he
      exact Or.inl (by omega)
    · exact False.elim (coreKernel_ne_top f hf ρ q hq hd hn)
  let s : (LinearMap.range r × ZMod 2) →ₗ[ZMod 2] M := {
    toFun x := x.1.val + x.2 • q (BinaryPermutation.allOne Line)
    map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]; abel
    map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
      smul_add, smul_smul, RingHom.id_apply, smul_eq_mul] }
  have hs : Function.Surjective s := by
    intro m
    obtain ⟨a, rfl⟩ := hq m
    refine ⟨(⟨r (projection a), ⟨projection a, rfl⟩⟩, BinaryPermutation.augmentation Line a), ?_⟩
    change q (inclusion (projection a)) + BinaryPermutation.augmentation Line a •
      q (BinaryPermutation.allOne Line) = q a
    rw [← map_smul, ← map_add, decomposition]
  have hupper := LinearMap.finrank_le_finrank_of_surjective hs
  rw [Module.finrank_prod, Module.finrank_self] at hupper
  have hlower := (LinearMap.range r).finrank_le
  omega

end BinaryLinearThree.FanoLineQuotients
