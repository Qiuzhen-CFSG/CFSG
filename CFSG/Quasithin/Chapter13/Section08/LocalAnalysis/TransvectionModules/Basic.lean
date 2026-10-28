module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import Theory.Representation.BinaryPermutation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.PResidual.Defs
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Quotient

/-!
# Permutation quotients and subgroup steps for §13.8

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp.947–948, 13.8.4–6.

For 13.8.4(5), the orbit-sum map on the specified H*-coset space is a
surjective intertwining map onto the literal section V_H/U_H. The flag of
index two makes the stabilizer fix the seed vector, and conjugate generation
makes the map surjective. The target action is required to be compatible
with conjugation on that section.

The other results establish the final fixed-seed contradiction used in
13.8.5 and the subgroup calculation in 13.8.6(3). The definitions retain
K₂ = O²(C_H(V₂)) and U₂ = ⟨V^{K₂}⟩. The complete solvable normal-closure
exclusion, recognition, markings, ranks and module identifications remain
obligations of the higher local-analysis proofs.
-/

@[expose] public section

open scoped BigOperators
open Module
open Subgroup
open Representation

namespace CFSG.Quasithin.Chapter13.Section08

/-! ## The actual permutation-module map -/

variable {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]

/-- An equivariant orbit family spanning `X`.  In the application `X` is the
actual section `V_H/U_H`, `A` is `H*`, and the vectors are the images of the
conjugates of `V`. -/
structure PermutationSectionData (Ω : Type*) [Fintype Ω] where
  action : Representation (ZMod 2) A X
  permutation : A →* Equiv.Perm Ω
  vector : Ω → X
  equivariant : ∀ a i, action a (vector i) = vector (permutation a i)
  spanning : Submodule.span (ZMod 2) (Set.range vector) = ⊤

namespace PermutationSectionData

variable {Ω : Type*} [Fintype Ω]
  (d : PermutationSectionData (A := A) (X := X) Ω)

/-- The linear map sending the coordinate vector at `i` to the orbit vector
`vector i`. -/
def map : BinaryPermutation.Full Ω →ₗ[ZMod 2] X where
  toFun v := ∑ i, v i • d.vector i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact smul_assoc _ _ _

@[simp] theorem map_single [DecidableEq Ω] (i : Ω) (c : ZMod 2) :
    d.map (Pi.single i c) = c • d.vector i := by
  classical
  change (∑ j, ((Pi.single i c : BinaryPermutation.Full Ω) j) • d.vector j) = _
  simp

theorem map_surjective [DecidableEq Ω] : Function.Surjective d.map := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← d.spanning]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  rw [← one_smul (ZMod 2) (d.vector i), ← d.map_single]
  exact LinearMap.mem_range_self d.map (Pi.single i 1)

/-- The source and target actions are intertwined by the constructed map. -/
theorem map_equivariant (a : A) (v : BinaryPermutation.Full Ω) :
    d.action a (d.map v) =
      d.map (BinaryPermutation.representation Ω (d.permutation a) v) := by
  classical
  change d.action a (∑ i, v i • d.vector i) =
    ∑ i, v ((d.permutation a).symm i) • d.vector i
  rw [map_sum]
  simp_rw [map_smul, d.equivariant]
  rw [← Equiv.sum_comp (d.permutation a)
    (fun i => v ((d.permutation a).symm i) • d.vector i)]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The actual equivariant permutation-module surjection. -/
noncomputable def intertwiningMap :
    Representation.IntertwiningMap
      ((BinaryPermutation.representation Ω).comp d.permutation) d.action :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ d.map (by
    intro a v
    exact (d.map_equivariant a v).symm)

theorem intertwiningMap_surjective [DecidableEq Ω] : Function.Surjective d.intertwiningMap :=
  d.map_surjective

end PermutationSectionData

/-- Descend the orbit map of a stabilizer-fixed vector to left cosets. -/
noncomputable def cosetOrbitVector (ρ : Representation (ZMod 2) A X)
    (P : Subgroup A) (v : X) (hv : ∀ p ∈ P, ρ p v = v) : A ⧸ P → X :=
  fun c => Quotient.liftOn' c (fun a => ρ a v) (by
    intro a b hab
    have he := hv (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    calc
      ρ a v = ρ a (ρ (a⁻¹ * b) v) := congrArg (ρ a) he.symm
      _ = ρ b v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left])

@[simp] theorem cosetOrbitVector_mk (ρ : Representation (ZMod 2) A X)
    (P : Subgroup A) (v : X) (hv : ∀ p ∈ P, ρ p v = v) (a : A) :
    cosetOrbitVector ρ P v hv (QuotientGroup.mk a) = ρ a v := rfl

/-- A spanning orbit defines the permutation representation on its stabilizer cosets. -/
noncomputable def cosetPermutationSectionData (ρ : Representation (ZMod 2) A X)
    (P : Subgroup A) [Fintype (A ⧸ P)] (v : X)
    (hv : ∀ p ∈ P, ρ p v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range fun a => ρ a v) = ⊤) :
    PermutationSectionData (A := A) (X := X) (A ⧸ P) where
  action := ρ
  permutation := MulAction.toPermHom A (A ⧸ P)
  vector := cosetOrbitVector ρ P v hv
  equivariant a c := by
    induction c using QuotientGroup.induction_on with
    | H b =>
      change ρ a (ρ b v) = ρ (a * b) v
      rw [map_mul, Module.End.mul_apply]
  spanning := by
    rw [← hspan]
    congr 1
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      induction c using QuotientGroup.induction_on with
      | H a => exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk a, rfl⟩

/-- A quotient-generation lemma used to lift the source product decomposition.
The kernel is absorbed into `K`; no product equality is assumed. -/
theorem exists_product_of_quotient_generation
    {A : Type*} [Group A] (N K T : Subgroup A) [N.Normal]
    (hN : N ≤ K)
    (hgen : ∀ x : A ⧸ N, ∃ k : K, ∃ t : T,
      x = QuotientGroup.mk' N (k : A) * QuotientGroup.mk' N (t : A)) :
    ∀ a : A, ∃ k : K, ∃ t : T, (k : A) * t = a := by
  intro a
  obtain ⟨k, t, ht⟩ := hgen (QuotientGroup.mk' N a)
  have hq : (QuotientGroup.mk' N) a =
      (QuotientGroup.mk' N) ((k : A) * (t : A)) := by
    simpa only [map_mul] using ht
  let n : A := ((k : A) * (t : A)) / a
  have hn : n ∈ N := by
    dsimp [n]
    exact QuotientGroup.eq_iff_div_mem.mp hq.symm
  have hnK : n ∈ K := hN hn
  let k' : K := ⟨n⁻¹ * (k : A), K.mul_mem (K.inv_mem hnK) k.property⟩
  refine ⟨k', t, ?_⟩
  dsimp [k', n]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  group

end CFSG.Quasithin.Chapter13.Section08

open Subgroup Module Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08

variable {G : Type*} [Group G]

/-- The conjugation compatibility needed to use the literal source section. -/
def SectionConjugation (H V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃))) : Prop :=
  ∀ (h : H) (x : Source.VH H V),
    ρ (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)) x)) =
      Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V))
        ⟨(h : G) * (x : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H h.property) x).mp x.property⟩)

/-- The index-two version of the source permutation quotient construction. -/
private theorem permutation_surjection_of_section_index_two (H M V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    [Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))]
    (hindex : (Source.UH H V₃).relIndex V = 2)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ) :
    ∃ f : Representation.IntertwiningMap
      ((BinaryPermutation.representation (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))).comp
        (MulAction.toPermHom (Source.Hstar H) (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)))) ρ,
      Function.Surjective f := by
  classical
  let W := Source.VH H V
  let Z := Source.UH H V₃
  let q : W →* Source.Vsection H V V₃ := QuotientGroup.mk' (Z.subgroupOf W)
  let π : H →* Source.Hstar H := QuotientGroup.mk' (pCore 2 H)
  have hVW : V ≤ W := le_conjugateSpanBy V H
  obtain ⟨a, haV, haZ, hcoset⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hindex
  let v := Additive.ofMul (q ⟨a, hVW haV⟩)
  let S := Submodule.span (ZMod 2) (Set.range fun b => ρ b v)
  have hseed (b : G) (hb : b ∈ V) :
      Additive.ofMul (q ⟨b, hVW hb⟩) = 0 ∨ Additive.ofMul (q ⟨b, hVW hb⟩) = v := by
    rcases hcoset b hb with hba | hbZ
    · right
      have hqba : q (⟨b, hVW hb⟩ * ⟨a, hVW haV⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hba
      have he : Additive.ofMul (q ⟨b, hVW hb⟩) + v = 0 := hqba
      have hvv : v + v = 0 := by
        simpa only [add_smul, one_smul, zero_smul] using
          (congrArg (fun c : ZMod 2 => c • v) (show 1 + 1 = (0 : ZMod 2) from rfl))
      exact add_right_cancel (he.trans hvv.symm)
    · left
      exact (QuotientGroup.eq_one_iff _).mpr hbZ
  have hvne : v ≠ 0 := by
    intro hv
    apply haZ
    have he : q ⟨a, hVW haV⟩ = 1 := hv
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf W) ⟨a, hVW haV⟩).mp he
  have hfix : ∀ p ∈ Source.starImage H (H ⊓ M), ρ p v = v := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := hp
    have hcV : (h : G) * a * (h : G)⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hnorm hh) a).mp haV
    have hc := hseed _ hcV
    rw [← hρ h ⟨a, hVW haV⟩] at hc
    rcases hc with hz | hv
    · apply (hvne ?_).elim
      calc
        v = ρ (π h)⁻¹ (ρ (π h) v) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        _ = 0 := by rw [hz, map_zero]
    · exact hv
  let C := ((S.toAddSubgroup.toSubgroup').comap q).map W.subtype
  have hWC : W ≤ C := by
    apply (Subgroup.closure_le C).mpr
    rintro x ⟨h, hh, b, hb, rfl⟩
    let x : W := ⟨h * b * h⁻¹,
      (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H hh) b).mp (hVW hb)⟩
    refine ⟨x, ?_, rfl⟩
    change Additive.ofMul (q x) ∈ S
    rw [show Additive.ofMul (q x) = ρ (π ⟨h, hh⟩) (Additive.ofMul (q ⟨b, hVW hb⟩)) from
      (hρ ⟨h, hh⟩ ⟨b, hVW hb⟩).symm]
    rcases hseed b hb with hz | hv
    · rw [hz, map_zero]
      exact S.zero_mem
    · rw [hv]
      exact Submodule.subset_span ⟨_, rfl⟩
  have hspan : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) x.toMul
    obtain ⟨b', hb', heq⟩ := hWC b.property
    have he : b' = b := Subtype.ext heq
    subst b'
    change Additive.ofMul (q b) ∈ S at hb'
    change q b = x.toMul at hb
    change Additive.ofMul (q b) ∈ S at hb'
    simpa only [hb, ofMul_toMul] using hb'
  let d := cosetPermutationSectionData ρ (Source.starImage H (H ⊓ M)) v hfix hspan
  exact ⟨d.intertwiningMap, d.intertwiningMap_surjective⟩

/-- The permutation-module assertion in 13.8.4(5), from the source flag,
noncentrality from 13.7.7, the normalizer from 13.7.3(9), and the compatible
quotient action. -/
theorem source_13_8_4_permutation_surjection (H M V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    [Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))]
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ) :
    ∃ f : Representation.IntertwiningMap
      ((BinaryPermutation.representation (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))).comp
        (MulAction.toPermHom (Source.Hstar H) (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)))) ρ,
      Function.Surjective f := by
  have hi : V₃ = V ⊓ Source.UH H V₃ :=
    flag_intersection_of_index_two V V₃ (Source.UH H V₃)
      (le_inf hflag (le_conjugateSpanBy V₃ H)) hindex
      (seed_not_le_UH_of_noncentral H V V₃ hnoncentral)
  apply permutation_surjection_of_section_index_two H M V V₃ ?_ hnorm ρ hρ
  rwa [hi, inf_relIndex_left] at hindex

end CFSG.Quasithin.Chapter13.Section08

open Module Representation Subgroup
namespace CFSG.Quasithin.Chapter13.Section08
variable {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]

/-- The final centralizer argument in 13.8.5: normality propagates fixedness
of the seed through its orbit, and faithfulness then kills the subgroup.
This does not assume or establish the preceding solvable-case alternatives. -/
theorem normal_subgroup_eq_bot_of_fixed_generating_seed
    (ρ : Representation (ZMod 2) A X) (hfaithful : Function.Injective ρ)
    (K : Subgroup A) [K.Normal] (B : Set X)
    (hgen : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ b ∈ B, x = ρ a b} = ⊤)
    (hfixed : ∀ k ∈ K, ∀ b ∈ B, ρ k b = b) : K = ⊥ := by
  apply le_bot_iff.mp
  intro k hk
  change k = 1
  apply hfaithful
  ext x
  rw [map_one]
  change ρ k x = x
  have hx : x ∈ Submodule.span (ZMod 2) {x | ∃ a : A, ∃ b ∈ B, x = ρ a b} :=
    hgen.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hb, rfl⟩ := hx
    have hk' : a⁻¹ * k * a ∈ K := by
      simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem k hk a⁻¹
    calc
      ρ k (ρ a b) = ρ a (ρ (a⁻¹ * k * a) b) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = ρ a b := by rw [hfixed _ hk' b hb]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end CFSG.Quasithin.Chapter13.Section08

namespace CFSG.Quasithin.Chapter13.Section08.Source
open Subgroup
variable {G : Type*} [Group G]

/-- The two-residual of the centralizer in 13.8.6. This differs from the
normalizer-based construction used later in the linear-four branch. -/
def K2 (H V₂ : Subgroup G) : Subgroup G :=
  (pResidual 2 ↥(H ⊓ centralizer (V₂ : Set G))).map (H ⊓ centralizer (V₂ : Set G)).subtype

/-- The actual conjugate span in 13.8.6. -/
def U2 (H V V₂ : Subgroup G) : Subgroup G := conjugateSpanBy V (K2 H V₂)

theorem K2_le_centralizer (H V₂ : Subgroup G) :
    K2 H V₂ ≤ H ⊓ centralizer (V₂ : Set G) := map_subtype_le _

theorem K2_le (H V₂ : Subgroup G) : K2 H V₂ ≤ H :=
    (K2_le_centralizer H V₂).trans inf_le_left

theorem seed_le_U2 (H V V₂ : Subgroup G) : V ≤ U2 H V V₂ := le_conjugateSpanBy _ _

end CFSG.Quasithin.Chapter13.Section08.Source

namespace CFSG.Quasithin.Chapter13.Section08
open Subgroup
variable {G : Type*} [Group G]

/-- Normalizing both the seed and its actors normalizes their conjugate span. -/
theorem normalizes_conjugate_span (A B K : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hAK : A ≤ normalizer (K : Set G)) :
    A ≤ normalizer (conjugateSpanBy B K : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨k, hk, b, hb, rfl⟩
  refine Subgroup.subset_closure ⟨a * k * a⁻¹,
    (mem_normalizer_iff.mp (hAK ha) k).mp hk,
    a * b * a⁻¹, (mem_normalizer_iff.mp (hAB ha) b).mp hb, ?_⟩
  group

/-- The action on a seed propagates through conjugators normalizing its actor. -/
theorem actor_normalizes_conjugate_span (V L K : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (hKL : K ≤ normalizer (L : Set G)) :
    L ≤ normalizer (conjugateSpanBy V K : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl x ⟨k, hk, v, hv, rfl⟩
  have hl' : k⁻¹ * l * k ∈ L := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hKL (K.inv_mem hk)) l).mp hl
  refine Subgroup.subset_closure ⟨k, hk,
    (k⁻¹ * l * k) * v * (k⁻¹ * l * k)⁻¹,
    (mem_normalizer_iff.mp (hLV hl') v).mp hv, ?_⟩
  group

/-- Commutator generation propagates through conjugators normalizing the actor. -/
theorem conjugate_span_eq_commutator (V L K : Subgroup G)
    (hV : V = ⁅V, L⁆) (hKL : K ≤ normalizer (L : Set G)) :
    conjugateSpanBy V K = ⁅conjugateSpanBy V K, L⁆ := by
  have hLV : L ≤ normalizer (V : Set G) := by
    rw [hV]
    exact normalizer_commutator_ge_right V L
  let S := conjugateSpanBy V K
  have hKS : K ≤ normalizer (S : Set G) := le_normalizer_conjugateSpanBy V K
  have hKn : K ≤ normalizer (⁅S, L⁆ : Subgroup G) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hKS hk),
      mem_normalizer_iff_map_conj_eq.mp (hKL hk)]
  apply le_antisymm
  · apply conjugateSpanBy_le _ hKn
    rw [hV]
    exact commutator_mono (le_conjugateSpanBy V K) le_rfl
  · exact le_normalizer_iff_commutator_le_left.mp
      (actor_normalizes_conjugate_span V L K hLV hKL)

/-- Interchange two conjugate spans when the outer actors normalize the inner ones. -/
theorem conjugate_span_le_iterated_span (B L K : Subgroup G)
    (hKL : K ≤ normalizer (L : Set G)) :
    conjugateSpanBy (conjugateSpanBy B L) K ≤
      conjugateSpanBy (conjugateSpanBy B K) L := by
  apply conjugateSpanBy_le
    (conjugateSpanBy_mono (le_conjugateSpanBy B K) le_rfl)
  exact normalizes_conjugate_span K (conjugateSpanBy B K) L
    (le_normalizer_conjugateSpanBy B K) hKL

/-- The span computation in 13.8.6(3), before instantiating the local two-residual. -/
theorem local_13_8_6_commutator_span (H L L₂ K₂ V V₃ : Subgroup G)
    (hK : K₂ ≤ H) (hL : L₂ ≤ L) (hKL : K₂ ≤ normalizer (L₂ : Set G))
    (hgen : V = conjugateSpanBy V₃ L₂) (hcomm : V = ⁅V, L₂⁆) :
    conjugateSpanBy V K₂ = ⁅conjugateSpanBy V K₂, L₂⁆ ∧
      conjugateSpanBy V K₂ ≤ Source.UL L H V₃ := by
  refine ⟨conjugate_span_eq_commutator V L₂ K₂ hcomm hKL, ?_⟩
  rw [hgen]
  exact (conjugate_span_le_iterated_span V₃ L₂ K₂ hKL).trans
    (conjugateSpanBy_mono (conjugateSpanBy_mono le_rfl hK) hL)

/-- The group-theoretic part of 13.8.6(3), with the literal two-residual of
the centralizer. The local normality input comes from 13.5.4 after the
A₆ conclusion of 13.8.6(6) is established. -/
theorem source_U2_eq_commutator_le_UL (H L L₂ V V₂ V₃ : Subgroup G)
    (hL : L₂ ≤ L) (hlocal : normalizer (V₂ : Set G) ≤ normalizer (L₂ : Set G))
    (hgen : V = conjugateSpanBy V₃ L₂) (hcomm : V = ⁅V, L₂⁆) :
    Source.U2 H V V₂ = ⁅Source.U2 H V V₂, L₂⁆ ∧
      Source.U2 H V V₂ ≤ Source.UL L H V₃ := by
  have hK : Source.K2 H V₂ ≤ normalizer (L₂ : Set G) :=
    (Source.K2_le_centralizer H V₂).trans
      (inf_le_right.trans ((centralizer_le_normalizer _).trans hlocal))
  exact local_13_8_6_commutator_span H L L₂ (Source.K2 H V₂) V V₃
    (Source.K2_le H V₂) hL hK hgen hcomm

end CFSG.Quasithin.Chapter13.Section08

end
