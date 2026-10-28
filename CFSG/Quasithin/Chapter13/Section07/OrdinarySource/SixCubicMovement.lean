module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixChief
public import CFSG.Quasithin.Chapter13.Section07.PairEIntersections
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Cubic movement on the original full-span quotient

A cubic subgroup of the contained A₆ component cannot fix V_H/U_H.
The action kernel contains O₂(K), so simplicity of K/O₂(K) would force
K into that kernel. The actual product H=KT then reduces the conjugate
span to VU_H. Since T acts trivially on the index-two quotient V/V₃,
this would make the whole H-action trivial, contrary to source13.7.7.

The final theorem obtains H=KT from the actual marked natural section
and applies this argument to each cubic subgroup of the original L₁.
It supplies the full-span contribution to the terminal six-chief count.
Source: Aschbacher--Smith,13.7.6(3a),13.7.7 and the conclusion of13.7.21,
printed pp.939--940 and945--946.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition Section08.TransvectionRecognition.Component
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

omit [Finite G] in
private theorem simple_core_kernel_contains_of_cubic
    {A C K : Subgroup G} [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hN : K ≤ normalizer (C : Set G)) (hQ : K.pCoreIn 2 ≤ C)
    (hAK : A ≤ K) (hAC' : A ≤ C) (hA : Nat.card A = 3) : K ≤ C := by
  let N := C.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer hN
  have hQN : pCore 2 K ≤ N := by
    intro x hx
    exact hQ (mem_map_of_mem K.subtype hx)
  let q := QuotientGroup.mk' (pCore 2 K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q)
    (Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)) with hbot | htop
  · have hNQ : N ≤ pCore 2 K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (f := q) N).mp hbot
    have hAQ : A ≤ K.pCoreIn 2 := by
      intro x hx
      exact mem_map_of_mem K.subtype (hNQ (show (⟨x,hAK hx⟩ : K) ∈ N from hAC' hx))
    have hp : IsPGroup 2 A := ((pCore_isPGroup (p := 2) (G := K)).map K.subtype).to_le hAQ
    have hc := hp.card_eq_or_dvd
    rw [hA] at hc
    norm_num at hc
  · have hNt : N = ⊤ := by
      have hh := comap_map_eq_self (f := q) (by simpa only [q,QuotientGroup.ker_mk'] using hQN)
      rw [htop,comap_top] at hh
      exact hh.symm
    intro x hx
    exact (show (⟨x,hx⟩ : K) ∈ N from hNt.symm ▸ mem_top _)

variable (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- An actual cubic in the A₆ component moves the noncentral full-span quotient. -/
theorem cubic_moves_full_span_quotient
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (hspan : ¬ ⁅Section08.Source.VH H V,H⁆ ≤ Section08.Source.UH H V₃)
    (A : Subgroup G) (hAK : A ≤ K) (hA : Nat.card A = 3) :
    ¬ ⁅Section08.Source.VH H V,A⁆ ≤ Section08.Source.UH H V₃ := by
  let U := Section08.Source.UH H V₃
  let W := Section08.Source.VH H V
  let C := commutatorPreimage H W U
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V₃ H
  have hHW : H ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy V H
  have hHC : H ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized H W U H hHU H.le_normalizer hHW hHU
  have hQC : H.pCoreIn 2 ≤ C := le_commutatorPreimage (pCoreIn_le 2 H)
    (by rw [commutator_comm]; exact source_span_core_commutator_le d h)
  intro hAC
  have hAC' : A ≤ C := le_commutatorPreimage (hAK.trans hKH)
    (by rw [commutator_comm]; exact hAC)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hKN : K ≤ C := simple_core_kernel_contains_of_cubic (hKH.trans hHC)
    ((pCoreAmbient_mono_of_isSubnormalIn K H 2 hKH hK.subnormal).trans hQC)
    hAK hAC' hA
  have hWU : ⁅W,K⁆ ≤ U := by
    rw [commutator_comm]
    exact (commutator_mono hKN le_rfl).trans (commutator_commutatorPreimage_le H W U hHU)
  have hWV : W ≤ V ⊔ U := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    have hgm : g ∈ (K : Set G) * (T : Set G) := hprod ▸ hg
    obtain ⟨k,hk,t,ht,rfl⟩ := hgm
    have htv : t*v*t⁻¹ ∈ V := le_normalizer_iff.mp
      (le_sup_right.trans d.normalizes_V) t ht v hv
    have hkw : ⁅k,t*v*t⁻¹⁆ ∈ U := by
      rw [commutator_comm] at hWU
      exact hWU (commutator_mem_commutator hk (le_conjugateSpanBy V H htv))
    have hm := (V ⊔ U).mul_mem (mem_sup_right hkw) (mem_sup_left htv)
    change (k*t)*v*(k*t)⁻¹ ∈ V ⊔ U
    have he : (k*t)*v*(k*t)⁻¹ = ⁅k,t*v*t⁻¹⁆ * (t*v*t⁻¹) := by group
    rw [he]
    exact hm
  have hvcard : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hi : V₃.relIndex V = 2 := by
    have hh := (V₃.subgroupOf V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe d.seed_le).toEquiv,d.seed_card,
      hvcard] at hh
    change V₃.relIndex V * 8 = 16 at hh
    omega
  have hVT : ⁅V,(T : Subgroup G)⁆ ≤ U :=
    (commutator_le_of_normalized_index_two V V₃ (T : Subgroup G) d.seed_le
      hi
      (le_sup_right.trans d.normalizes_V) d.seed_stable).trans (le_conjugateSpanBy V₃ H)
  have hUT : ⁅U,(T : Subgroup G)⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (h.T_le_H.trans hHU)
  have hVP : V ≤ commutatorPreimage H (T : Subgroup G) U := le_commutatorPreimage h.V_le_H hVT
  have hUP : U ≤ commutatorPreimage H (T : Subgroup G) U := le_commutatorPreimage h.UH_le_H hUT
  have hWT : ⁅W,(T : Subgroup G)⁆ ≤ U :=
    (commutator_mono (hWV.trans (sup_le hVP hUP)) le_rfl).trans
      (commutator_commutatorPreimage_le H (T : Subgroup G) U hHU)
  have hTC : (T : Subgroup G) ≤ C := le_commutatorPreimage h.T_le_H
    (by rw [commutator_comm]; exact hWT)
  apply hspan
  rw [commutator_comm]
  have hle : H ≤ C := by
    intro x hx
    have hm : x ∈ (K : Set G) * (T : Set G) := hprod ▸ hx
    obtain ⟨k,hk,t,ht,rfl⟩ := hm
    exact C.mul_mem (hKN hk) (hTC ht)
  exact (commutator_mono hle le_rfl).trans (commutator_commutatorPreimage_le H W U hHU)

/-- Every actual cubic in L₁ moves the full-span quotient in the contained A₆ case. -/
theorem source_six_cubic_movement
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (hspan : ¬ ⁅Section08.Source.VH H V,H⁆ ≤ Section08.Source.UH H V₃)
    (A : Subgroup G) (hAL : A ≤ sourceOne L T V₁) (hA : Nat.card A = 3) :
    ¬ ⁅Section08.Source.VH H V,A⁆ ≤ Section08.Source.UH H V₃ := by
  exact cubic_moves_full_span_quotient d h hKH hK eK
    (ModelExclusions.contained_six_full_action d hH h hKH hK hL₁K ρ hρ eK hs).1
    hspan A (hAL.trans hL₁K) hA

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
