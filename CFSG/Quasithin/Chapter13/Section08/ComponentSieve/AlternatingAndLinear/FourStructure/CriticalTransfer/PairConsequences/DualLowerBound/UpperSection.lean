module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlanePermutation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ConjugateSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

/-!
# The upper-section argument for strict critical actors

The actual quotient map V_H → V_H/U_H and its conjugation formula keep
this action attached to the source subgroups. An index-two seed, its
H-conjugate span and its marked plane-parabolic normalizer construct the
cyclic vector required by the plane-permutation theorem.

At the other endpoint, equality Uγ*=Vγ* would bound [U_H,Vγ] by Uγ V₁.
Normal generation makes its image modulo Uγ nonzero. Since |V₁|=2,
some element would consequently have displacement rank one on Vγ/Uγ.
Transport by the specified ambient conjugator contradicts the proved
exclusion on V_H/U_H. This supplies the no-transvection branch of
13.8.11(1), with its earlier generation and edge-centrality inputs explicit.
All normality is relative to the indicated vertex group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.4(5), 13.8.9 and 13.8.11(1), printed
pp.947–950; 13.8.18(2), p.953; and the plane-parabolic identification in
13.8.25, pp.960–962. This is the additional reason beyond centrality of
I ∩ D_H used in the dual lower-bound assembly.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]

/-- A concrete binary model of V/U with the actual H/O₂(H) action. Unlike
the lower central section, its kernel U need only be normalized by H. -/
structure UpperSection (H V U : Subgroup G)
    (τ : Representation (ZMod 2) (Source.Hstar H) E) where
  le : V ≤ H
  normalizes : H ≤ normalizer (V : Set G)
  kernel_le : U ≤ V
  quotient : V →* Multiplicative E
  surjective : Function.Surjective quotient
  kernel : quotient.ker = U.subgroupOf V
  conjugates : ∀ (a : H) (v : V),
    τ (QuotientGroup.mk' (pCore 2 H) a) (quotient v).toAdd =
      (quotient ⟨(a : G) * (v : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (normalizes a.property) v).mp v.property⟩).toAdd

namespace UpperSection
variable {H V U : Subgroup G} {τ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : UpperSection H V U τ)
include s

noncomputable def conjugate (e : G ≃* G) :
    UpperSection (H.map e.toMonoidHom) (V.map e.toMonoidHom)
      (U.map e.toMonoidHom) (τ.comp (starEquiv e H).symm.toMonoidHom) where
  le := map_mono s.le
  normalizes := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono s.normalizes
  kernel_le := map_mono s.kernel_le
  quotient := s.quotient.comp (V.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
  surjective := s.surjective.comp (V.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  kernel := by
    ext x
    change (V.equivMapOfInjective e.toMonoidHom e.injective).symm x ∈ s.quotient.ker ↔
      (x : G) ∈ U.map e.toMonoidHom
    rw [s.kernel, mem_subgroupOf, equivMap_symm_val, mem_map_equiv]
  conjugates := by
    intro a u
    change τ ((starEquiv e H).symm
      (QuotientGroup.mk' (pCore 2 (H.map e.toMonoidHom)) a))
      (s.quotient ((V.equivMapOfInjective e.toMonoidHom e.injective).symm u)).toAdd = _
    rw [starEquiv_symm_mk, s.conjugates]
    apply congrArg (fun x : V => (s.quotient x).toAdd)
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, equivMap_symm_val, map_mul, map_inv]

theorem commutator_mem (a : H) (v : V) : ⁅(a : G), (v : G)⁆ ∈ V :=
  commutator_le.mp (le_normalizer_iff_commutator_le_right.mp s.normalizes)
    a a.property v v.property

theorem displacement (a : H) (v : V) :
    τ (QuotientGroup.mk' (pCore 2 H) a) (s.quotient v).toAdd - (s.quotient v).toAdd =
      (s.quotient ⟨⁅(a : G), (v : G)⁆, s.commutator_mem a v⟩).toAdd := by
  rw [s.conjugates]
  have he : (⟨⁅(a : G), (v : G)⁆, s.commutator_mem a v⟩ : V) =
      ⟨(a : G) * (v : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes a.property) v).mp v.property⟩ * v⁻¹ := rfl
  rw [he, map_mul, map_inv]
  exact sub_eq_add_neg _ _

def image (X : Subgroup G) : Submodule (ZMod 2) E :=
  AddSubgroup.toZModSubmodule 2 ((X.subgroupOf V).map s.quotient).toAddSubgroup'

theorem image_kernel_sup (Z : Subgroup G) (hZV : Z ≤ V) :
    s.image (U ⊔ Z) = s.image Z := by
  unfold image
  rw [subgroupOf_sup s.kernel_le hZV, Subgroup.map_sup]
  rw [(Subgroup.map_eq_bot_iff (U.subgroupOf V)).mpr s.kernel.ge, bot_sup_eq]

theorem normalizes_kernel : H ≤ normalizer (U : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha u hu
  have hz : (s.quotient ⟨u, s.kernel_le hu⟩).toAdd = 0 := by
    change (⟨u, s.kernel_le hu⟩ : V) ∈ s.quotient.ker
    rwa [s.kernel]
  have hc := s.conjugates ⟨a, ha⟩ ⟨u, s.kernel_le hu⟩
  rw [hz, map_zero] at hc
  have hk : (⟨a * u * a⁻¹,
      (mem_normalizer_iff.mp (s.normalizes ha) u).mp (s.kernel_le hu)⟩ : V) ∈ s.quotient.ker := hc.symm
  rwa [s.kernel] at hk

/-- The source index-two seed and normal generation construct the actual
plane-parabolic cyclic vector, rather than postulating a permutation label. -/
theorem planeGenerated_of_index_two_seed
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (X : Subgroup G) (hXV : X ≤ V) (hspan : V = conjugateSpanBy X H)
    (hindex : U.relIndex X = 2)
    (P : Submodule (ZMod 2) ChiefFactors.NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hparabolic : ∀ a : H, eH (QuotientGroup.mk' (pCore 2 H) a) ∈
      BinaryLinear.parabolic P → (a : G) ∈ normalizer (X : Set G)) :
    IsPlaneParabolicGenerated τ eH := by
  obtain ⟨x, hx, hxu, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hindex
  let xV : V := ⟨x, hXV hx⟩
  let v : E := (s.quotient xV).toAdd
  have hneg : -v = v := by
    calc
      -v = (-1 : ZMod 2) • v := (neg_one_smul (ZMod 2) v).symm
      _ = v := by rw [show (-1 : ZMod 2) = 1 from by decide, one_smul]
  have hseed (y : V) (hy : (y : G) ∈ X) : (s.quotient y).toAdd = 0 ∨ (s.quotient y).toAdd = v := by
    rcases hcosets y hy with h | h
    · right
      have hh : (s.quotient (y * xV)).toAdd = 0 := by
        change y * xV ∈ s.quotient.ker
        rwa [s.kernel]
      rw [map_mul] at hh
      exact (eq_neg_of_add_eq_zero_left hh).trans hneg
    · left
      change y ∈ s.quotient.ker
      rwa [s.kernel]
  refine ⟨P, v, hP, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    have hyX : (a : G) * x * (a : G)⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hparabolic a hg) x).mp hx
    let y : V := ⟨(a : G) * x * (a : G)⁻¹, hXV hyX⟩
    have he : τ (QuotientGroup.mk' (pCore 2 H) a) v = (s.quotient y).toAdd :=
      s.conjugates a xV
    rw [he]
    rcases hseed y hyX with hy | hy
    · have hyU : (y : G) ∈ U := by
        change y ∈ U.subgroupOf V
        rw [← s.kernel]
        exact hy
      exact (hxu ((mem_normalizer_iff.mp (s.normalizes_kernel a.property) x).mpr hyU)).elim
    · exact hy
  · let S := Submodule.span (ZMod 2) (Set.range (fun g => τ g v))
    let K : Subgroup G := ((S.toAddSubgroup.toSubgroup').comap s.quotient).map V.subtype
    have hVK : V ≤ K := by
      rw [hspan]
      apply (closure_le _).mpr
      rintro _ ⟨a, ha, y, hy, rfl⟩
      let yV : V := ⟨y, hXV hy⟩
      refine ⟨⟨a * y * a⁻¹,
        (mem_normalizer_iff.mp (s.normalizes ha) y).mp (hXV hy)⟩, ?_, rfl⟩
      change (s.quotient _).toAdd ∈ S
      rw [← s.conjugates ⟨a, ha⟩ yV]
      rcases hseed yV hy with he | he
      · rw [he, map_zero]
        exact S.zero_mem
      · rw [he]
        exact Submodule.subset_span ⟨_, rfl⟩
    apply top_unique
    intro w _
    obtain ⟨y, hy⟩ := s.surjective (Multiplicative.ofAdd w)
    obtain ⟨z, hz, he⟩ := hVK y.property
    have he' : z = y := Subtype.ext he
    subst z
    change (s.quotient y).toAdd ∈ S at hz
    rwa [hy] at hz

variable [Finite G] [FiniteDimensional (ZMod 2) E]

theorem image_finrank_le_one (Z : Subgroup G) (hZ : Nat.card Z = 2) :
    Module.finrank (ZMod 2) (s.image Z) ≤ 1 := by
  have hsurj : Function.Surjective
      (fun x : Z.subgroupOf V => (⟨(s.quotient x.val).toAdd,
        ⟨x.val, x.property, rfl⟩⟩ : s.image Z)) := by
    intro u
    obtain ⟨x, hx, he⟩ := u.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hi : Function.Injective (fun x : Z.subgroupOf V => (⟨x.val.val, x.property⟩ : Z)) := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Z => (z : G)) h))
  have hc := (Nat.card_le_card_of_surjective _ hsurj).trans
    (Nat.card_le_card_of_injective _ hi)
  rw [hZ, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have := Nat.log_monotone (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 2 = 1 from by decide] using this

theorem exists_rank_one_of_noncentral_line
    (F Z : Subgroup G) (hFH : F ≤ H) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hbound : ⁅F, V⁆ ≤ U ⊔ Z) (hnoncentral : ¬ ⁅F, V⁆ ≤ U) :
    ∃ f : F, Module.finrank (ZMod 2)
      (LinearMap.range (τ (QuotientGroup.mk' (pCore 2 H) ⟨f, hFH f.property⟩) - 1)) = 1 := by
  have hex : ∃ f ∈ F, ∃ v ∈ V, ⁅f, v⁆ ∉ U := by
    by_contra! hh
    exact hnoncentral (commutator_le.mpr hh)
  obtain ⟨f, hf, v, hv, hne⟩ := hex
  let a : H := ⟨f, hFH hf⟩
  let d := τ (QuotientGroup.mk' (pCore 2 H) a) - 1
  have hr : LinearMap.range d ≤ s.image Z := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨x, hx⟩ := s.surjective (Multiplicative.ofAdd w)
    have hw : (s.quotient x).toAdd = w := congrArg Multiplicative.toAdd hx
    change τ _ w - w ∈ s.image Z
    rw [← hw, s.displacement, ← s.image_kernel_sup Z hZV]
    exact ⟨⟨⁅f, (x : G)⁆, s.commutator_mem a x⟩,
      commutator_le.mp hbound f hf x x.property, rfl⟩
  have hd : d (s.quotient ⟨v, hv⟩).toAdd ≠ 0 := by
    intro he
    have he' : (s.quotient ⟨⁅f, v⁆, s.commutator_mem a ⟨v, hv⟩⟩).toAdd = 0 :=
      (s.displacement a ⟨v, hv⟩).symm.trans he
    have hk : (⟨⁅f, v⁆, s.commutator_mem a ⟨v, hv⟩⟩ : V) ∈ s.quotient.ker := he'
    rw [s.kernel] at hk
    exact hne hk
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range d) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨_, ⟨_, rfl⟩⟩, fun he => hd (congrArg Subtype.val he)⟩
  have hle := (Submodule.finrank_mono hr).trans (s.image_finrank_le_one Z hZ)
  exact ⟨⟨f, hf⟩, by change Module.finrank (ZMod 2) (LinearMap.range d) = 1; omega⟩
omit [FiniteDimensional (ZMod 2) E] in
/-- The center of a nontrivial line-valued displacement really lies in V. -/
theorem line_le_of_noncentral_bound
    (F Z : Subgroup G) (hFH : F ≤ H) (hZH : Z ≤ H) (hZ : Nat.card Z = 2)
    (hbound : ⁅F, V⁆ ≤ U ⊔ Z) (hnoncentral : ¬ ⁅F, V⁆ ≤ U) : Z ≤ V := by
  let _ : (U.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer s.normalizes_kernel
  let _ : (V.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer s.normalizes
  have hb : ⁅F.subgroupOf H, V.subgroupOf H⁆ ≤ U.subgroupOf H ⊔ Z.subgroupOf H := by
    rw [← subgroupOf_sup (s.kernel_le.trans s.le) hZH]
    apply map_le_iff_le_comap.mp
    rwa [map_commutator, map_subgroupOf_eq_of_le hFH, map_subgroupOf_eq_of_le s.le]
  have hn : ¬ ⁅F.subgroupOf H, V.subgroupOf H⁆ ≤ U.subgroupOf H := by
    intro hh
    apply hnoncentral
    have hm := map_le_iff_le_comap.mpr hh
    rwa [map_commutator, map_subgroupOf_eq_of_le hFH, map_subgroupOf_eq_of_le s.le] at hm
  have hcard : Nat.card (Z.subgroupOf H) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv, hZ]
  have hz := (CriticalGeometry.line_le_of_noncentral_commutator
    (F.subgroupOf H) (V.subgroupOf H) (U.subgroupOf H) (Z.subgroupOf H)
    (subgroupOf_mono H s.kernel_le) hcard hb hn).1
  intro z hz'
  exact hz (show (⟨z, hZH hz'⟩ : H) ∈ Z.subgroupOf H from hz')

/-- The full noncentrality and line calculation yields a rank-one element. -/
theorem exists_rank_one_of_noncentral_bound
    (F Z : Subgroup G) (hFH : F ≤ H) (hZH : Z ≤ H) (hZ : Nat.card Z = 2)
    (hbound : ⁅F, V⁆ ≤ U ⊔ Z) (hnoncentral : ¬ ⁅F, V⁆ ≤ U) :
    ∃ f : F, Module.finrank (ZMod 2)
      (LinearMap.range (τ (QuotientGroup.mk' (pCore 2 H) ⟨f, hFH f.property⟩) - 1)) = 1 :=
  s.exists_rank_one_of_noncentral_line F Z hFH
    (s.line_le_of_noncentral_bound F Z hFH hZH hZ hbound hnoncentral) hZ hbound hnoncentral

end UpperSection
section Strict
variable {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) T}

/-- The actual section kills commutators with the two-core; no faithful-action
identification is needed for this direction. -/
theorem central_section_core_commutator (s : ConjugationSection H UH Z ρ) :
    ⁅UH, Source.QH H⁆ ≤ Z := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro a ⟨aH, ha, rfl⟩ u hu
  have he : QuotientGroup.mk' (pCore 2 H) aH = 1 := (QuotientGroup.eq_one_iff aH).mpr ha
  apply (s.quotient_eq_zero_iff ⟨⁅(aH : G), u⁆, s.commutator_mem aH ⟨u, hu⟩⟩).mp
  rw [← s.displacement aH ⟨u, hu⟩, he, map_one]
  exact sub_self _

variable [Finite G] [FiniteDimensional (ZMod 2) E]

/-- The no-transvection branch of 13.8.11(1), on the actual upper section.
Normal generation supplies the nonzero displacement; equality of star images
would confine every displacement to the image of the central line. -/
theorem starImage_lt_of_upper_no_rank_one
    (s : ConjugationSection H UH Z ρ)
    (J Ug Vg X B : Subgroup G)
    (τ : Representation (ZMod 2) (Source.Hstar J) E)
    (t : UpperSection J Vg Ug τ)
    (hVgH : Vg ≤ H) (hUHJ : UH ≤ J) (hZ : Nat.card Z = 2)
    (hspan : Vg = conjugateSpanBy X J)
    (hgen : J = conjugateSpanBy UH J ⊔ B)
    (hedge : ⁅B, X⁆ ≤ Ug) (hnoncentral : ¬ ⁅J, Vg⁆ ≤ Ug)
    (hno : ∀ a, Module.finrank (ZMod 2) (LinearMap.range (τ a - 1)) ≠ 1) :
    Source.starImage H Ug < Source.starImage H Vg := by
  have hUV := t.kernel_le
  have hn := CriticalGeometry.noncentral_of_relative_generation J UH B X Vg Ug hUHJ
    ((le_conjugateSpanBy X J).trans (hspan.symm.le.trans t.le))
    t.normalizes_kernel hspan hgen hedge hnoncentral
  refine lt_of_le_of_ne (map_mono (subgroupOf_mono H hUV)) ?_
  intro heq
  have hc := CriticalGeometry.commutator_bound_of_equal_starImage H UH Ug Vg Z
    s.le hVgH (s.line_le.trans s.le)
    (s.centralizes.trans (centralizer_le_normalizer _)) hUV
    (hVgH.trans s.normalizes) (central_section_core_commutator s) heq
  have hb : ⁅UH, Vg⁆ ≤ Ug ⊔ Z := hc.trans (sup_le_sup_right
    (le_normalizer_iff_commutator_le_right.mp (hUHJ.trans t.normalizes_kernel)) Z)
  obtain ⟨a, ha⟩ := t.exists_rank_one_of_noncentral_bound UH Z hUHJ
    (s.line_le.trans hUHJ) hZ hb hn
  exact hno _ ha

/-- Transport the genuine V_H/U_H action to the other endpoint before
applying the plane-permutation exclusion. All three subgroup identities use
the same ambient conjugator. -/
theorem starImage_lt_of_plane_upperSection
    (s : ConjugationSection H UH Z ρ)
    (VH : Subgroup G) (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H VH UH τ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hplane : IsPlaneParabolicGenerated τ eH)
    (g : G) (J Ug Vg X B : Subgroup G)
    (hJ : J = H.map (MulAut.conj g).toMonoidHom)
    (hUg : Ug = UH.map (MulAut.conj g).toMonoidHom)
    (hVg : Vg = VH.map (MulAut.conj g).toMonoidHom)
    (hVgH : Vg ≤ H) (hUHJ : UH ≤ J) (hZ : Nat.card Z = 2)
    (hspan : Vg = conjugateSpanBy X J)
    (hgen : J = conjugateSpanBy UH J ⊔ B)
    (hedge : ⁅B, X⁆ ≤ Ug) (hnoncentral : ¬ ⁅J, Vg⁆ ≤ Ug) :
    Source.starImage H Ug < Source.starImage H Vg := by
  subst J Ug Vg
  exact starImage_lt_of_upper_no_rank_one s _ _ _ X B _ (t.conjugate (MulAut.conj g))
    hVgH hUHJ hZ hspan hgen hedge hnoncentral
    (fun a => PlanePermutation.finrank_ne_one τ eH hplane ((starEquiv (MulAut.conj g) H).symm a))
/-- The strict actor inclusion from the index-two source seed, its marked
plane stabilizer, and the specified endpoint conjugator. The permutation
module premise, endpoint module generation and noncentrality are transported
or proved here. Normal generation by U_H remains the explicit 13.8.18 input. -/
theorem starImage_lt_of_plane_seed
    (s : ConjugationSection H UH Z ρ)
    (VH : Subgroup G) (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H VH UH τ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (X : Subgroup G) (hXV : X ≤ VH) (hspan : VH = conjugateSpanBy X H)
    (hindex : UH.relIndex X = 2)
    (P : Submodule (ZMod 2) ChiefFactors.NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hparabolic : ∀ a : H, eH (QuotientGroup.mk' (pCore 2 H) a) ∈
      BinaryLinear.parabolic P → (a : G) ∈ normalizer (X : Set G))
    (g : G) (J Ug Vg B : Subgroup G)
    (hJ : J = H.map (MulAut.conj g).toMonoidHom)
    (hUg : Ug = UH.map (MulAut.conj g).toMonoidHom)
    (hVg : Vg = VH.map (MulAut.conj g).toMonoidHom)
    (hVgH : Vg ≤ H) (hUHJ : UH ≤ J) (hZ : Nat.card Z = 2)
    (hgen : J = conjugateSpanBy UH J ⊔ B)
    (hedge : ⁅B, X.map (MulAut.conj g).toMonoidHom⁆ ≤ Ug)
    (hnoncentral : ¬ ⁅H, VH⁆ ≤ UH) :
    Source.starImage H Ug < Source.starImage H Vg := by
  apply starImage_lt_of_plane_upperSection s VH τ t eH
    (t.planeGenerated_of_index_two_seed eH X hXV hspan hindex P hP hparabolic)
    g J Ug Vg (X.map (MulAut.conj g).toMonoidHom) B hJ hUg hVg hVgH hUHJ hZ
  · rw [hVg, hJ, hspan]
    exact CriticalGeometry.map_conjugateSpan X H _
  · exact hgen
  · exact hedge
  · intro hc
    rw [hJ, hVg, hUg, ← map_commutator] at hc
    exact hnoncentral ((map_le_map_iff_of_injective (MulAut.conj g).injective).mp hc)

end Strict
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
