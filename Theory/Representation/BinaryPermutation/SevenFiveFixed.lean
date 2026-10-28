module
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.Representation.BinaryOffender.Basic
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension

/-!
# Sylow-fixed vectors control the same A₅ inside the deleted A₇ module

A Sylow-normalized A₅ fixes exactly two of the seven letters. Their binary
indicator lies in the deleted module and is fixed by every permutation
normalizing that A₅. Fixing the whole Sylow-fixed space preserves this pair,
and therefore normalizes its full alternating pointwise fixer, the original A₅.

The second theorem lifts the conclusion through an actual two-kernel.
The A₅-section theorem identifies the literal image; perfectness and the
Sylow containment of the kernel lift its normalizer to the original subgroup.

Source: Aschbacher–Smith 5.1.13, printed p.637, the six-dimensional
alternative in the Cartan centralization argument.
-/

public noncomputable section
open Subgroup MulAction Equiv Representation Representation.BinaryOffender
namespace BinaryPermutation.SevenFiveFixed
abbrev A7 := alternatingGroup (Fin 7)
abbrev S7 := Perm (Fin 7)

private theorem normalizer_preserves_fixed (B : Subgroup S7) {g : S7}
    (hg : g ∈ normalizer (B : Set S7)) (i : Fin 7) :
    g i ∈ fixedPoints B (Fin 7) ↔ i ∈ fixedPoints B (Fin 7) := by
  have forward (g : S7) (hg : g ∈ normalizer (B : Set S7)) (i : Fin 7)
      (hi : i ∈ fixedPoints B (Fin 7)) : g i ∈ fixedPoints B (Fin 7) := by
    intro b
    have hb := (mem_normalizer_iff''.mp hg b.val).mp b.property
    have hh := hi ⟨g⁻¹ * b.val * g,hb⟩
    change (g⁻¹ * b.val * g) i = i at hh
    have he := congrArg g hh
    change b.val (g i) = g i
    change g (g.symm (b.val (g i))) = g i at he
    simpa only [g.apply_symm_apply] using he
  exact ⟨fun hi => by simpa using forward g⁻¹ (inv_mem hg) (g i) hi, forward g hg i⟩

/-- Fixing the Sylow-fixed part of the deleted seven-letter module preserves
any A₅ subgroup normalized by that Sylow. The actual A₅ is retained. -/
theorem fixed_kernel_le_normalizer_five
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSB : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (P : Subgroup S7)
    (hPB : P ≤ normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set S7))
    {g : S7}
    (hg : ∀ v ∈ fixedSpace (coreRepresentation (Fin 7)) P,
      coreRepresentation (Fin 7) g v = v) :
    g ∈ normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set S7) := by
  classical
  let C := B.map (alternatingGroup (Fin 7)).subtype
  have hfixed : fixedPoints C (Fin 7) = fixedPoints B (Fin 7) := by
    ext i
    constructor
    · intro hi b
      exact hi ⟨b.val.val,mem_map_of_mem _ b.property⟩
    · intro hi x
      obtain ⟨b,hb,he⟩ := x.property
      change x.val i = i
      rw [←he]
      exact hi ⟨b,hb⟩
  obtain ⟨i,j,hij,hset⟩ := Set.ncard_eq_two.mp
    (Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B e S hSB)
  obtain ⟨i',j',hne,hB⟩ :=
    Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e S hSB
  -- Use the support of the actual fixed pair, so every normalizer preserves it.
  let v : core (Fin 7) := ⟨Pi.single i (1 : ZMod 2) + Pi.single j 1, by
    norm_num [mem_core,Finset.sum_add_distrib]
    decide⟩
  have hv (k : Fin 7) : v.val k ≠ 0 ↔ k ∈ fixedPoints C (Fin 7) := by
    rw [hfixed,hset]
    by_cases hki : k = i
    · subst k; simp [v,hij]
    by_cases hkj : k = j
    · subst k; simp [v,Ne.symm hij]
    simp [v,hki,hkj]
  have hvP : v ∈ fixedSpace (coreRepresentation (Fin 7)) P := by
    intro p
    apply Subtype.ext
    ext k
    change v.val (p.val.symm k) = v.val k
    have hh := normalizer_preserves_fixed C (hPB p.property) (p.val.symm k)
    rw [p.val.apply_symm_apply,←hv,←hv] at hh
    have bits : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
    exact bits _ _ hh.symm
  have hgp : ∀ k, g k ∈ fixedPoints B (Fin 7) ↔ k ∈ fixedPoints B (Fin 7) := by
    intro k
    have hh := congrArg (fun w : core (Fin 7) => w.val (g k)) (hg v hvP)
    change v.val (g.symm (g k)) = v.val (g k) at hh
    rw [g.symm_apply_apply] at hh
    simp only [←hfixed,←hv,hh]
  -- A₅ is the full alternating pointwise fixer of its fixed pair.
  have hfull : B = fixingSubgroup A7 (fixedPoints B (Fin 7)) := by
    apply le_antisymm
    · intro b hb k
      exact k.property ⟨b,hb⟩
    · intro b hb
      rw [hB]
      intro k
      have hk : k.val ∈ fixedPoints B (Fin 7) := by
        intro x
        have hx : x.val ∈ fixingSubgroup A7 ({i',j'} : Set (Fin 7)) := hB ▸ x.property
        exact hx ⟨k.val,k.property⟩
      exact hb ⟨k.val,hk⟩
  have hC (x : S7) : x ∈ C ↔ x ∈ alternatingGroup (Fin 7) ∧
      ∀ k ∈ fixedPoints B (Fin 7), x k = k := by
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,fun k hk => hk ⟨b,hb⟩⟩
    · rintro ⟨hx,hfix⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      rw [hfull]
      intro k
      exact hfix k k.property
  apply mem_normalizer_iff.mpr
  intro x
  rw [hC,hC]
  constructor
  · rintro ⟨hx,hxf⟩
    refine ⟨(inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx g,?_⟩
    intro k hk
    have hkg : g.symm k ∈ fixedPoints B (Fin 7) :=
      (hgp (g.symm k)).mp (by simpa using hk)
    change g (x (g.symm k)) = k
    rw [hxf _ hkg,g.apply_symm_apply]
  · rintro ⟨hx,hxf⟩
    refine ⟨?_,?_⟩
    · have hh := (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem
        (g*x*g⁻¹) hx g⁻¹
      convert hh using 1
      group
    · intro k hk
      have hh := hxf (g k) ((hgp k).mpr hk)
      change g (x (g.symm (g k))) = g k at hh
      exact g.injective (by simpa using hh)
end BinaryPermutation.SevenFiveFixed

namespace BinaryPermutation.SevenFiveFixed
variable {G : Type*} [Group G] [Finite G]

/-- The same fixed-space control lifts through a two-kernel to a perfect
subgroup with original two-core quotient A₅. -/
theorem fixed_kernel_normalizes_perfect_preimage
    (f : G →* S7) (hf : IsPGroup 2 f.ker)
    (N : Subgroup G) [N.Normal] (hN : N.map f = alternatingGroup (Fin 7))
    (R : Subgroup G) [Group.IsPerfect R] (hRN : R ≤ N)
    (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) (hPR : (P : Subgroup G) ≤ normalizer (R : Set G))
    {g : G} (hg : ∀ v ∈ fixedSpace (coreRepresentation (Fin 7)) ((P : Subgroup G).map f),
      coreRepresentation (Fin 7) (f g) v = v) : g ∈ normalizer (R : Set G) := by
  let r : N →* A7 := (f.comp N.subtype).codRestrict _
    (by
      intro n
      change f n.val ∈ alternatingGroup (Fin 7)
      rw [←hN]
      exact mem_map_of_mem f n.property)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨n,hn,hx⟩ := (show x.val ∈ N.map f from hN.symm ▸ x.property)
    exact ⟨⟨n,hn⟩,Subtype.ext hx⟩
  let R' := R.subgroupOf N
  let B := R'.map r
  have hmap : B.map (alternatingGroup (Fin 7)).subtype = R.map f := by
    rw [map_map]
    change R'.map (f.comp N.subtype) = R.map f
    rw [←map_map,map_subgroupOf_eq_of_le hRN]
  have hk : IsPGroup 2 (r.subgroupMap R').ker := by
    let j : (r.subgroupMap R').ker →* f.ker :=
      (N.subtype.comp (R'.subtype.comp (r.subgroupMap R').ker.subtype)).codRestrict _ (by
        intro x
        exact congrArg (fun y : B => y.val.val) x.property)
    exact hf.of_injective j (by
      intro x y hxy
      have hh : x.val.val.val = y.val.val.val := congrArg (fun z : f.ker => z.val) hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext hh)))
  let a := subgroupOfEquivOfLe hRN
  let e' := (QuotientGroup.congr (pCore 2 R') (pCore 2 R) a (pCore_map_iso 2 a)).trans e
  let eB : B ≃* alternatingGroup (Fin 5) :=
    alternatingGroup.SevenFiveSection.imageFiveEquiv r R' hk e'
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal N
  have hSB : (S : Subgroup N) ≤ normalizer (R' : Set N) := by
    intro s hs
    have hp : s.val ∈ (P : Subgroup G) := by
      rw [hS] at hs
      exact hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hPR hp) x.val
  have hRB : ((S.mapSurjective hr : Sylow 2 A7) : Subgroup A7) ≤ normalizer (B : Set A7) :=
    (map_mono hSB).trans (R'.le_normalizer_map r)
  have hPB : (P : Subgroup G).map f ≤ normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set S7) := by
    rw [hmap]
    exact (map_mono hPR).trans (R.le_normalizer_map f)
  have hg' := fixed_kernel_le_normalizer_five B eB (S.mapSurjective hr) hRB _ hPB hg
  rw [hmap] at hg'
  have hQ : f.ker ≤ normalizer (R : Set G) := (hf.le_sylow_of_normal P).trans hPR
  have he : normalizer ((R ⊔ f.ker : Subgroup G) : Set G) = normalizer (R : Set G) := by
    have hh := normalizer_perfect_image_comap R f.ker hf hQ
    rwa [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hh := (R.map f).le_normalizer_comap f hg'
  rw [comap_map_eq,he] at hh
  exact hh
end BinaryPermutation.SevenFiveFixed
