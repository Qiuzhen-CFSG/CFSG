module
public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Quotient fixed vectors in the pure-line centralizer

The line in its own centralizer is central. Characteristic two therefore
passes to the literal central quotient. The image of a local Sylow subgroup
contains the quotient two-core, so its centralizer lies in that core.
Lifting through the central two-group kernel puts every Sylow-fixed vector
modulo the line, and all its local conjugates, in the original two-core.

A normal subgroup of a finite two-group has a nontrivial central element.
Applied in the quotient of the local Sylow subgroup, this also supplies an
actual fixed-vector lift outside the line in each invariant factor.
The original offender application is in NonFFSourceDoubledBinaryPureCore.
Source: Aschbacher–Smith, A.1.8 and the quotient step of 7.6.1,
printed pp.21,702, refs/quasithin.pdf. Source 7.7.2 remains an explicit input;
no property of an arbitrary involution centralizer is asserted.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCore
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem line_central (Z : Subgroup G) :
    Z.subgroupOf (centralizer (Z : Set G)) ≤ center (centralizer (Z : Set G)) := by
  intro z hz
  exact mem_center_iff.mpr fun c => Subtype.ext (c.property z hz).symm

instance line_normal (Z : Subgroup G) :
    (Z.subgroupOf (centralizer (Z : Set G))).Normal :=
  ⟨by
    intro z hz c
    have he := mem_center_iff.mp (line_central Z hz) c
    simpa only [he,mul_inv_cancel_right] using hz⟩

@[expose] def fixedModuloLine (Z A S : Subgroup G) : Subgroup G :=
  let C := centralizer (Z : Set G)
  let : (Z.subgroupOf C).Normal := line_normal Z
  (centralizerModulo (A.subgroupOf C) (S.subgroupOf C) (Z.subgroupOf C)).map C.subtype

omit [Finite G] in
theorem mem_fixedModuloLine (Z A S : Subgroup G) (hAC : A ≤ centralizer (Z : Set G))
    (hSC : S ≤ centralizer (Z : Set G)) (x : G) :
    x ∈ fixedModuloLine Z A S ↔ x ∈ A ∧ ∀ s ∈ S, ⁅s,x⁆ ∈ Z := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨ha,hc⟩ := mem_centralizerModulo_iff.mp hx
    exact ⟨ha,fun s hs => hc ⟨s,hSC hs⟩ hs⟩
  · rintro ⟨ha,hc⟩
    exact ⟨⟨x,hAC ha⟩,mem_centralizerModulo_iff.mpr ⟨ha,fun s hs => hc s hs⟩,rfl⟩

theorem fixedModuloLine_le_core (Z A S : Subgroup G)
    (hpZ : IsPGroup 2 Z)
    (hc : centralizer (pCore 2 (centralizer (Z : Set G)) : Set (centralizer (Z : Set G))) ≤
      pCore 2 (centralizer (Z : Set G)))
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype = S) :
    fixedModuloLine Z A S ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  let C := centralizer (Z : Set G)
  let N := Z.subgroupOf C
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact hpZ.comap_subtype
  have hchar := q.centralizer_pCore_le_of_surjective_centralKernel hq
    (by rw [QuotientGroup.ker_mk']; exact line_central Z) hc
  let Pq := P.mapSurjective (f := q) hq
  have hSP : S.subgroupOf C = P := by
    rw [← hP]
    exact comap_map_eq_self_of_injective C.subtype_injective _
  rintro _ ⟨x,hx,rfl⟩
  have hxq : q x ∈ centralizer ((Pq : Subgroup (C ⧸ N)) : Set (C ⧸ N)) := by
    change q x ∈ centralizer ((P : Subgroup C).map q : Set (C ⧸ N))
    rw [← hSP]
    exact hx.2
  have hxc := hchar ((centralizer_le (pCore_isPGroup.le_sylow_of_normal Pq)) hxq)
  have hxcore : x ∈ pCore 2 C := by
    rw [← q.comap_pCore_of_ker_isPGroup hq hk]
    exact hxc
  exact mem_map_of_mem C.subtype hxcore


/-- A Sylow-invariant subgroup escaping the central line has a nonzero
fixed vector modulo that line, with an actual lift in the same subgroup. -/
theorem exists_fixedModuloLine_outside
    (Z A S : Subgroup G) (hpS : IsPGroup 2 S)
    (hAS : A ≤ S) (hSN : S ≤ normalizer (A : Set G))
    (hSC : S ≤ centralizer (Z : Set G)) (hAZ : ¬ A ≤ Z) :
    ∃ x ∈ fixedModuloLine Z A S, x ∉ Z := by
  let N := Z.subgroupOf S
  let R := A.subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hSC.trans (Subgroup.centralizer_le_normalizer _))
  let : R.Normal := normal_subgroupOf_of_le_normalizer hSN
  let q := QuotientGroup.mk' N
  let B := R.map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hB : B ≠ ⊥ := by
    intro he
    have hk : R ≤ q.ker := (Subgroup.map_eq_bot_iff R).mp he
    apply hAZ
    intro a ha
    exact (QuotientGroup.eq_one_iff (N := N) (⟨a,hAS ha⟩ : S)).mp
      (hk (show (⟨a,hAS ha⟩ : S) ∈ R from ha))
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  let : Fact (IsPGroup 2 (S ⧸ N)) := ⟨hpS.to_quotient N⟩
  obtain ⟨b,hb,hbc⟩ := exists_nontrivial_center_mem_normal (p := 2) B
  obtain ⟨a,ha,hab⟩ := b.property
  have haz : (a : G) ∉ Z := by
    intro hz
    apply hb
    apply Subtype.ext
    rw [← hab]
    exact (QuotientGroup.eq_one_iff a).mpr hz
  refine ⟨a,(mem_fixedModuloLine Z A S (hAS.trans hSC) hSC a).mpr ⟨ha,?_⟩,haz⟩
  intro s hs
  have he : q ⁅(⟨s,hs⟩ : S),a⁆ = 1 := by
    rw [map_commutatorElement,hab,commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp hbc (q ⟨s,hs⟩)
  exact (QuotientGroup.eq_one_iff (N := N) ⁅(⟨s,hs⟩ : S),a⁆).mp he

/-- Both fixed-space seeds and all their local conjugates lie in the
centralizer core under the source characteristic-two hypothesis. -/
theorem fixedModuloLine_closure_le_core (Z A S B : Subgroup G)
    (hpZ : IsPGroup 2 Z)
    (hc : centralizer (pCore 2 (centralizer (Z : Set G)) : Set (centralizer (Z : Set G))) ≤
      pCore 2 (centralizer (Z : Set G)))
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype = S)
    (hBC : B ≤ centralizer (Z : Set G)) :
    conjugateSpanBy (fixedModuloLine Z A S) B ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  apply conjugateSpanBy_le (fixedModuloLine_le_core Z A S hpZ hc P hP)
  exact hBC.trans ((centralizer (Z : Set G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCore
