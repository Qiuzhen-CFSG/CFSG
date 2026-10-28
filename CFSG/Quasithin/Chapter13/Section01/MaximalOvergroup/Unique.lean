module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Normalizers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
/-!
# Unique maximal overgroup of the original LT

Inside each maximal two-local H containing L₀T, source 1.2.4 supplies a
normal C-component K containing L₀. The same Ξₚ(L₀) is characteristic in K,
so H normalizes it. Its normalizer is already a maximal two-local; maximality
therefore gives equality. Different canonical primes yield the same actual
normalizer. Universal A/C and the containing-component normality are proved
source inputs, while the whole-orbit bound retains its earlier producer.

Source: Aschbacher--Smith, Lemma 13.1.4(2), printed p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)

variable (hA410 : A410EarlierResult G)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
include h hA36 hA38 hA410 hbound

theorem Hypothesis1311.overgroup_le_radical_normalizer
    {L₀ H : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hH : IsMaximalTwoLocal H) (hLH : L₀ ⊔ (T : Subgroup G) ≤ H)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    H ≤ normalizer (XiP p L₀ : Set G) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have h0H : L₀ ≤ H := le_sup_left.trans hLH
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hLH
  have hHT : H ∈ HOver G (T : Set G) := ⟨mem_H_of_isTwoLocal hH.1, hTH⟩
  have hB : L₀.subgroupOf H ∈ L H (T.subtype hTH : Subgroup H) :=
    (mem_LIn_iff_subgroupOf hTH h0H).mp ⟨h0H,hl⟩
  have hTL := radicalLocal_invariant_of_A38 hA38 hl
    (uniqueness_local_quotient_sqtk h.simpleQTKE hl.2.2) hL.2
  have hTB : (T.subtype hTH : Subgroup H) ≤ normalizer (L₀.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact (mem_normalizer_iff.mp (hTL ht) x.val).mp hx
  obtain ⟨J,⟨hJ,hBJ,hJN⟩,_⟩ := lemma_1_2_4_containment_normality_source
    (uniqueness_local_quotient_sqtk h.simpleQTKE hHT.1) (T.subtype hTH) hB hTB
  let K := J.map H.subtype
  have hKH : K ≤ H := map_subtype_le J
  have he : K.subgroupOf H = J := comap_map_eq_self_of_injective H.subtype_injective J
  have hK : K ∈ L G T := (lemma_1_2_6 T hHT).1 ⟨hKH,he.symm ▸ hJ⟩ |>.2
  have hLK : L₀ ≤ K := by
    simpa only [map_subgroupOf_eq_of_le h0H] using map_mono (f := H.subtype) hBJ
  have hKn : (K.subgroupOf H).Normal := he.symm ▸ hJN
  have hN := (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  let := h.radical_characteristic_in_overgroup_of_orbit_bound hA36 hA38 hA410 hbound
    hL hK hLK ho hd
  have hn := hN.trans (normalizer_le_normalizer_characteristic_image K ((XiP p L₀).subgroupOf K))
  simpa only [map_subgroupOf_eq_of_le ((XiP_le p L₀).trans hLK)] using hn

/-- The original component and Sylow subgroup have a unique maximal
local overgroup, identified using any canonical odd radical. -/
theorem Hypothesis1311.radical_normalizer_unique_of_orbit_bound
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    IsMaximalTwoLocal (normalizer (XiP p L₀ : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (XiP p L₀ : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (XiP p L₀ : Set G) := by
  obtain ⟨hm,hl⟩ := h.radical_normalizer_maximal_of_orbit_bound hA36 hA38
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D)) hA410 hbound hL ho hd
  refine ⟨hm,hl,fun H hH hLH => ?_⟩
  have hHN := h.overgroup_le_radical_normalizer hA36 hA38 hA410 hbound hL hH hLH ho hd
  exact le_antisymm hHN (hH.2 hm.1 hHN)

/-- Canonical primes give the same actual normalizer, with no prime selection. -/
theorem Hypothesis1311.radical_normalizer_eq_of_orbit_bound
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q)
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hdq : q ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    normalizer (XiP p L₀ : Set G) = normalizer (XiP q L₀ : Set G) := by
  obtain ⟨hm,hl,_⟩ := h.radical_normalizer_unique_of_orbit_bound hA36 hA38 hA410 hbound hL hp hdp
  exact (h.radical_normalizer_unique_of_orbit_bound hA36 hA38 hA410 hbound hL hq hdq).2.2 _ hm hl

end CFSG.Quasithin.Chapter13.Section01
