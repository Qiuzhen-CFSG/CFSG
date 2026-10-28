module
public import Theory.ElementaryAbelian.Basic
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCountCertificates
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryProducts
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCertificate

/-!
# Genuine involution-class counts in native Held elementary subgroups

The actual subgroup supplies a multiplicatively closed compatible vertex set.
The checked coverage and product-sensitive count certificates therefore apply
to its genuine Held conjugacy classes. No subgroup enumeration is an input.
Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Held.OrdinaryElementary
open NativeCoverage LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private theorem native_count_spectrum (E : Subgroup He) [IsElementaryAbelian 2 E]
    (hEP : E ≤ representative) {n : ℕ} (hE : Nat.card E = n) (hn : n=16 ∨ n=32) :
    allowedCount n (Nat.card {x : E // IsConj a (x : He)}) := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (native v).val ∈ E)
  have hs (v : Fin 192) : v∈s ↔ (native v).val∈E := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
  have hcover (x : E) : ∃v,(native v).val=x.val := by
    have hp : (⟨x.val,hEP x.property⟩ : representative)^2=1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian x.val x.property
    obtain ⟨v,hv⟩ := vertex_of_square _ hp
    exact ⟨v,congrArg Subtype.val hv⟩
  have hninj : Function.Injective (fun v => (native v).val) :=
    representative.subtype_injective.comp native_injective
  let f : s → E := fun v => ⟨(native v.val).val,(hs _).mp v.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      exact Subtype.ext (hninj (congrArg (fun x : E => x.val) he))
    · intro x
      obtain ⟨v,hv⟩ := hcover x
      exact ⟨⟨v,(hs v).mpr (hv.symm ▸ x.property)⟩,Subtype.ext hv⟩
  have hcard : s.card=n := by
    rw [←Nat.card_eq_finsetCard]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).trans hE
  have h0 : 0∈s := by
    apply (hs 0).mpr
    change (normalForm 0).val ∈ E
    rw [Held.InvolutionFixedData.Coverage.normalForm_zero]
    exact E.one_mem
  have hcomm : ∀v∈s,∀w∈s,compatible v w=true := by
    intro v hv w hw
    apply native_compatible
    apply Subtype.ext
    exact setLike_mul_comm ((hs v).mp hv) ((hs w).mp hw)
  have hcoset : ∀v w,w∈s → compatible v w=true → (productVertex v w∈s ↔ v∈s) := by
    intro v w hw hc
    rw [hs,hs,native_product v w hc]
    change (native v).val*(native w).val∈E ↔ (native v).val∈E
    exact E.mul_mem_cancel_right ((hs w).mp hw)
  have hlarge : 16≤s.card := by rcases hn with rfl | rfl <;> omega
  obtain ⟨k,hk⟩ := clique_coverage s hlarge hcomm
  have hsub : s⊆candidateSet k := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk v hv⟩
  have hcount : allowedCount n (markedCount s) := by
    rcases hn with rfl | rfl
    · exact candidate_count16 k s hcard h0 hsub hcomm hcoset
    · exact candidate_count32 k s hcard h0 hsub hcomm hcoset
  have hclass (v : Fin 192) : marked v=true ↔ IsConj a (native v).val := classA_iff _
  let A := s.filter (fun v => marked v=true)
  let g : A → {x : E // IsConj a (x : He)} := fun v =>
    ⟨⟨(native v.val).val,(hs _).mp (Finset.mem_filter.mp v.property).1⟩,
      (hclass _).mp (Finset.mem_filter.mp v.property).2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro v w he
      exact Subtype.ext (hninj (congrArg (fun z : {x : E // IsConj a (x : He)} => z.val.val) he))
    · intro x
      obtain ⟨v,hv⟩ := hcover x.val
      refine ⟨⟨v,Finset.mem_filter.mpr ⟨(hs v).mpr (hv.symm ▸ x.val.property),?_⟩⟩,?_⟩
      · exact (hclass v).mpr (hv.symm ▸ x.property)
      · exact Subtype.ext (Subtype.ext hv)
  have he : markedCount s = Nat.card {x : E // IsConj a (x : He)} := by
    change A.card = _
    rw [←Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.ofBijective g hg)
  rwa [he] at hcount

/-- Every native elementary subgroup of order32 has exactly six or ten
involutions in the actual Held 2A class. -/
theorem card_classA_thirtyTwo_of_le (E : Subgroup He) [IsElementaryAbelian 2 E]
    (hE : Nat.card E=32) (hEP : E≤representative) :
    Nat.card {x : E // IsConj a (x : He)}=6 ∨
      Nat.card {x : E // IsConj a (x : He)}=10 := by
  simpa only [allowedCount,show (32:ℕ)≠16 by decide,↓reduceIte] using
    native_count_spectrum E hEP hE (Or.inr rfl)

/-- The actual Held 2A count on a native elementary order16 subgroup belongs
to the proved five-value list. -/
theorem card_classA_sixteen_of_le (E : Subgroup He) [IsElementaryAbelian 2 E]
    (hE : Nat.card E=16) (hEP : E≤representative) :
    Nat.card {x : E // IsConj a (x : He)}=0 ∨
      Nat.card {x : E // IsConj a (x : He)}=2 ∨
      Nat.card {x : E // IsConj a (x : He)}=4 ∨
      Nat.card {x : E // IsConj a (x : He)}=6 ∨
      Nat.card {x : E // IsConj a (x : He)}=12 := by
  simpa only [allowedCount,↓reduceIte] using
    native_count_spectrum E hEP hE (Or.inl rfl)

end Held.OrdinaryElementary
