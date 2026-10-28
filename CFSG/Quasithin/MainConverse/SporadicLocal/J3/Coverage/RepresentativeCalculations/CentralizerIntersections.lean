module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections.E
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections.U
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections.B

/-!
# The three intersections inside the fixed J₃ involution centralizer

The certified centralizer chain exhausts C. For the two normalizers, a finite
check either expresses a row in four generators of the appropriate local
candidate or gives a basis vector whose conjugate lies outside E or U.
For the centralizer of B, noncommutation with its second generator eliminates
all but sixteen rows, which are identified with the elementary masks.

Source: the concrete route to the maximal two-locals in GLS 3, Table 5.3h,
printed p.269. These containments are inputs to `LocalReduction`, not by
themselves the full ambient-normalizer or local-coverage theorem. All finite
identities are kernel checked in the actual unchanged ATLAS model.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open CentralizerCertificate Intersections
set_option Elab.async false

private theorem mem_of_embedding_mem (g : Model) (H : Subgroup Model)
    (hg : embedding g ∈ H.map embedding) : g ∈ H := by
  obtain ⟨x, hx, he⟩ := mem_map.mp hg
  have h : x = g := Subtype.ext he
  exact h ▸ hx

private theorem conjugation_eq (g : Model) (r : CIndex) (hr : embedding g = CRep r)
    (j : Fin 4) (k : Fin 16)
    (hk : elementaryElement k = (MulAut.conj g) (elementaryGenerator j)) :
    CRep r * fastBasis j * (CRep r)⁻¹ = fastElementary k := by
  have he := congrArg embedding hk.symm
  change embedding (g * elementaryGenerator j * g⁻¹) = embedding (elementaryElement k) at he
  simpa only [map_mul, map_inv, hr, ← fastBasis_eq, ← fastElementary_eq] using he

/-- The part of C normalizing the fixed order-sixteen elementary candidate
lies in the unchanged affine local candidate. -/
public theorem centralizer_inf_normalizer_elementary_le
    (hS : Nat.card sylowCandidate = 128) :
    localFamily 0 ⊓ normalizer (elementaryCandidate : Set Model) ≤ localFamily 1 := by
  rintro g ⟨hg, hn⟩
  obtain ⟨r, hr⟩ := rep_complete g hg
  have hgood : goodE r := by
    by_contra hbad
    have hx := (hn (elementaryGenerator (outsideE r))).mp (elementaryGenerator_mem _)
    obtain ⟨k, hk⟩ := (mem_elementaryCandidate_iff hS _).mp hx
    have hs : ∀ k : Fin 16, supported 15 k := by decide +kernel
    have he := conjugation_eq g r hr (outsideE r) k hk
    rcases exclusionE r hbad k (hs k) with h0 | h1
    · exact h0 (congrArg (fun p : Equiv.Perm (Fin 6156) => p 0) he)
    · exact h1 (congrArg (fun p : Equiv.Perm (Fin 6156) => p 1) he)
  apply mem_of_embedding_mem
  rw [hr]
  exact goodE_mem r hgood

/-- The part of C normalizing the four-group on elementary coordinates 0 and 2
lies in the unchanged Thompson-normalizer candidate. -/
public theorem centralizer_inf_normalizer_representative_two_le
    (hS : Nat.card sylowCandidate = 128) :
    localFamily 0 ⊓ normalizer (elementaryRepresentative 2 : Set Model) ≤ localFamily 2 := by
  rintro g ⟨hg, hn⟩
  obtain ⟨r, hr⟩ := rep_complete g hg
  have hgood : goodU r := by
    by_contra hbad
    have hj : elementaryGenerator (outsideU r) ∈ elementaryRepresentative 2 := by
      rw [← elementarySpan_representative hS]
      exact generator_mem_elementarySpan hS 5 _ (outsideU_supported r)
    have hx := (hn (elementaryGenerator (outsideU r))).mp hj
    obtain ⟨k, hk, he⟩ := (mem_elementaryRepresentative_iff hS 2 _).mp hx
    have heq := conjugation_eq g r hr (outsideU r) k he
    rcases exclusionU r hbad k hk with h0 | h1
    · exact h0 (congrArg (fun p : Equiv.Perm (Fin 6156) => p 0) heq)
    · exact h1 (congrArg (fun p : Equiv.Perm (Fin 6156) => p 1) heq)
  apply mem_of_embedding_mem
  rw [hr]
  exact goodU_mem r hgood

/-- The part of C centralizing the four-group on elementary coordinates 0 and 1
is contained in the fixed elementary candidate. -/
public theorem centralizer_inf_centralizer_representative_one_le
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    localFamily 0 ⊓ centralizer (elementaryRepresentative 1 : Set Model) ≤ elementaryCandidate := by
  rintro g ⟨hg, hc⟩
  obtain ⟨r, hr⟩ := rep_complete g hg
  have hj : elementaryGenerator 1 ∈ elementaryRepresentative 1 :=
    mem_sup_right (mem_zpowers _)
  have he : CRep r * fastBasis 1 = fastBasis 1 * CRep r := by
    have h := congrArg embedding (hc (elementaryGenerator 1) hj).symm
    simpa only [map_mul, hr, ← fastBasis_eq] using h
  have hgood := detectionB r (congrArg (fun p : Equiv.Perm (Fin 6156) => p 0) he)
  have hmem := elementaryElement_mem hS (maskB r)
  have hE := elementaryCandidate_le_localFamily_zero hS hC hmem
  have heq := eq_of_pair (rep_mem r) (model_mem _ hE)
    (by simpa only [fastElementary_eq] using (positiveB r hgood).1)
    (by simpa only [fastElementary_eq] using (positiveB r hgood).2)
  have h : g = elementaryElement (maskB r) := Subtype.ext (hr.trans heq)
  exact h.symm ▸ hmem

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
