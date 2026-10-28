module
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.Elementary
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Detection
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Generators
import Mathlib.Tactic.FinCases
/-!
# Two-letter separation in the fixed J₃ centralizer

The certified `CRep` chain exhausts C. A kernel check shows that only the
identity fixes letters 0 and 1, hence these letters separate elements of C.
The cached elementary and local generators are identified with the unchanged
model generators, allowing subsequent certificates to avoid long word expansion.

Source: GLS 3, Table 5.3h, p.269; the retained degree-6156 ATLAS J₃ action.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open OrderCertificate CentralizerCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

@[expose] public def fastBasis : Fin 4 → Equiv.Perm (Fin 6156) :=
  ![AffineCertificate.G3, AffineCertificate.G2, AffineCertificate.G1, AffineCertificate.G0]
public theorem fastBasis_eq (j : Fin 4) : fastBasis j = embedding (elementaryGenerator j) := by
  fin_cases j <;> simp only [fastBasis,
    AffineCertificate.G0_eq, AffineCertificate.G1_eq, AffineCertificate.G2_eq,
    AffineCertificate.G3_eq] <;> rfl
@[expose] public def fastElementary (i : Fin 16) : Equiv.Perm (Fin 6156) :=
  evalWord fastBasis (elementaryWord i)
public theorem fastElementary_eq (i : Fin 16) :
    fastElementary i = embedding (elementaryElement i) := by
  suffices ∀ w : List (Fin 4), evalWord fastBasis w =
      embedding (evalWord elementaryGenerator w) from this _
  intro w
  induction w with
  | nil => exact (map_one embedding).symm
  | cons j w ih => simp only [evalWord, map_mul, fastBasis_eq, ih]

public theorem rep_mem (r : CIndex) : CRep r ∈ C0H := by
  exact C0H.mul_mem (C0Rep_mem _) (C1H_le (C1H.mul_mem (C1Rep_mem _)
    (C2H_le (C2H.mul_mem (C2Rep_mem _) (C3H_le (C3H.mul_mem (C3Rep_mem _)
      (C4H_le (C4H.mul_mem (C4Rep_mem _) (C5H_le (C5Rep_mem _))))))))))

private theorem pair_fixer : ∀ r : CIndex,
    CRep r 0 = 0 → CRep r 1 = 1 → r = (0,0,0,0,0,0) := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

public theorem eq_of_pair {g h : Equiv.Perm (Fin 6156)} (hg : g ∈ C0H) (hh : h ∈ C0H)
    (h0 : g 0 = h 0) (h1 : g 1 = h 1) : g = h := by
  obtain ⟨r, hr⟩ := CRep_complete ⟨h⁻¹ * g, C0H.mul_mem (C0H.inv_mem hh) hg⟩
  change h⁻¹ * g = CRep r at hr
  have hx (x : Fin 6156) (he : g x = h x) : CRep r x = x := by
    rw [← hr]
    change h.symm (g x) = x
    rw [he, Equiv.symm_apply_apply]
  have hz := pair_fixer r (hx 0 h0) (hx 1 h1)
  subst r
  have he : CRep (0,0,0,0,0,0) = 1 := rfl
  rw [he] at hr
  exact (inv_mul_eq_one.mp hr).symm

public theorem model_mem (g : Model) (hg : g ∈ localFamily 0) : embedding g ∈ C0H := by
  rw [C0H_eq_map]
  exact mem_map.mpr ⟨g, hg, rfl⟩
public theorem rep_complete (g : Model) (hg : g ∈ localFamily 0) :
    ∃ r, embedding g = CRep r := CRep_complete ⟨embedding g, model_mem g hg⟩

public theorem word_mem {n : Nat} (H : Subgroup (Equiv.Perm (Fin 6156)))
    (f : Fin n → Equiv.Perm (Fin 6156)) (hf : ∀ i, f i ∈ H) (w : List (Fin n)) :
    evalWord f w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hf i) ih

@[expose] public def fastAffine : Fin 7 → Equiv.Perm (Fin 6156) :=
  ![AffineCertificate.G0, AffineCertificate.G1, AffineCertificate.G2,
    AffineCertificate.G3, AffineCertificate.G4, AffineCertificate.G5, AffineCertificate.G6]
public theorem fastAffine_eq (i : Fin 7) : fastAffine i = embedding (affineGenerator i) := by
  fin_cases i <;> simp only [fastAffine, AffineCertificate.G0_eq, AffineCertificate.G1_eq,
    AffineCertificate.G2_eq, AffineCertificate.G3_eq, AffineCertificate.G4_eq,
    AffineCertificate.G5_eq, AffineCertificate.G6_eq] <;> rfl
public theorem fastAffine_mem (i : Fin 7) : fastAffine i ∈ (localFamily 1).map embedding := by
  rw [fastAffine_eq]
  exact mem_map.mpr ⟨affineGenerator i, affineGenerator_mem i, rfl⟩

@[expose] public def fastThompson : Fin 8 → Equiv.Perm (Fin 6156) :=
  ![ThompsonCertificate.g1Perm, ThompsonCertificate.g5Perm, ThompsonCertificate.g4Perm,
    ThompsonCertificate.g3Perm, ThompsonCertificate.g2Perm, ThompsonCertificate.g0Perm,
    ThompsonCertificate.g8Perm, ThompsonCertificate.g6Perm]
public theorem fastThompson_eq (i : Fin 8) :
    fastThompson i = embedding (thompsonNormalizerGenerator i) := by
  have h0 := congrArg embedding ThompsonCertificate.g0_eq
  have h1 := congrArg embedding ThompsonCertificate.g1_eq
  have h2 := congrArg embedding ThompsonCertificate.g2_eq
  have h3 := congrArg embedding ThompsonCertificate.g3_eq
  have h4 := congrArg embedding ThompsonCertificate.g4_eq
  have h5 := congrArg embedding ThompsonCertificate.g5_eq
  have h6 := congrArg embedding ThompsonCertificate.g6_eq
  have h8 := congrArg embedding ThompsonCertificate.g8_eq
  fin_cases i
  · exact h1
  · exact h5
  · exact h4
  · exact h3
  · exact h2
  · exact h0
  · exact h8
  · exact h6
public theorem fastThompson_mem (i : Fin 8) :
    fastThompson i ∈ (localFamily 2).map embedding := by
  rw [fastThompson_eq]
  exact mem_map.mpr ⟨thompsonNormalizerGenerator i, thompsonNormalizerGenerator_mem i, rfl⟩

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
