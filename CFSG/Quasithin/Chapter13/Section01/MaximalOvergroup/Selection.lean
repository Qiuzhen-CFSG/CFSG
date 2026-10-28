module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Unique
/-!
# The original maximal counterexample selected in 13.1.7

If the faithful nonquasisimple family is nonempty, select a containing
maximal local K. Its normalizer is the unique maximal two-local over the
original L₀T and is also the normalizer of an actual nontrivial canonical
odd radical. All subgroup inclusions and the same ambient Sylow subgroup
are retained. This is the counterexample setup, not its later elimination.

Source: Aschbacher--Smith, 13.1.4(2) and the setup of 13.1.7, pp.867--868.
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

theorem Hypothesis1311.exists_maximal_counterexample_of_orbit_bound
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      K ∈ nonquasisimpleFaithful T ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      (∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (K : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        XiP p L₀ = XiP p K ∧
        normalizer (K : Set G) = normalizer (XiP p L₀ : Set G) := by
  obtain ⟨K,hK,hLK,hf,_hTK,p,hp,ho,hp3,hd,hne,hn,hKL⟩ :=
    h.exists_normal_radical_of_orbit_bound hA36 hA38 hA410 hbound hL
  let : Fact p.Prime := ⟨hp⟩
  have he := h.radical_eq_of_overgroup_of_orbit_bound hA36 hA38 hA410 hbound
    hL hK.1 hLK ho hd
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have hshape := (XiP_oddQuotient_of_A36 hA36 hl
    (uniqueness_local_quotient_sqtk h.simpleQTKE hl.2.2) hL.2 ho hd).2
  have hdK := prime_dvd_fitting_of_normal_radical ((XiP_le p L₀).trans hLK) hn hshape
  have hNK := (h.maximal_radical_normalizer_data hA36 hA38
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D)) hK hKL.2 ho hdK).1
  rw [← he] at hNK
  obtain ⟨hm,hl,hunique⟩ :=
    h.radical_normalizer_unique_of_orbit_bound hA36 hA38 hA410 hbound hL ho hd
  rw [← hNK] at hm hl hunique
  exact ⟨K,hK,hLK,hf,hKL,hm,hl,hunique,p,hp,ho,hp3,hd,hne,he,hNK⟩

end CFSG.Quasithin.Chapter13.Section01
