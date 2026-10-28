module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Quotient
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch
public import Theory.GroupTheory.PerfectCentralPGroupSplit

/-!
# Recognizing and splitting the five-centralizer quotient

A single involution class with a four-group centralizer gives the proved
Brauer–Suzuki–Wall alternatives A₄ and A₅. The literal centralizer quotient
has order divisible by five, ruling out A₄. Its central kernel of order five
then splits: A₅ is perfect and its Sylow five-subgroups are cyclic, so the
central p-group splitting theorem applies to the actual quotient projection.

The quotient involution data remains to be derived from the 47.1 geometry.
It is not an assumption of the intended 47.2 theorem. In particular merely
having one four-group centralizer does not supply the conjugacy field below.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
This supplies the recognition implication used in place of the q=4 case of
*Finite Group Theory*, second edition, Exercise 16.6, pp.266–267.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent

variable {G : Type*} [Group G] [Finite G]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Local facts about the literal quotient, before recognition or splitting. -/
structure QuotientInvolutionData (E : Subgroup G) (t : G)
    (hEt : E ≤ involutionCentralizer t) where
  conjugate : ∀ u : Quotient E, orderOf u = 2 → IsConj u (rootInQuotient E t hEt)
  centralizer_equiv : Nonempty
    (centralizer ({rootInQuotient E t hEt} : Set (Quotient E)) ≃* DihedralGroup 2)

/-- The remaining local geometry for the whole root-five family. The representative
is allowed to vary in the prescribed ambient involution class. -/
def QuotientInvolutionFamily (t : G) : Prop :=
  ∀ E : Subgroup G, FiveCentralizing t E →
    ∃ u : G, IsConj t u ∧ ∃ hEu : E ≤ involutionCentralizer u,
      Nonempty (QuotientInvolutionData E u hEu)

/-- A₄ is excluded by the remaining factor of five in |C_G(E)/E|. -/
theorem quotient_equiv_of_involutionData (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) (t : G) (ht : orderOf t = 2)
    (hEt : E ≤ involutionCentralizer t) (I : QuotientInvolutionData E t hEt) :
    Nonempty (Quotient E ≃* alternatingGroup (Fin 5)) := by
  have hi := rootInQuotient_order E hE t ht hEt
  let localData : DihedralInvolutionCentralizerHypotheses (Quotient E) 2 := {
    two_le := le_rfl
    z := rootInQuotient E t hEt
    involution := ⟨fun he => by simp [he] at hi, hi ▸ pow_orderOf_eq_one _⟩
    involutions_conjugate := fun u hu =>
      isConj_iff.mp (I.conjugate u (orderOf_eq_prime hu.2 hu.1))
    centralizer_equiv := I.centralizer_equiv }
  obtain ⟨b, _, _, hb⟩ := localData.exists_brauerSuzukiWallHypotheses
  have hb2 : Nat.card b.K = 2 := by simpa using hb
  rcases alternating_four_or_five_of_bsw_card_two b hb2 with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hd := five_dvd_quotient_card hG E hE
    rw [Nat.card_congr e4.toEquiv,
      alternatingGroup.card_of_card_eq_four (by simp)] at hd
    norm_num at hd
  · exact h5

/-- A recognized quotient has a section of its literal central extension.
No Schur-multiplier computation or additional splitting premise is used. -/
theorem exists_section_of_quotient_equiv (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
      (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let f : centralizer (E : Set G) →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = kernel E := by
    ext x
    change e (QuotientGroup.mk' (kernel E) x) = 1 ↔ x ∈ kernel E
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  have hc : f.ker ≤ center (centralizer (E : Set G)) := by
    rw [hk]
    exact kernel_le_center E
  have hp : IsPGroup 5 f.ker := IsPGroup.of_card (n := 1) (by
    rw [hk, kernel_card E hE, pow_one])
  have hcyclic (P : Sylow 5 (alternatingGroup (Fin 5))) : IsCyclic P := by
    apply isCyclic_of_prime_card (p := 5)
    rw [P.card_eq_multiplicity, InvolutionGeometry.card_A5]
    decide +kernel
  exact PerfectCentralCovering.exists_section_of_central_pGroup_kernel f hf hc hp hcyclic

/-- The section gives an actual internal complement, with the original kernel. -/
theorem exists_complement_of_quotient_equiv (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
      (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ ∧
        (kernel E).IsComplement' s.range := by
  obtain ⟨s, hs⟩ := exists_section_of_quotient_equiv E hE e
  let f : centralizer (E : Set G) →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))
  have hfs (a : alternatingGroup (Fin 5)) : f (s a) = a :=
    DFunLike.congr_fun hs a
  have hk (x : centralizer (E : Set G)) : f x = 1 ↔ x ∈ kernel E := by
    change e (QuotientGroup.mk' (kernel E) x) = 1 ↔ x ∈ kernel E
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  refine ⟨s, hs, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · rw [disjoint_def]
    rintro x hx ⟨a, rfl⟩
    have ha : a = 1 := (hfs a).symm.trans ((hk _).mpr hx)
    rw [ha, map_one]
  · apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_mul.mpr ⟨x * (s (f x))⁻¹, ?_, s (f x), ⟨f x, rfl⟩, ?_⟩
    · apply (hk _).mp
      rw [map_mul, map_inv, hfs, mul_inv_cancel]
    · group

/-- The recognition implication supplies a genuine section for its actual consumer. -/
theorem exists_section_of_involutionData (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) (t : G) (ht : orderOf t = 2)
    (hEt : E ≤ involutionCentralizer t) (I : QuotientInvolutionData E t hEt) :
    ∃ e : Quotient E ≃* alternatingGroup (Fin 5),
      ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
        (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ := by
  obtain ⟨e⟩ := quotient_equiv_of_involutionData hG E hE t ht hEt I
  obtain ⟨s, hs⟩ := exists_section_of_quotient_equiv E hE e
  exact ⟨e, s, hs⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
