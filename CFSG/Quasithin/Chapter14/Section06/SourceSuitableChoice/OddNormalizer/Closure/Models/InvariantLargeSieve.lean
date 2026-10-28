module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.F918
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.EvenSource
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OrderSieve
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The invariant large-prime F.9.18 sieve

Pass the actual invariant component to its faithful almost-simple section.
The F.9.18 rank-one rows give cyclic odd subgroups, the even linear and G₂
rows contradict the intrinsic Frattini action, and the small binary,
alternating and Mathieu rows cannot contain the required prime square.
The sole surviving symplectic row has cyclic complement automizer. The
canonical quotient maps transport that conclusion back to the original
normalizer action on the odd complement, including central-cover cases.

StrictSource applies this at five to the original exchanged factors,
whose automizer is noncyclic. No A.3.15 case-existence assumption or later
14.6.15 conclusion is used. The earlier Theorems A and C are the checked
known-simple source theorems.

Source: Aschbacher--Smith 1.3.4, pp.510--511; F.9.18(4), pp.325--326;
comparison in the proof of original 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding Chapter1.XiEmbedding.InvariantLarge
open Chapter13.Section08.Components.Models

/-- On the literal F.9.18 list, the large-prime intrinsic pair has cyclic
complement automizer. The full symplectic group is its only surviving row. -/
theorem large_f918_automizer_cyclic
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q] [Group.IsPerfect Q]
    {D B : Subgroup J} [D.Normal] {S : Sylow 2 J} {p : ℕ}
    (eQ : Q ⧸ center Q ≃* D)
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hC : centralizer (D : Set J) = ⊥)
    (hm : F918Models Q) : IsCyclic (automizer S B) := by
  let : IsSimpleGroup D := hA.simple
  let : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
  rcases hm with ⟨hm,_⟩ | hm
  · cases hm with
    | bender hm =>
      exact (A315Source.not_rank_one hA hB (Group.IsPerfect.not_isMulCommutative D)
        (hm.of_mulEquiv eQ.symm)).elim
    | linear_three n hn hm =>
      have hd := hm.of_mulEquiv eQ.symm
      by_cases hn1 : n = 1
      · exact (A315Source.not_binary_linear hA hB 3 (Or.inl rfl)
          (by simpa only [hn1,pow_one] using hd)).elim
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hd
        exact (A315Source.not_linear_even hA hB hF (by omega) e).elim
    | symplectic n hn hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      by_cases hn2 : 2 ≤ n
      · have ej := (eQ.symm.trans e).trans
          (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn2)
        exact (A315Source.symplectic_alternative eQ hA hB hC hF hn2 ej).2.2
      · have hn1 : n = 1 := by omega
        have htwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
        exact (A315Source.not_alternating hA hB 6 (by omega)
          ⟨(eQ.symm.trans e).trans
            (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix htwo)⟩).elim
    | g2 n hn hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      by_cases hn2 : 2 ≤ n
      · exact (A315Source.not_g2_even hA hB hF hn2
          ((eQ.symm.trans e).trans
            (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hF))).elim
      · have hn1 : n = 1 := by omega
        have htwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
        exact (A315Source.not_g2_derived hA hB
          ⟨(eQ.symm.trans e).trans
            (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv (Atlas.G2.binaryFieldEquiv htwo))⟩).elim
    | linear_four hm =>
      exact (A315Source.not_binary_linear hA hB 4 (by tauto) (hm.of_mulEquiv eQ.symm)).elim
    | linear_five hm =>
      exact (A315Source.not_binary_linear hA hB 5 (by tauto) (hm.of_mulEquiv eQ.symm)).elim
    | alternating_seven he =>
      exact (A315Source.not_alternating hA hB 7 (by omega) (he.map (eQ.symm.trans ·))).elim
  · have he : Nonempty (D ≃* Sporadic.Mathieu.M22) := by
      rcases hm with ⟨e⟩ | ⟨_,_,⟨e⟩⟩
      · obtain ⟨e⟩ := e
        let ec := QuotientGroup.congr (center Q) (center Sporadic.Mathieu.M22) e
          (Subgroup.center_map_equiv e)
        let ez := (QuotientGroup.quotientMulEquivOfEq Sporadic.Mathieu.m22_center_eq_bot).trans
          QuotientGroup.quotientBot
        exact ⟨(eQ.symm.trans ec).trans ez⟩
      · exact ⟨eQ.symm.trans e⟩
    exact (A315Source.not_mathieu hA hB .m22 (by tauto) he).elim

/-- F.9.18 forces a cyclic automizer for a relatively normal invariant
component at every prime above three, with the actual Sylow input retained. -/
theorem invariant_large_f918_automizer_cyclic
    {G : Type*} [Group G] [Finite G] {p : ℕ} {T X P J L : Subgroup G}
    (h : SylowInput KnownSimple.IsKnownSimple p T X P J L) (hp : 3 < p)
    (hm : F918Models (XiQuotient L)) : IsCyclic (automizer T P) := by
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  let : (SourceTransport.component h).Normal := SourceTransport.component_normal h
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  have hc := large_f918_automizer_cyclic (SourceTransport.simpleComponentEquiv h)
    (h.a315Input hA hC hp) (SourceTransport.complement_pairAction h hA hC hp)
    (SourceTransport.component_centralizer h) hm
  rw [SourceTransport.sylow_eq_image] at hc
  exact SourceTransport.automizer_cyclic_of_image (SourceTransport.ambientMap h)
    (h.complement_le_component.trans le_sup_left) le_sup_right
    (SourceTransport.complementMap_injective h hA hC hp) hc
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
