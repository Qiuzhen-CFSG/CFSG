module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.MathieuTwelve
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.HigmanSims
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddPrimary
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.Mathieu.SchurMultipliers.SourceCovers
public import Theory.Mathieu.SchurMultipliers.OddLocalPartialInversion

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Source

/-!
# Original sporadic intrinsic three-complement alternatives

The checked Mathieu and sporadic cover theorems remove the central kernel
using the original trivial two-core. The fixed-carrier pair calculations then
exclude the impossible cases or give the actual M11 and Held planes. The final
consumer retains the literal original local input, Sylow subgroup and component
quotient. The J4 calculation is separate; no universal sporadic sieve is assumed.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511, together with the
retained Held correction documented in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.Source
universe u
variable {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

/-- The surviving M11 branch identifies both the plane and the whole component. -/
theorem m11_surviving (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M11) :
    Nonempty (R ≃* Plane 3) ∧ Nonempty (Q ≃* Sporadic.Mathieu.M11) := by
  let : IsQuasisimple Q := h.quasisimple
  have hz : center Q = ⊥ := by
    rw [← centralQuotientCover_ker e]
    exact Sporadic.Mathieu.SchurMultipliers.m11_cover_kernel_eq_bot (centralQuotientCover e)
  let j := equiv_of_center_eq_bot e hz
  exact ⟨m11_plane_of_equiv h j, ⟨j⟩⟩

/-- The original M12 pair is impossible, including all central covers. -/
theorem m12_excluded (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M12) : False := by
  let : IsQuasisimple Q := h.quasisimple
  have hz := Sporadic.Mathieu.SchurMultipliers.m12_center_isTwoGroup e
  let j := SporadicActions.centralQuotientEquiv h.twoCore hz e
  have hi := pairInput_of_equiv h j
  exact MathieuTwelve.no_pair _ _ hi.oddComplement hi.permutes

/-- The actual M23 invariant-line theorem applies through its original central quotient. -/
theorem m23_reducible (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M23) : PairReducible (S : Subgroup Q) R := by
  let : IsQuasisimple Q := h.quasisimple
  have hz : IsPGroup 2 (center Q) := by
    rw [← centralQuotientCover_ker e]
    exact Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m23_cover_kernel_isTwoGroup
      (centralQuotientCover e)
  exact SporadicActions.pairReducible_of_centralQuotient h e hz
    (by intro hF hS hP S' R' hi; exact @SporadicActions.m23_carrierPairExclusion hF hS hP S' R' hi)

/-- The actual M24 pair theorem applies with its covering premise discharged. -/
theorem m24_reducible (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M24) : PairReducible (S : Subgroup Q) R := by
  let : IsQuasisimple Q := h.quasisimple
  exact SporadicActions.pairReducible_of_centralQuotient h e
    (Sporadic.Mathieu.SchurMultipliers.m24_center_isTwoGroup e)
    (by intro hF hS hP S' R' hi; exact @SporadicActions.m24_carrierPairExclusion hF hS hP S' R' hi)

/-- Full J2 automorphism coverage and its proved odd-primary cover bound discharge both premises. -/
theorem j2_reducible (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.LeechRelated.J2.Carrier) :
    PairReducible (S : Subgroup Q) R := by
  let : IsQuasisimple Q := h.quasisimple
  exact SporadicActions.pairReducible_of_centralQuotient h e
    (Theory.SpecificGroups.J2HSMultipliers.J2.center_isPGroup_of_quotient_equiv e)
    (by
      intro hF hS hP S' R' hi
      exact @SporadicActions.j2_carrierPairExclusion_of_coverage
        Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionAction_surjective hF hS hP S' R' hi)

/-- The HS fixed-carrier exclusion applies to every original quasisimple pair. -/
theorem hs_excluded (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  let : IsQuasisimple Q := h.quasisimple
  let j := SporadicActions.centralQuotientEquiv h.twoCore
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e) e
  exact HigmanSims.no_pair (pairInput_of_equiv h j)

/-- The Ru fixed-carrier exclusion applies without a covering or maximal-overgroup premise. -/
theorem ru_excluded (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Rudvalis.Model) : False := by
  let : IsQuasisimple Q := h.quasisimple
  let j := SporadicActions.centralQuotientEquiv h.twoCore
    (Rudvalis.Multiplier.source_center_isPGroup ⟨e⟩) e
  exact rudvalis_no_pair (pairInput_of_equiv h j)

/-- Ten original sporadic quotient cases, retaining the actual M11 and Held survivors. -/
theorem alternatives_of_source (h : PairInput S R)
    (hm : IsRemainingSporadicQuotient Q ∨
      Nonempty (Q ⧸ center Q ≃* Sporadic.Mathieu.M23) ∨
      Nonempty (Q ⧸ center Q ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (Q ⧸ center Q ≃* Sporadic.LeechRelated.J2.Carrier)) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧
        (Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨ Nonempty (Q ≃* Held.He))) := by
  rcases hm with hm | e | e | e
  · rcases hm with e | e | e | e | e | e | e
    · obtain ⟨hp, he⟩ := m11_surviving h e.some
      exact Or.inr ⟨hp, Or.inl he⟩
    · exact (m12_excluded h e.some).elim
    · exact Or.inl (mathieu_twentyTwo_cover h e.some)
    · exact (hs_excluded h e.some).elim
    · obtain ⟨hp, he⟩ := HeldPairs.surviving_of_source h e.some
      exact Or.inr ⟨hp, Or.inr he⟩
    · exact (ru_excluded h e.some).elim
    · exact (j1_no_pair h e.some).elim
  · exact Or.inl (m23_reducible h e.some)
  · exact Or.inl (m24_reducible h e.some)
  · exact Or.inl (j2_reducible h e.some)

/-- The literal local/Sylow consumer discharges all ten sporadic pair branches. -/
theorem alternatives_of_local_input {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hm : IsRemainingSporadicQuotient (XiQuotient L) ∨
      Nonempty (XiQuotient L ⧸ center (XiQuotient L) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty (XiQuotient L ⧸ center (XiQuotient L) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (XiQuotient L ⧸ center (XiQuotient L) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    Alternatives 3 T P L ∨ HeldAlternative 3 T P L := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  rcases alternatives_of_source hi hm with hr | ⟨he, hm⟩
  · exact (not_pairReducible h hPL hTL (by simpa only [hS] using hr)).elim
  · have hp := plane_of_quotient_plane h hPL he
    rcases hm with hm | hm
    · exact Or.inl ⟨hp, Or.inr ⟨hTL, Or.inr (Or.inr ⟨rfl, Or.inl hm⟩)⟩⟩
    · exact Or.inr ⟨rfl, hp, hTL, hm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.Source
