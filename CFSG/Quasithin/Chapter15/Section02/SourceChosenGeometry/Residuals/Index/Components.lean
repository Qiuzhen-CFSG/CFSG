module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Models
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.FullSupport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.TwoOrbitResidualSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.Held

/-!
# The component cases of the chosen residual and support calculation

If the partner normal closure Kc differs from K = O²(H), the adequate
embedding theorem supplies an actual component orbit.  The binary invariant
row has three-prime index by the centerless rank-two/outer-group calculation
of A.3.18.  The exchanged rank-one row uses the actual two-component residual
identity from 1.2.2(a), with its quotient maps and moving element retained.
The retained Held component has the same residual identity, using its proved
outer two-group bound.  No exclusion of Held is needed for these conclusions.

Thus Kc is the literal O^{3′}(Mc) in every component row.  Its index is prime
to three; the existing intersection argument then excludes the actual proper
support alternative and constructs the original commutator-plane geometry.
The residual identity is proved from the component data before the index is
deduced; neither identity nor full support is an input to that calculation.

The Kc = K index calculation and the ambient Held exclusion from the short
structural list remain with this residual-geometry owner.  The parent
`qt-e-152-plane-geometry` supplies the preceding source inputs to `ResidualInput`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4)--(5), printed p.1111, using A.3.18 and 1.2.2(a).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter1.XiEmbedding
open Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open Section04.LocalSetup.EmbeddingReduction
open Section01 Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The residual equality holds in every component row, including Held. -/
theorem ResidualInput.residual_equality_of_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hne : partnerSpan H Mc ≠ residual H) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  have hMc := h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1
  have hHM : H ≤ Mc :=
    (Section01.source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (Section03.InitialSource.centralizer_le_partner T h.partner)
  have hle : partnerSpan H Mc ≤ threePrimeResidual Mc :=
    partnerSpan_le_threePrimeResidual hHM d.quotient.some
  rcases d.component_orbit with he | ⟨P,L,hP,hL,_,hq,hn,hcomm,hPL,he,ha⟩
  · exact (hne he).elim
  · have hXL : residual H ≤ componentOrbit L (T : Subgroup G) :=
      (le_conjugateSpanBy _ _).trans he.le
    rcases ha with ha | hh
    · rcases ha.2 with ⟨hs,hm⟩ | ⟨hi,_⟩
      · have hQ : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
          refine ⟨?_, hMc.isKGroup.quotient _⟩
          intro r hr ho
          let _ : Fact r.Prime := ⟨hr⟩
          exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
            (hMc.stronglyQuasithin r hr ho)
        have hi : (normalizer (L.subgroupOf Mc : Set Mc)).index = 2 := by
          rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hL.2 with hn | hi
          · exact (hs.1 ((partner_mem_overgroups h).2.trans
              ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn))).elim
          · exact hi
        have hqs := swapped_model_simple hq hm
        have hres := swapped_normalClosure_eq_residual_source hMc hP hL hq hqs hXL hs hm hi
        have horbit := swapped_normalClosure_eq_orbit hP hL hqs hXL hs hi
        rw [threePrimeResidual_eq]
        exact he.trans ((horbit.1.trans horbit.2).symm.trans hres)
      · have ho : componentOrbit L (T : Subgroup G) = L :=
          le_antisymm (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hi)
            (le_componentOrbit L (T : Subgroup G))
        have hnL : (L.subgroupOf Mc).Normal := ho ▸ hn
        have hXL' : residual H ≤ L := ho ▸ hXL
        obtain ⟨n,hdegree,hmodel,_⟩ := invariantWreathSieve T (residual H) P Mc L hP hMc
          hL hq hnL hi (ho ▸ hPL) hXL' (ho ▸ hcomm) d.residual_join_quotient ha
        have hm : ClassicalGroup.IsPSL (XiQuotient L) 4 2 ∨
            ClassicalGroup.IsPSL (XiQuotient L) 5 2 := by
          rcases hdegree with rfl | rfl
          · exact Or.inl hmodel
          · exact Or.inr hmodel
        apply le_antisymm hle
        rw [threePrimeResidual_eq]
        exact (binary_residual_le hMc hP hL hnL hXL' hm).trans (he.trans ho).ge
    · have hi := hh.2.2.1
      have ho : componentOrbit L (T : Subgroup G) = L :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hi)
          (le_componentOrbit L (T : Subgroup G))
      have hnL : (L.subgroupOf Mc).Normal := ho ▸ hn
      have hXL' : residual H ≤ L := ho ▸ hXL
      apply le_antisymm hle
      rw [threePrimeResidual_eq]
      exact (held_residual_le hMc hP hL hnL hXL' hh.2.2.2.some).trans (he.trans ho).ge

/-- The index conclusion in the component cases, on the original subgroup of Mc. -/
theorem ResidualInput.index_coprime_of_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hne : partnerSpan H Mc ≠ residual H) :
    Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index := by
  rw [d.residual_equality_of_ne hne, threePrimeResidual_eq]
  change Nat.Coprime 3 (((primeToResidual 3 Mc).map Mc.subtype).comap Mc.subtype).index
  rw [comap_map_eq_self_of_injective Mc.subtype_injective]
  exact primeToResidual_index_coprime 3

/-- The literal proper-support disjunct is impossible in a component row. -/
theorem ResidualInput.not_proper_of_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hne : partnerSpan H Mc ≠ residual H) :
    letI := localModule_elementary_from_source h.ambient T
      ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1, h.maximal.1.2⟩
    ¬ ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
      V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype :=
  not_proper_of_intersection_centralizes h
    (d.intersection_centralizes (d.residual_equality_of_ne hne))

/-- Every component row excludes the literal proper-support alternative. -/
theorem ResidualInput.full_of_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hne : partnerSpan H Mc ≠ residual H) :
    V = localModule T M :=
  d.full_of_index (d.index_coprime_of_ne hne)

/-- Application of the component calculation to the parent's actual plane geometry. -/
theorem ResidualInput.geometry_of_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hne : partnerSpan H Mc ≠ residual H) :
    ChosenPlaneGeometry h H ⁅V,B⁆ := d.geometry_of_full (d.full_of_ne hne)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
