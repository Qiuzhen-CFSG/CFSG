module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits

/-!
# Residual models with the actual Held branch retained

The completed invariant wreath sieve applies after transporting the original
H/O₂(H) quotient across O²(H)T = H. For a moved component, the source
normalizer-index bound makes its T-orbit exactly L joined with Lᵗ. Both
conjugates normalize L, so this join is also the literal subgroup product.
These arguments prove every non-Held branch of original 15.2.12(2), including
the full automorphism-group quotient and both component memberships.

The adequate intrinsic embedding theorem also permits Held. Its residual
case below retains the actual Mc-normal closure, relative normality,
complement, and dihedral automizer. It is an outstanding ambient case, not
one of the source's three structural alternatives. No intrinsic exclusion
is inferred from the Sylow or dihedral hypotheses.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(2), printed p.1111, using 1.2.1(3), 1.3.4, and 14.1.6;
the invariant sieve is the completed source 10.2.4 calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter1.XiEmbedding
open Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

omit [Finite G] in
private theorem orbit_eq_of_invariant {L : Subgroup G}
    (hi : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    componentOrbit L (T : Subgroup G) = L :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hi)
    (le_componentOrbit L (T : Subgroup G))

private theorem orbit_eq_sup_of_swapped
    (h : ChosenSmallSource T M Mc V) {P L : Subgroup G}
    (hL : L ∈ cComponentsIn Mc) (hs : SwappedFactors (T : Subgroup G) P L)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hm : t ∉ normalizer (L : Set G)) :
    componentOrbit L (T : Subgroup G) = L ⊔ L.conjBy t := by
  have hTM : (T : Subgroup G) ≤ Mc := (partner_mem_overgroups h).2
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
    have hMc := h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1
    refine ⟨?_, hMc.isKGroup.quotient _⟩
    intro r hr ho
    let _ : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hMc.stronglyQuasithin r hr ho)
  have hi : (normalizer (L.subgroupOf Mc : Set Mc)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hL.2 with hn | hi
    · exact (hs.1 (hTM.trans ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn))).elim
    · exact hi
  let tM : Mc := ⟨t, hTM ht⟩
  have htM : tM ∉ normalizer (L.subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hL.1]
    exact hm
  have hconj (s : T) : L.conjBy (s : G) = L ∨ L.conjBy (s : G) = L.conjBy t := by
    by_cases hs : (s : G) ∈ normalizer L
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hs)
    · have hsM : (⟨s, hTM s.property⟩ : Mc) ∉ normalizer (L.subgroupOf Mc : Set Mc) := by
        rw [← subgroupOf_normalizer_eq hL.1]
        exact hs
      have he : tM⁻¹ * (⟨s, hTM s.property⟩ : Mc) ∈ normalizer (L.subgroupOf Mc : Set Mc) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htM, hsM])
      rw [← subgroupOf_normalizer_eq hL.1] at he
      have heq : L.conjBy (t⁻¹ * (s : G)) = L := mem_normalizer_iff_map_conj_eq.mp he
      have hh := congrArg (fun C : Subgroup G => C.conjBy t) heq
      rw [conjBy_mul, conjBy_inv'] at hh
      exact Or.inr hh
  apply le_antisymm
  · apply iSup_le
    intro s
    change L.conjBy (s : G) ≤ L ⊔ L.conjBy t
    rcases hconj s with he | he <;> rw [he]
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_componentOrbit L (T : Subgroup G))
      (le_iSup (fun s : T => L.conjBy s) ⟨t, ht⟩)

/-- The retained Held branch consists of the literal partner span, with all
of the component, normality, complement and automizer data on that subgroup. -/
@[expose] def HeldResidualCase (T : Sylow 2 G) (H Mc : Subgroup G) : Prop :=
  ∃ P : Subgroup G,
    LocalInput 3 (T : Subgroup G) (residual H) P Mc ∧
    partnerSpan H Mc ∈ cComponentsIn Mc ∧
    partnerSpan H Mc ∈ LStar G (T : Subgroup G) ∧
    IsQuasisimple (XiQuotient (partnerSpan H Mc)) ∧
    ((partnerSpan H Mc).subgroupOf Mc).Normal ∧
    (T : Subgroup G) ≤ normalizer (partnerSpan H Mc : Set G) ∧
    P ≤ partnerSpan H Mc ∧
    residual H ≤ partnerSpan H Mc ∧
    ⁅partnerSpan H Mc, P⁆ = partnerSpan H Mc ∧
    Nonempty (P ≃* Plane 3) ∧
    Nonempty (automizer (T : Subgroup G) P ≃* DihedralGroup 4) ∧
    Nonempty (XiQuotient (partnerSpan H Mc) ≃* Held.He)

/-- Transport the supplied quotient across the literal residual--Sylow join. -/
theorem ResidualInput.residual_join_quotient {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    Nonempty (XiQuotient (residual H ⊔ (T : Subgroup G)) ≃* ParabolicWreath) := by
  let e : (residual H ⊔ (T : Subgroup G) : Subgroup G) ≃* H :=
    MulEquiv.subgroupCongr d.residual_join
  let q : XiQuotient (residual H ⊔ (T : Subgroup G)) ≃* XiQuotient H :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact d.quotient.map (fun f => q.trans f)

/-- All three source alternatives, or the explicit actual Held component.
The intrinsic Held alternative is deliberately retained. -/
theorem ResidualInput.structural_or_held {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    StructuralAlternatives T H Mc ∨ HeldResidualCase T H Mc := by
  rcases d.component_orbit with he | ⟨P,L,hP,hL,hLs,hq,hn,hcomm,hPL,he,ha⟩
  · exact Or.inl (Or.inl he)
  · rcases ha with ha | hh
    · rcases ha.2 with ⟨hs,hm⟩ | ⟨hi,_⟩
      · obtain ⟨t,ht,htn,_⟩ := hs.2
        have ho := orbit_eq_sup_of_swapped h hL hs ht.1 htn
        have heq : partnerSpan H Mc = L ⊔ L.conjBy t := he.trans ho
        have hnL : L.conjBy t ≤ normalizer (L : Set G) :=
          (le_iSup (fun s : T => L.conjBy s) ⟨t,ht.1⟩).trans
            (cComponentOrbit_le_normalizer hL (partner_mem_overgroups h).2)
        refine Or.inl (Or.inr (Or.inr ⟨L,t,hLs,hL,ht.1,htn,heq,?_,?_⟩))
        · rw [heq]
          exact coe_mul_of_right_le_normalizer_left L (L.conjBy t) hnL
        · rcases hm with ⟨n,hn,_,hm⟩ | hm
          · exact Or.inl ⟨n,hn,hm⟩
          · exact Or.inr hm
      · have ho := orbit_eq_of_invariant hi
        have heL : partnerSpan H Mc = L := he.trans ho
        have hnL : (L.subgroupOf Mc).Normal := ho ▸ hn
        have hXL : residual H ≤ L :=
          (le_conjugateSpanBy (residual H) Mc).trans heL.le
        obtain ⟨n,hdegree,hmodel,hiso⟩ := invariantWreathSieve T (residual H) P Mc L hP
          (h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1)
          hL hq hnL hi (ho ▸ hPL) hXL (ho ▸ hcomm) d.residual_join_quotient ha
        subst L
        exact Or.inl (Or.inr (Or.inl ⟨hLs,hL,n,hdegree,hmodel,hiso⟩))
    · have ho := orbit_eq_of_invariant hh.2.2.1
      have heL : partnerSpan H Mc = L := he.trans ho
      subst L
      exact Or.inr ⟨P,hP,hL,hLs,hq,ho ▸ hn,hh.2.2.1,ho ▸ hPL,
        le_conjugateSpanBy _ _,ho ▸ hcomm,hh.2.1,
        Invariant.automizer_equiv_dihedral hP hh.2.1 d.residual_join_quotient,hh.2.2.2⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
