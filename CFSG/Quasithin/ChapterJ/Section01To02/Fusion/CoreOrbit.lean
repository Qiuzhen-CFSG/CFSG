module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Seed
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Counting
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.FiberGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Transport
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry

/-!
# The involution orbit and local fusion: J.2.8

The seed construction uses the earlier source intersections and the actual
H/Q map. The counting theorem combines fifteen quotient fibers of size
sixteen. The local fusion proof uses a conjugator in L intersect H followed
by a Q-conjugator and the inverse of the chosen ell; Q <= L keeps the whole
conjugator in L. Finally an L-conjugator transports C_S(u) to the controlled
centralizer, and J.2.6(3) supplies fusion to z.

`sourceJ28_of_earlier_source` constructs the seed and all three geometry and
transport inputs to `sourceJ28_of_geometry`. J.2.3(6,9) follow from the genuine
LocalSetup through the full commutator and Steinberg intersection proofs.
Only J.2.2(5), SourceJ24 and SourceJ26 remain explicit earlier-source inputs;
no J.2.8 orbit or centralizer conclusion is assumed. Their producers are
`qt-j12-parabolic-structure`, `qt-j12-fusion-commutators`, and
`qt-j12-fusion-outer`. The fusion and section assembly owners retain the
discharge of these inputs.

Source: Aschbacher–Smith, J.2.8, printed pp.437–438 / PDF pp.448–449.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Retaining the parabolic conjugator and Q <= L gives the actual L-fusion in J.2.8(2). -/
theorem fusion_into_U (d : TypeRuSetup G) (s : ConjugateSeed d)
    (f : FiberGeometry d s) (t : QuotientTransport d s) (hQL : d.Q ≤ d.L)
    (homega : omegaOneAmbient d.HC = d.U)
    {i : G} (hi : i ∈ d.S ⊓ d.Q) (ho : orderOf i = 2) :
    ∃ l : d.L, (l : G) * i * (l : G)⁻¹ ∈ d.U := by
  by_cases hiU : i ∈ d.U
  · exact ⟨1, by simpa using hiU⟩
  let iQ : d.Q := ⟨i, hi.2⟩
  obtain ⟨l, hl⟩ := t.parabolic iQ hi.1 (involution_not_HC d homega hiU ho)
  obtain ⟨y, hy⟩ := conjugate_into_fiber d ⟨l, l.property.2⟩ s.w iQ ho hl
  obtain ⟨q, hq⟩ := f.conjugate y
  let a : d.L := ⟨(l : G) * q, d.L.mul_mem l.property.1 (hQL q.property)⟩
  have ha : (a : G) * s.w * (a : G)⁻¹ = i := by
    have hy' : (l : G) * (y : d.Q) * (l : G)⁻¹ = i := congrArg Subtype.val hy
    simpa only [a, mul_inv_rev, mul_assoc] using
      (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹) hq).trans hy'
  obtain ⟨u, hu, he⟩ := s.mem_conjugate
  refine ⟨s.ell⁻¹ * a⁻¹, ?_⟩
  have hw : (s.w : G) = (s.ell : G) * u * (s.ell : G)⁻¹ := he.symm
  rw [← ha, hw]
  simp only [coe_mul, coe_inv, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left, inv_mul_cancel, mul_one]
  exact hu

/-- Transport a controlled S-centralizer by an actual L-conjugator, then apply J.2.6(3). -/
theorem fusion_centralizer (d : TypeRuSetup G) {z : G}
    (h26 : SourceJ26 d z) (t : ElementaryTransport d)
    (v : G) (hv : v ∈ d.U) (hvV : v ∉ d.V)
    (hc : d.S ⊓ centralizer ({v} : Set G) ≤ d.Q)
    {u i : G} (hu : u ∈ d.U) (huV : u ∉ d.V)
    (hi : i ∈ d.S ⊓ centralizer ({u} : Set G)) (ho : orderOf i = 2) :
    IsConj i z := by
  obtain ⟨l, hl⟩ := t u v hu huV hv hvV
  let c := MulAut.conj (l : G)
  have hcv : c u = v := hl
  have hcS : c i ∈ d.S :=
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) i).mp hi.1
  have hcc : c i ∈ centralizer ({v} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, hcv] using congrArg c (mem_centralizer_singleton_iff.mp hi.2)
  have hconj : IsConj (c i) z := h26.2.2.1 (c i) (hc ⟨hcS, hcc⟩)
    ((c.orderOf_eq i).trans ho)
  exact (isConj_iff.mpr ⟨(l : G), rfl⟩).trans hconj

/-- Assemble the orbit and local fusion from the fiber and transport geometry.
`sourceJ28_of_earlier_source` below supplies all three geometric inputs. -/
theorem sourceJ28_of_geometry (d : TypeRuSetup G) {z : G}
    (s : ConjugateSeed d) (f : FiberGeometry d s) (t : QuotientTransport d s)
    (et : ElementaryTransport d) (hQL : d.Q ≤ d.L)
    (h26 : SourceJ26 d z) : SourceJ28 d z := by
  have homega := h26.2.2.2.1
  have hU : d.U ≤ d.HC := homega ▸ omegaOneAmbient_le d.HC
  refine ⟨⟨outside_transitive_of_fiber d homega s.w t.all f.conjugate,
    outside_card_of_fiber d hU homega t.card s.w t.all (fiber_card d s f),
    fun i hi => h26.2.2.1 i hi.1 hi.2.2⟩, ?_, ?_⟩
  · intro i hi ho
    exact fusion_into_U d s f t hQL homega hi ho
  · obtain ⟨v, hv, hvV, hc⟩ := f.centralizer_control
    intro u hu huV i hi ho
    exact fusion_centralizer d h26 et v hv.1 hvV hc hu huV hi ho

/-- All three clauses of J.2.8, conditional only on the explicit earlier
J.2.2(5), J.2.4 and J.2.6 conclusions. The seed, its sixteen-element fiber,
the actual Q-conjugators, and both restricted L-transports are constructed.
The J.2.3(6,9) inputs to the fiber proof are discharged from LocalSetup. -/
theorem sourceJ28_of_earlier_source (d : LocalSetup G) {z : G}
    (h225 : ∀ l : d.L,
      ConjugateIntersections.conjugateU d l ≠ d.toTypeRuSetup.U →
      Nat.card (((ConjugateIntersections.conjugateU d l).subgroupOf
        d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      ConjugateIntersections.conjugateU d l ⊓ d.toTypeRuSetup.HC = d.V)
    (h24 : SourceJ24 d.toTypeRuSetup) (h26 : SourceJ26 d.toTypeRuSetup z) :
    SourceJ28 d.toTypeRuSetup z := by
  have h239 (l : d.L) (hl : (l : G) ∉ d.toTypeRuSetup.H) :
      d.toTypeRuSetup.U ⊓ ConjugateIntersections.conjugateU d l = d.V :=
    SpecialCore.CommutatorGeometry.U_inf_conjugate d l l.property hl
  obtain ⟨s⟩ := exists_conjugateSeed d.toTypeRuSetup d.card_Z h239
    (fun l hl => ⟨ConjugateIntersections.conjugateU_le_H d l l.property, h225 l hl⟩)
  have h236 := SpecialCore.CommutatorGeometry.FixedSeed.full_commutator d
    ((d.Q_sup_S_eq_parabolic_core.trans d.parabolic_core_eq_R₁).symm)
    d.parabolic_core_eq_R₁
    (SpecialCore.CommutatorGeometry.natural_parabolics d.ru1)
  exact sourceJ28_of_geometry d.toTypeRuSetup s
    (fiberGeometry_of_earlier_source d s h24 h26 h236 h239)
    (quotientTransport d s) (elementaryTransport d) d.Q_le_L h26


end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
