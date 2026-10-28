module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TrackComparison
public import CFSG.Quasithin.ChapterF.Section09.TrackBounds
public import CFSG.Quasithin.Chapter13.Section08.Elementary
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.AbelianConjugateSpan
/-!
# Constructing the 13.8 critical pair from abelian centralizer closure

The abelian full V-span of 13.7.8 has exponent two, and its H-span is
normal in H. Hence V lies in O₂(H). The natural orbit transitivity and
that same closure give 13.8.3. The actual even-critical-pair theorem now
forces odd track, and the O₂(H) containment forces track at least three.
The F.7/F.9 track comparison then constructs the original normalized
critical pair and its terminal transporter.

Only the earlier F.9 applicability and the genuine abelian-closure
result remain inputs; no parity, distance or chosen path is assumed.
Source: Aschbacher--Smith, 13.7.8 and 13.8.2--4, pp.935--947.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

theorem f9_pair_of_abelian_closure (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (z:G) (hz:z≠1) (hpoint:D.V₁=zpowers z)
    (htrans:∀v∈D.V,v≠1→∃l∈D.L,l*z*l⁻¹=v)
    [IsMulCommutative (centralizerConjugateClosure D.V z)] :
    ∃c:CriticalPair D.L (D.T:Subgroup G) D.H D.V, 3≤c.path.length ∧ Odd c.path.length := by
  have hHC : D.H≤centralizer ({z}:Set G) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact (h.H_centralizes ha z (by rw [hpoint]; exact mem_zpowers z)).symm
  let : IsMulCommutative (conjugateSpanBy D.V (centralizer ({z}:Set G))) := by
    rw [←centralizerConjugateClosure_eq_conjugateSpanBy]
    infer_instance
  let : IsMulCommutative (conjugateSpanBy D.V D.H) :=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hHC
  let : IsElementaryAbelian 2 D.V := h.elementary
  let : IsElementaryAbelian 2 (conjugateSpanBy D.V D.H) :=
    conjugateSpanBy_elementary_of_commutative D.V D.H
  have hcore : D.V≤D.QH :=
    (le_conjugateSpanBy D.V D.H).trans
      (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
        (conjugateSpanBy_le_self h.V_le_H) (le_normalizer_conjugateSpanBy D.V D.H))
  have hc : ∀g:G,D.V⊓D.V.map (MulAut.conj g).toMonoidHom ≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
    intro g hg
    exact intersecting_conjugates_commute D.L D.V hz
      (le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal))
      htrans g hg
  have hb:=h.b_bounds_of_intersecting_conjugates_commute hcore hc
  rw [←f9_criticalDistance_eq D h] at hb
  exact f9_criticalPair_bounds D h hb
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
