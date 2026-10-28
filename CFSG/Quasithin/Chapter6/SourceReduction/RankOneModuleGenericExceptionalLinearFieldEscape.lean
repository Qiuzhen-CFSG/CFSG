module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeDefs
public import Theory.GroupTheory.CentralizerConjugateGeneration.Intersecting
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# The final quadratic bound in the escaping cubic branch

Starting with the literal local data and the abelian centralizer span of
5.1.23, transitivity of L₂ on V₂ minus the identity makes intersecting
conjugates commute. This supplies F.8.1(a) and the commutator condition
of F.9.1. With V₊ = V = V₂, the additional centralizer test in the proved
F.9.16 witness construction is automatic. The resulting faithful action
is on the actual ⟨V₂^H⟩/⟨z⟩, with actor H/O₂(H), and has q ≤ 2.

This is a conditional source application: construction of the local data,
abelianness in 5.1.23, and the incompatible strict bound remain explicit.
E.5.4 belongs to the preceding normalizing branch of 5.1.20 and is not
needed after cubic escape has been assumed.

Source: Aschbacher--Smith, final paragraph of 5.1.14, printed p.646;
F.8.1 and F.9.16(3), pp.315,323--324 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

namespace LocalData
variable (d : LocalData T H C z)
include d

theorem point_card : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp d.point_mem).2.1 d.point_ne

theorem actor_normalizes_plane : actor T C ≤ normalizer (plane C z : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer d.plane_le).mp d.reduced.normal
  exact le_sup_left.trans hn

theorem H_centralizes_point : H ≤ centralizer (zpowers z : Set G) := by
  exact d.g2.H_le.trans (normalizer_le_centralizer_of_card_two _ d.point_card)

/-- A.1.7 on the actual plane, using precisely the abelian-span conclusion
of 5.1.23. This gives all intersecting conjugates, not only those through z. -/
theorem intersecting_conjugates_commute
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))]
    (g : G) (hi : plane C z ⊓ (plane C z).map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅plane C z, (plane C z).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let : IsMulCommutative (centralizerConjugateClosure (plane C z) z) := by
    rw [centralizerConjugateClosure_eq_conjugateSpanBy]
    infer_instance
  apply intersecting_conjugates_commute_of_transitive_centralizer_span
    (plane C z) (le_conjugateSpanBy (zpowers z) C (mem_zpowers z)) d.point_ne
    (fun x hx hn => ?_) g hi
  obtain ⟨l, hl, he⟩ := d.transitive x hx hn
  exact ⟨l, d.actor_normalizes_plane hl, he⟩

/-- The actual H-span inherits the abelian centralizer span of 5.1.23. -/
theorem span_abelian
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))] :
    IsMulCommutative (conjugateSpanBy (plane C z) H) := by
  apply conjugateSpanBy_isMulCommutative_of_le
    (K := centralizer ({z} : Set G)) le_rfl
  simpa only [zpowers_eq_closure, centralizer_closure] using d.H_centralizes_point

/-- All F.8.1 conditions, with conjugate commutativity proved from 5.1.23. -/
theorem f8_hypothesis
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))] :
    ChapterF.Section08.Setup.Hypothesis (setup T H C z) where
  sylow := ⟨T, rfl⟩
  elementary := d.g2.elementary
  residual := d.g2.residual
  T_normalizes_L := d.g2.T_normalizes_L
  characteristic_L := d.characteristic_actor
  V_le_LT := d.plane_le
  reduced := d.reduced
  centralizer_eq := d.centralizer_eq
  point_ne_bot := d.g2.point_ne_bot
  point_le := d.g2.point_le
  T_normalizes_point := d.g2.T_normalizes_point
  conjugates_commute := by
    intro g hg
    apply d.intersecting_conjugates_commute g⁻¹
    exact ne_bot_of_le_ne_bot hg (inf_le_inf_right _ d.g2.point_le)
  quotient_nonzero := d.g2.quotient_nonzero
  irreducible := d.g2.irreducible
  H_le := d.g2.H_le
  local_le := d.g2.local_le
  characteristic_H := d.g2.characteristic_two
  centralizer_core_le := d.kernel_core
  generated_core := d.generated_core

/-- The source F.9 specialization has V₊ = V₂. Both centralizers and the
point-stabilizer residual are transported literally from the F.8 setup. -/
theorem f9_hypothesis
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))] :
    (f9Setup T H C z).Hypothesis := by
  have hn : normalizer (zpowers z : Set G) = centralizer (zpowers z : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ d.point_card)
      (Subgroup.centralizer_le_normalizer _)
  have hlocal : (f9Setup T H C z).L₁ = (setup T H C z).L₁ := by
    exact congrArg (fun N : Subgroup G => (pResidual 2 N).map N.subtype)
      (congrArg (fun N : Subgroup G => actor T C ⊓ N) hn.symm)
  have hV : plane C z ≤ H := d.g2.V_le_T.trans (le_sup_right.trans d.g2.local_le)
  refine {
    elementary := d.g2.elementary
    residual := d.g2.residual
    normalizes_L := d.g2.T_normalizes_L
    characteristic_L := d.characteristic_actor
    V_le_LT := d.plane_le
    reduced := d.reduced
    sylow_centralizer := d.centralizer_eq
    point_card := d.point_card
    normalizes_point := d.g2.T_normalizes_point
    point_lt := lt_of_le_of_ne d.g2.point_le d.g2.quotient_nonzero
    plus_le := le_rfl
    H_centralizes := d.H_centralizes_point
    local_le := ?_
    characteristic_H := d.g2.characteristic_two
    kernel_core := ?_
    local_normalizes := ?_
    irreducible := ?_
    normalizer_control := le_rfl
    generated_core := d.generated_core
    commutator_lifting := ?_ }
  · rw [hlocal]
    exact d.g2.local_le
  · have hh := d.kernel_core
    rw [ChapterF.Section08.Setup.quotientCentralizer_eq_intrinsic _ d.g2.H_le
      (plane C z) hV] at hh
    exact hh
  · rw [hlocal]
    exact d.g2.local_normalizes_V
  · intro W hW hWV hN
    rw [hlocal] at hN
    exact d.g2.irreducible W hW hWV hN
  · intro g hg _ _ _
    let : IsMulCommutative (conjugateSpanBy (plane C z) H) := d.span_abelian
    have hfirst : plane C z ≤ conjugateSpanBy (plane C z) H := le_conjugateSpanBy _ _
    have hsecond : (plane C z).map (MulAut.conj g).toMonoidHom ≤
        conjugateSpanBy (plane C z) H := by
      rintro _ ⟨v, hv, rfl⟩
      exact subset_closure ⟨g, hg, v, hv, rfl⟩
    have hc : ⁅plane C z, (plane C z).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact hfirst.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le hsecond))
    exact ⟨hc, (commutator_comm _ _).trans hc⟩

/-- F.9.16(3) on the original quotient action. No FF, critical-pair,
chosen-actor or upper-ratio premise remains. -/
theorem quadraticRatio_le_two
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))]
    [IsElementaryAbelian 2 (conjugateSpanBy (plane C z) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (plane C z) H) (zpowers z)) :
    quadraticRatio a.representation ≤ 2 := by
  let : IsElementaryAbelian 2 (plane C z) := d.g2.elementary
  let : IsMulCommutative (conjugateSpanBy (plane C z) H) := d.span_abelian
  apply OriginalF916.original_bound (SourceF91.ofF91 d.f9_hypothesis)
    d.intersecting_conjugates_commute _ a
  intro x hx
  exact Or.inl (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (zpowers_le.mpr hx)))

/-- Construct the literal faithful quotient action as well as its bound. -/
theorem exists_bounded_action
    [IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))] :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (plane C z) H),
      letI := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy (plane C z) H) (zpowers z),
        quadraticRatio a.representation ≤ 2 := by
  let : IsElementaryAbelian 2 (plane C z) := d.g2.elementary
  let : IsMulCommutative (conjugateSpanBy (plane C z) H) := d.span_abelian
  apply OriginalF916.original_bounded_action (SourceF91.ofF91 d.f9_hypothesis)
    d.intersecting_conjugates_commute
  intro x hx
  exact Or.inl (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (zpowers_le.mpr hx)))

end LocalData
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
