module
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.BaerSuzukiInternalPair

/-!
# The original F.9 reductions in the unitary abelian-closure argument

Under F.9.1 and 13.3.17(3), the full module closure is abelian exactly when
`V` lies in the actual local two-core. The smaller closure becomes elementary
abelian when its image fixes the seed. Seed irreducibility identifies its
intersection with the core centralizer as the original point subgroup.

The nontrivial core-intersection step follows from Hall–Witt: if `V∩Q_H`
centralized `U_H`, then `[V,Q_H]` would centralize `U_H`; since `[Q_H,U_H]`
is central, `[V,U_H]` would centralize `Q_H`, contradicting the noncentral
seed. Thus the F.9.7 duality consequence needs no separately assumed pairing.
Finally Baer–Suzuki supplies a literal conjugate pair whose join is not a
two-group and contains its own conjugator.

The genuine point-parabolic action rows and F.9.1 applicability remain
with the source assembly. No final abelian-closure conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.3.18, printed pp.894–895; F.9.1–7, printed pp.317–321.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

/-- The commuting branch in 13.3.18: F.9.2 and the commutator conclusion
of 13.3.17(3) turn `V≤Q_H` into an abelian conjugate closure. -/
theorem closure_abelian_of_le_core
    (h : D.Hypothesis)
    (hcomm : ∀ g ∈ D.H,
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ ≤
        D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hV : D.V ≤ D.QH) : IsMulCommutative D.VH := by
  apply (conjugateSpanBy_commutative_iff D.V D.H).mpr
  apply le_centralizer_iff.mp
  apply (closure_le _).mpr
  rintro x ⟨g, hg, v, hv, rfl⟩
  let f := (MulAut.conj g).toMonoidHom
  have hQ : D.QH.map f = D.QH :=
    mem_normalizer_iff_map_conj_eq.mp (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D) hg)
  have hVg : D.V.map f ≤ D.QH := (map_mono hV).trans_eq hQ
  have hc : ⁅D.V, D.QH⁆ ≤ D.V :=
    le_normalizer_iff_commutator_le_left.mp (h.QH_le_T.trans h.T_normalizes_V)
  have hcg : ⁅D.V.map f, D.QH⁆ ≤ D.V.map f := by
    have hm := map_mono (f := f) hc
    rwa [map_commutator, hQ] at hm
  have hinter : ⁅D.V, D.V.map f⁆ ≤ D.V ⊓ D.V.map f := by
    refine le_inf ((commutator_mono le_rfl hVg).trans hc) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl hV).trans hcg
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (hcomm g hg hinter))) (mem_map_of_mem f hv)

/-- In the original F.9 setup, abelianness is equivalent to containment
in the actual local two-core, under 13.3.17(3). -/
theorem closure_abelian_iff_le_core
    (h : D.Hypothesis)
    (hcomm : ∀ g ∈ D.H,
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ ≤
        D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    IsMulCommutative D.VH ↔ D.V ≤ D.QH := by
  refine ⟨fun hc => ?_, closure_abelian_of_le_core h hcomm⟩
  let := h.elementary
  let _ : IsMulCommutative (conjugateSpanBy D.V D.H) := hc
  let _ : IsElementaryAbelian 2 D.VH :=
    conjugateSpanBy_elementary_of_commutative (p := 2) D.V D.H
  exact (le_conjugateSpanBy D.V D.H).trans
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.VH)
      h.VH_le_H (le_normalizer_conjugateSpanBy D.V D.H))

/-- The smaller closure becomes elementary abelian as soon as its actual
image centralizes the seed. -/
theorem seed_closure_elementary
    (h : D.Hypothesis)
    (hc : D.UH ≤ centralizer (D.Vplus : Set G)) : IsElementaryAbelian 2 D.UH := by
  let := h.elementary
  let _ : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
  let _ : IsMulCommutative (conjugateSpanBy D.Vplus D.H) :=
    (conjugateSpanBy_commutative_iff _ _).mpr (le_centralizer_iff.mp hc)
  exact conjugateSpanBy_elementary_of_commutative D.Vplus D.H

/-- The nontrivial core-intersection step of 13.3.18 follows directly from
Hall–Witt. This is the same consequence as the perfect pairing F.9.7. -/
theorem core_intersection_not_centralizes_seed_closure
    (h : D.Hypothesis)
    (hmove : D.Vplus ≤ ⁅D.V,D.UH⁆)
    (hnoncentral : ¬ D.Vplus ≤ centralizer (D.QH : Set G)) :
    ¬ D.V ⊓ D.QH ≤ centralizer (D.UH : Set G) := by
  intro hVC
  have hVQ : ⁅D.V,D.QH⁆ ≤ D.V ⊓ D.QH :=
    le_inf
      (le_normalizer_iff_commutator_le_left.mp (h.QH_le_T.trans h.T_normalizes_V))
      (le_normalizer_iff_commutator_le_right.mp
        (h.V_le_H.trans ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH))
  have hfirst : ⁅⁅D.UH,D.QH⁆,D.V⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (h.commutator_UH_QH_le_point.trans
        ((le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le h.V_le_H)))
  have hsecond : ⁅⁅D.QH,D.V⁆,D.UH⁆ = ⊥ := by
    rw [commutator_comm D.QH D.V]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hVQ.trans hVC)
  exact hnoncentral (hmove.trans (commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_rotate hfirst hsecond)))

/-- Irreducibility of the seed modulo its central line identifies its
intersection with the actual core centralizer. -/
theorem seed_inf_core_centralizer
    (h : D.Hypothesis)
    (hnoncentral : ¬ D.Vplus ≤ centralizer (D.QH : Set G)) :
    D.Vplus ⊓ centralizer (D.QH : Set G) = D.V₁ := by
  have hpoint : D.V₁ ≤ D.Vplus ⊓ centralizer (D.QH : Set G) :=
    le_inf h.point_lt.le ((le_centralizer_iff.mp h.H_centralizes).trans
      (centralizer_le (pCoreIn_le 2 D.H)))
  have hn : D.L₁ ⊔ (D.T : Subgroup G) ≤
      normalizer (D.Vplus ⊓ centralizer (D.QH : Set G) : Set G) :=
    (le_inf h.local_normalizes
      (h.local_le.trans
        (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH.trans
          (normalizer_le_normalizer_centralizer D.QH)))).trans
      inf_normalizer_le_normalizer_inf
  rcases h.irreducible _ hpoint inf_le_left hn with he | he
  · exact he
  · exact (hnoncentral (inf_eq_left.mp he)).elim

/-- A nonabelian closure supplies an actual pair of module conjugates
whose join is not a two-group, with the conjugator in the same `H`. -/
theorem exists_non_two_pair_of_nonabelian_closure
    (h : D.Hypothesis)
    (hcomm : ∀ g ∈ D.H,
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ ≤
        D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hn : ¬ IsMulCommutative D.VH) :
    ∃ g ∈ D.H, g ∈ D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom ∧
      ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let := h.elementary
  exact exists_internal_conjugate_sup_not_isPGroup_in D.H D.V h.V_le_H
    (fun hV => hn (closure_abelian_of_le_core h hcomm hV))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
