module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.ComponentAction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionConsequences
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1
public import Theory.GroupTheory.Commutator.FixedLineAction
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Weak closure and fusion in the natural branch

The preceding component, abelian-span and local-control stages imply that
W₀(T,V) centralizes the unchanged chosen V. Suppose A=V^g≤T moves V.
The aligned conjugate-core argument gives [K₁,O₂(K₁)]≤C_G(U).
Perfectness then makes [K₁,O₂(K₁T)] centralize U. Meanwhile O₂(K₁T)
displaces V into V₁ and fixes V₁. Its action commutes with L₁ on V;
irreducibility of V/V₁ and the fixed-line lemma force it to centralize V.
This contradicts the proved local-control clause that O₂(K₁) moves V₂.

This replaces the source's order-five/seven coprime-actor calculation by
the natural quotient's invariant-subgroup criterion. No actor selection,
core-centralization or weak-closure premise remains. The existing fusion
consequences give N_G(W₀)≤N_G(L) and the complete hyperplane assertion.
The preceding component/abelianity and local-control stages remain with
`qt-d-1291-natural-source`, which owns the full natural-branch assembly.

Source: Aschbacher--Smith, 12.9.9, printed pp.862--863 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The two-core of K₁T centralizes V if a Sylow-contained conjugate moves V.
The irreducibility of V/V₁ replaces the source's selected odd-order actor. -/
theorem point_overgroup_core_centralizes_of_moving
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥) :
    (C.K1 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let : IsElementaryAbelian 2 (F.tilde V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
  let := C.component.perfect
  let : Group.IsPerfect C.K1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe C.point_le).toMonoidHom)
    (subgroupOfEquivOfLe C.point_le).surjective
  let J := C.K1 ⊔ (T : Subgroup G)
  let P := J.pCoreIn 2
  have hJH : J ≤ F.H := control.overgroup.2.1
  have hPH : P ≤ F.H := (pCoreIn_le 2 J).trans hJH
  have hJP : J ≤ normalizer (P : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hPK : P ≤ normalizer (C.K1 : Set G) :=
    hPH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hKP : C.K1 ≤ normalizer (P : Set G) := le_sup_left.trans hJP
  have hcomm : ⁅C.K1,P⁆ ≤ C.K1.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 J).to_le (le_normalizer_iff_commutator_le_right.mp hKP))
      (le_normalizer_iff_commutator_le_left.mp hPK)
      (normalizer_commutator_ge_left C.K1 P)
  have hcU := (point_component_two_core_centralizes_of_moving h hn earlier F hab C control
    g hAT hmove).1
  have hdouble : ⁅⁅C.K1,P⁆,C.K1⁆ ≤ centralizer (F.U : Set G) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hcomm).trans hcU
  have hHC : F.H ≤ normalizer (centralizer (F.U : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer _)
  have hcentral : ⁅C.K1,P⁆ ≤ centralizer (F.U : Set G) := by
    have hh := commutator_commutator_le_of_rotate_of_le_normalizer
      (C.point_le.trans hHC) (C.point_le.trans hHC) (hPH.trans hHC)
      hdouble (by simpa only [commutator_comm P C.K1] using hdouble)
    simpa only [commutator_eq_self] using hh
  have hPV : ⁅P,V⁆ ≤ F.Vi 1 :=
    (commutator_mono le_rfl (le_conjugateSpanBy V J)).trans
      (local_span_core_displacement h earlier F J control.overgroup)
  apply centralizes_of_irreducible_fixed_line (F.Li L 1) P V (F.Vi 1)
    (F.le_seed 1) (by simpa using F.card 1 (by have := h.rank; omega))
    (by rw [h.seed_card]; rcases hn with rfl | rfl <;> norm_num)
    (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
    (hPH.trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by have := h.rank; omega)))) hPV
  · exact ((commutator_mono C.contains le_rfl).trans hcentral).trans
      (centralizer_le (le_conjugateSpanBy V F.H))
  · intro B hZB hBV hBN
    exact F.invariant_subgroup_of_ambient_natural h.naturalMarking
      (by have := h.rank; omega) B hZB hBV hBN

/-- No conjugate of the original seed contained in T can move it. -/
theorem sylow_conjugate_centralizes
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G)) :
    conjugate V g ≤ centralizer (V : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_contra hmoves
  have hc := point_overgroup_core_centralizes_of_moving h hn earlier F hab C control g hAT hmoves
  have hcore : C.K1.pCoreIn 2 ≤ (C.K1 ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C.K1)
      ((pCoreIn_le 2 C.K1).trans le_sup_left)
      ((control.overgroup.2.1.trans
        ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)).trans
          (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1)))
  apply control.core_moves_plane
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((hcore.trans hc).trans (centralizer_le (F.le_seed 2)))

/-- The complete W₀-centralization input of 12.9.9, conditional exactly on
its preceding component, abelian-span and local-control stages. -/
theorem weakClosureInput (K : GroupClass.{u}) : WeakClosureInput K := by
  intro X _ _ T L V n h hn earlier F hab C control
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAV,hindex⟩,hAT⟩
  have he : A = V.map (MulAut.conj g).toMonoidHom :=
    le_antisymm hAV (relIndex_eq_one.mp (by simpa only [pow_zero] using hindex))
  subst A
  simpa only [conjugate, inv_inv] using
    sylow_conjugate_centralizes h hn earlier F hab C control g⁻¹
      (by simpa only [conjugate, inv_inv] using hAT)

/-- Both clauses of source 12.9.9, applied to the unchanged original seed. -/
theorem fusionInput (K : GroupClass.{u}) : FusionInput K :=
  fusionInput_of_weakClosure (weakClosureInput K)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
