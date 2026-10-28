module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The two surviving embedding branches in 15.4.20

The universal corrected local embedding theorem supplies the complete alternatives.
The genuine orbit statement in 1.2.1(3), together with the actual Sylow subgroup,
makes an invariant component relatively normal. The D₈ action excludes the
symplectic, linear-three and Mathieu-eleven cases. The remaining binary models
have simple two-core quotient and the full automorphism quotient; the exchanged
case retains both rank-one models and the exact conjugate factorization.

The earlier-result parameters below are universally quantified source statements,
not extra hypotheses containing the two-branch conclusion. Their source owners
must discharge them in final Chapter 15 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.2.1(3), 1.2.2(a), 1.3.4, printed pp.504, 509–511 and 1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u

/-- The full source 1.2.1(3), uniformly over the local subgroups of the standing group. -/
def ComponentOrbitTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ (A : Type u) [Group A] [Finite A], IsSimpleQTKE κ A →
    ∀ H ∈ Chapter1.H A, ∀ L ∈ Chapter1.cComponentsIn H,
      (L.subgroupOf H).Normal ∨
        (Set.range fun x : H => (L.subgroupOf H).map (MulAut.conj x).toMonoidHom).ncard = 2 ∧
          Chapter1.Section02.NonnormalCComponentModel (Chapter1.XiQuotient L)

/-- Exact source 1.2.2(a): the prime divides the order of the quotient image,
and the entire H-orbit has two elements. -/
def TwoOrbitResidualTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ (A : Type u) [Group A] [Finite A], IsSimpleQTKE κ A →
    ∀ H ∈ Chapter1.H A, ∀ L ∈ Chapter1.cComponentsIn H, ∀ p : ℕ,
      p.Prime → Odd p →
      (Set.range fun x : H => (L.subgroupOf H).map (MulAut.conj x).toMonoidHom).ncard = 2 →
      p ∣ Nat.card ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) →
      (primeToResidual p H).map H.subtype = componentOrbit L H

variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

/-- A Sylow two-subgroup cannot fix one member of an orbit of size two. -/
theorem normal_of_sylow_normalizes {L : Subgroup G}
    (hLH : L ≤ H) (hU : Chapter1.IsSylowIn 2 U H) (hUL : U ≤ normalizer L)
    (horbit : (L.subgroupOf H).Normal ∨
      (normalizer (L.subgroupOf H : Set H)).index = 2) :
    (L.subgroupOf H).Normal := by
  rcases horbit with hn | hi
  · exact hn
  · obtain ⟨S, hS⟩ := hU
    have hSN : (S : Subgroup H) ≤ normalizer (L.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hLH]
      intro s hs
      exact hUL (hS ▸ (show (s : G) ∈ (S : Subgroup H).map H.subtype from ⟨s, hs, rfl⟩))
    have hd := index_dvd_of_le hSN
    rw [hi] at hd
    exact (S.not_dvd_index hd).elim

omit [Finite G] in
/-- The fixed orbit consists of its original component. -/
theorem componentOrbit_eq_of_normalizes {L U : Subgroup G}
    (hUL : U ≤ normalizer L) : componentOrbit L U = L :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer L U L le_rfl hUL)
    (le_componentOrbit L U)

/-- Perfectness of the actual C-component implies two-perfectness. -/
theorem cComponent_twoPerfect {L : Subgroup G} (hL : L ∈ Chapter1.cComponentsIn H) :
    IsPPerfect 2 L := by
  let _ := hL.2.perfect
  let _ : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hL.1).toMonoidHom) (subgroupOfEquivOfLe hL.1).surjective
  intro N hN hp
  let _ := hN
  have hsub : Subsingleton (L ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Centerlessness removes all central-cover distinctions in this particular branch. -/
theorem simple_of_quasisimple_center_bot {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) (hz : center Q = ⊥) : IsSimpleGroup Q := by
  let _ := hq
  let _ := hq.simple
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)).isSimpleGroup

/-- Both retained rank-one models are simple; perfectness handles small fields. -/
theorem swapped_model_simple {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) (hm : Chapter1.XiEmbedding.SwappedModel 3 Q) :
    IsSimpleGroup Q := by
  have hl {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    let _ := hq
    let _ : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    have hs : IsSimpleGroup PSL(2, F) :=
      MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
        PSL2.Iwasawa inferInstance
    exact e.isSimpleGroup_congr.mpr hs
  rcases hm with ⟨n, _, _, hm⟩ | ⟨q, _, _, hm⟩ <;> exact hl hm

/-- All surviving model and action clauses, before normal-generation and residual assembly. -/
theorem PlacedX.two_branches (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (orbits : ComponentOrbitTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn H ∧
      IsQuasisimple (Chapter1.XiQuotient L) ∧
      IsSimpleGroup (Chapter1.XiQuotient L) ∧ d.wholeX ≤ componentOrbit L U ∧
      Nonempty (P₀ ≃* Chapter1.XiEmbedding.Plane 3) ∧
      Nonempty (Chapter1.XiEmbedding.automizer U P₀ ≃* DihedralGroup 4) ∧
      ((Chapter1.XiEmbedding.SwappedFactors U P₀ L ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient L) ∧
          (normalizer (L.subgroupOf H : Set H)).index = 2) ∨
        ((L.subgroupOf H).Normal ∧ d.wholeX ≤ L ∧
          (ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 4 2 ∨
            ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 5 2) ∧
          Nonempty (Chapter1.XiQuotient (L ⊔ U) ≃*
            MulAut (Chapter1.XiQuotient L)))) := by
  obtain ⟨hsq, hlocal, hSylow, hD⟩ := h.embedding_input hG P
  obtain ⟨L, hL, hq, hX, he, _, ha⟩ := h.component_alternatives hG embedding P
  have ho := orbits G hG H h.overgroup.1 L hL
  rw [ncard_conjugates_eq_index_normalizer] at ho
  have hUH : U ≤ H := le_sup_right.trans hlocal.overgroup
  rcases ha with ⟨hs, hm⟩ | ⟨hn, hm⟩
  · have hi : (normalizer (L.subgroupOf H : Set H)).index = 2 := by
      rcases ho with hn | ⟨hi, _⟩
      · exact (hs.1 (hUH.trans ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn))).elim
      · exact hi
    exact ⟨L, hL, hq, swapped_model_simple hq hm, hX, he, hD, Or.inl ⟨hs, hm, hi⟩⟩
  · have hLn := normal_of_sylow_normalizes hL.1 hSylow hn (ho.imp_right And.left)
    have hXL : d.wholeX ≤ L := (componentOrbit_eq_of_normalizes hn) ▸ hX
    have hmodel : ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 4 2 ∨
        ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 5 2 := by
      rcases hm with hthree | heleven | hfour | hfive
      · exact (SmallModels.not_linearThreeModel hlocal hSylow hL.1 hLn hXL hD hthree).elim
      · exact (SmallModels.not_mathieuEleven hlocal hSylow hL.1 hLn hXL hD heleven).elim
      · exact Or.inl hfour
      · exact Or.inr hfive
    have hz : center (Chapter1.XiQuotient L) = ⊥ := by
      rcases hmodel with hm | hm
      · exact binary_linear_center_eq_bot (by decide : 0 < 4) hm
      · exact binary_linear_center_eq_bot (by decide : 0 < 5) hm
    exact ⟨L, hL, hq, simple_of_quasisimple_center_bot hq hz, hX, he, hD,
      Or.inr ⟨hLn, hXL, hmodel,
        BinaryAction.binary_quotient_aut hsq hlocal hSylow hL hLn hXL hq hD hmodel⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
