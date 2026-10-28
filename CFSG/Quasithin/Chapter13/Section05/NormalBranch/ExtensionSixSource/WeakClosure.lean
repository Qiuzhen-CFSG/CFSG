module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.ConjugateCenters
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Thompson
public import Theory.GroupTheory.MutuallyNormalizingConjugate
public import CFSG.Quasithin.ChapterA.Section01.Transfer
/-!
# Weak closure in the original S₆ extension branch

The original core Q_H is weakly closed in its normalizer H. A.1.13 would
otherwise give a distinct mutually normalizing conjugate. Its Frattini
line and the original one generate the common order-four center, so the
marked orthogonal-action rigidity forces this conjugate back to Q_H.
Burnside fusion then proves that the original point is weakly closed in
that center. All geometry and quotient bounds are supplied by the original
source datum and the full conclusion of 13.5.15.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 13.5.16, printed p.921, weak closure and Burnside fusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (b : Conclusions D M 6 g)
  (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))

include d h e hseed hn hU b
private theorem point_fixed_of_core_weakly_closed
    (hweak : ∀ x : G, D.QH.conjBy x ≤ (D.T : Subgroup G) → D.QH.conjBy x = D.QH)
    {z y : G} (hz : z ∈ D.V₁)
    (hy : y ∈ (center D.QH).map D.QH.subtype) (hzy : IsConj z y) : y = z := by
  have hzC : z ∈ centralizer (D.QH : Set G) := by
    intro q hq
    exact (((show D.QH ≤ D.H from h.QH_le_T.trans h.T_le_H).trans b.six.1.le hq) z hz).symm
  have hyC : y ∈ centralizer (D.QH : Set G) := by
    rwa [core_centralizer h b]
  obtain ⟨n,hnorm,he⟩ := ChapterA.lemma_A_1_35_elements D.T D.QH h.QH_le_T
    (fun a ha => mem_normalizer_iff_map_conj_eq.mpr (hweak a ha)) hzC hyC hzy
  have hnH : n ∈ D.H := by
    rwa [core_normalizer d h e hseed hn hU b] at hnorm
  have hcomm : z * n = n * z := (b.six.1 ▸ hnH) z hz
  rw [←he,←hcomm,mul_assoc,mul_inv_cancel,mul_one]

include hS
/-- The original two-core is weakly closed in its normalizer. The normalizer
condition supplies a mutually normalizing pair, whose common center and
marked action force equality. -/
theorem core_weakly_closed_in_normalizer (x : G)
    (hx : D.QH.conjBy x ≤ D.H) : D.QH.conjBy x = D.QH := by
  by_contra hne
  obtain ⟨a,ha,haQ,hQa⟩ := exists_mutually_normalizing_conjugate D.QH
    (isPGroup_pCoreIn 2 D.H) ⟨x,by
      rwa [core_normalizer d h e hseed hn hU b],hne⟩
  have haH : D.QH.conjBy a ≤ D.H := by
    rwa [core_normalizer d h e hseed hn hU b] at haQ
  obtain ⟨hsq,hcomm⟩ := conjugate_core_square_commutator
    d h e hseed hn hU b hS a ha haQ hQa
  have hcard : 64 ≤ Nat.card (D.QH.conjBy a) := by
    change 64 ≤ Nat.card (D.QH.map (MulAut.conj a).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj a).injective,
      core_card d h e hseed hn hU b hS]
  exact ha (core_unique_large d h e hseed hn hU b hS
    (D.QH.conjBy a) haH hsq hcomm hcard)

/-- Weak closure in the supplied Sylow follows with the original embedding. -/
theorem core_weakly_closed_in_sylow (x : G)
    (hx : D.QH.conjBy x ≤ (D.T : Subgroup G)) : D.QH.conjBy x = D.QH :=
  core_weakly_closed_in_normalizer d h e hseed hn hU b hS x (hx.trans h.T_le_H)

/-- Burnside fusion on the actual core fixes the original involution line
inside its order-four center. -/
theorem point_fixed_in_core_center {z y : G} (hz : z ∈ D.V₁)
    (hy : y ∈ (center D.QH).map D.QH.subtype) (hzy : IsConj z y) : y = z :=
  point_fixed_of_core_weakly_closed d h e hseed hn hU b
    (core_weakly_closed_in_sylow d h e hseed hn hU b hS) hz hy hzy

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
