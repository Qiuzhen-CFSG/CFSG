module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Diagonal
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Coprime splitting of the Sylow omega-center

A diagonal section normalizes the Sylow subgroup and hence its elementary
abelian omega-center. Its odd order gives the direct coprime decomposition
into its fixed subgroup and its displacement subgroup. The latter lies in
U(L), and is disjoint from the center of L.

These are the group-action steps in the L₂-block calculation of
Aschbacher–Smith E.6.7, printed p.246. Identifying the fixed subgroup with
the full L-centralizer and proving nonzero displacement are separate steps;
no covering-module conclusion is assumed here.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L F : Type*} [Group L] [Field F] {B : Subgroup L}

private theorem normalizer_le_omegaCenter_normalizer (S : Subgroup L) :
    normalizer (S : Set L) ≤ normalizer (Stellmacher.omegaOneCenterAmbient S : Set L) := by
  apply subgroup_le_normalizer_of_conj_mem
  intro x z hz
  have hm : S.map (MulAut.conj (x : L)).toMonoidHom = S := by
    ext s
    rw [mem_map_equiv]
    simpa only [MulAut.conj_symm_apply, inv_inv] using
      ((mem_normalizer_iff.mp ((normalizer (S : Set L)).inv_mem x.property)) s).symm
  have he := Stellmacher.omegaOneCenterAmbient_map_injective
    (MulAut.conj (x : L)).toMonoidHom (MulAut.conj (x : L)).injective S
  rw [hm] at he
  rw [he]
  exact mem_map_of_mem _ hz

variable [Finite F] [CharP F 2] {a : MarkedBlockModel L B F}

/-- The diagonal torus acts on the actual omega-center by conjugation. -/
theorem DiagonalSection.normalizes_omegaCenter (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    d.torus ≤ normalizer (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) : Set L) :=
  (d.normalizes_sylow S hS).trans (normalizer_le_omegaCenter_normalizer _)

/-- Every displacement lies in the original omega-center. -/
theorem DiagonalSection.displacement_le_omegaCenter (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ ≤
      Stellmacher.omegaOneCenterAmbient (S : Subgroup L) :=
  le_normalizer_iff_commutator_le_left.mp (d.normalizes_omegaCenter S hS)

omit [Finite F] [CharP F 2] in
/-- The short-group definition places all torus displacements in U(L). -/
theorem DiagonalSection.displacement_le_blockU (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) :
    ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ ≤ ChapterC.blockU L :=
  commutator_mono (a.omegaOneCenter_le_core hshort S) le_top

variable [Finite L]

omit [CharP F 2] in
private theorem torus_coprime_omegaCenter (d : DiagonalSection a)
    (S : Sylow 2 L) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Nat.Coprime (Nat.card d.torus)
      (Nat.card (Stellmacher.omegaOneCenterAmbient (S : Subgroup L))) := by
  let : IsElementaryAbelian 2 (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)) :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2
    (Stellmacher.omegaOneCenterAmbient (S : Subgroup L))).exists_card_eq
  rw [hk, d.torus_card, hF]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  have he : Even (2 ^ n) := (even_iff_two_dvd.mpr (dvd_refl 2)).pow_of_ne_zero (by omega)
  exact (Nat.odd_sub' (Nat.one_le_pow n 2 (by decide))).mpr (by simpa using he)

/-- Coprime splitting, with the torus centralizer still identified literally. -/
theorem DiagonalSection.omegaCenter_coprime_decomposition (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) =
      (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (d.torus : Set L)) ⊔
        ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ := by
  let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  rw [sup_comm]
  exact eq_commutator_sup_centralizer_of_solvable_coprime Z d.torus
    (d.normalizes_omegaCenter S hS) (Group.isSolvable_of_comm fun x y => mul_comm x y)
    (torus_coprime_omegaCenter d S hn hF)

/-- The fixed and moving factors of the omega-center have trivial intersection. -/
theorem DiagonalSection.omegaCenter_coprime_disjoint (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Disjoint
      (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (d.torus : Set L))
      ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ := by
  let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hnorm := d.normalizes_omegaCenter S hS
  let : Normalizes d.torus Z := ⟨hnorm⟩
  have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := Z) (A := d.torus) (Group.isSolvable_of_comm fun x y => mul_comm x y)
    (torus_coprime_omegaCenter d S hn hF) inferInstance
  have hfix : (FixedPoints.subgroup d.torus Z).map Z.subtype =
      Z ⊓ centralizer (d.torus : Set L) := by
    change (fixedPointSubgroup d.torus Z).map Z.subtype = _
    rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Z d.torus hnorm]
    exact map_subgroupOf_eq_of_le inf_le_left
  rw [← hfix, ← commutatorAction_subgroup_conj_map_eq_commutator Z d.torus hnorm]
  exact disjoint_map Z.subtype_injective hc.disjoint

/-- In particular the global central factor is disjoint from displacement. -/
theorem DiagonalSection.omegaCenter_center_disjoint (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Disjoint (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ center L)
      ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ := by
  apply (d.omegaCenter_coprime_disjoint S hS hn hF).mono_left
  exact inf_le_inf_left _ (center_le_centralizer _)

end CFSG.Quasithin.ChapterE.Section06.L2Torus
