module
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeDefs
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOpposite
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The original right Cartan on the opposite core

The right Cartan B centralizes the cubic C and the original four-plane.
It normalizes the literal opposite-core geometry, acts trivially on I/S,
and normalizes the opposite image under the original faithful projection.

G.2.3 makes F = V[S,S] elementary with [F,C] contained in V. Coprime
action gives F = V C_F(C), and B normalizes the fixed factor. This retains
the additional original Cartan geometry for the remaining nonabelian S/V
case; it does not assert that the fixed factor lies in V.

Source: Aschbacher--Smith 5.1.22--23 and G.2.3,
printed pp.645--646 and 333--334, refs/quasithin.pdf.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ} {z : G}

private theorem local_point_centralized (d : LocalData T H C z) :
    H ≤ centralizer (zpowers z : Set G) := by
  have hc : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp d.point_mem).2.1 d.point_ne
  exact d.g2.H_le.trans (normalizer_le_centralizer_of_card_two _ hc)

theorem right_cartan_centralizes_cubic
    (c : LinearFieldCartan T L H A B C n) : B ≤ centralizer (C : Set G) := by
  let : IsCyclic A := c.left_cyclic
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact commutator_eq_bot_of_odd_normalizes_card_three C B c.cubic_card
    (by rw [c.right_card]; decide)
    (c.right_normalizes_left.trans (normalizer_le_normalizer_of_le_cyclic C A c.cubic_le))

theorem right_cartan_centralizes_plane
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z) :
    B ≤ centralizer (plane C z : Set G) := by
  exact le_centralizer_conjugateSpanBy_of_normalizes B (zpowers z) C
    ((le_centralizer_iff.mp (right_cartan_centralizes_cubic c)).trans
      (Subgroup.centralizer_le_normalizer _))
    ((c.right_le.trans inf_le_right).trans (local_point_centralized d))

omit [Finite G] in
private theorem normalizes_conjugate_of_centralizes
    (P Q R : Subgroup G) (hPQ : P ≤ normalizer (Q : Set G))
    (hPR : P ≤ centralizer (R : Set G)) (g : G) (hg : g ∈ R) :
    P ≤ normalizer (conjugate Q g : Set G) := by
  have hP : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp
      (((le_centralizer_iff.mp hPR).trans (Subgroup.centralizer_le_normalizer _))
        (R.inv_mem hg))
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hPQ
  rw [hP, map_equiv_normalizer_eq] at hh
  exact hh

theorem right_cartan_normalizes_opposite_geometry
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (g : G) (hg : g ∈ C) :
    let D := setup T (centralizer ({z} : Set G)) C z
    B ≤ normalizer (D.U : Set G) ∧
      B ≤ normalizer (conjugate D.U g : Set G) ∧
      B ≤ normalizer (D.I g : Set G) ∧
      B ≤ normalizer (D.S g : Set G) ∧
      B ≤ normalizer (D.W g : Set G) ∧
      B ≤ normalizer (conjugate (D.W g) g : Set G) ∧
      B ≤ normalizer (D.S₂ g : Set G) := by
  intro D
  have hBH : B ≤ D.H := by
    change B ≤ centralizer ({z} : Set G)
    have hBz := (c.right_le.trans inf_le_right).trans (local_point_centralized d)
    simpa only [zpowers_eq_closure, centralizer_closure] using hBz
  have hBU : B ≤ normalizer (D.U : Set G) :=
    hBH.trans (le_normalizer_conjugateSpanBy D.V D.H)
  have hBC := right_cartan_centralizes_cubic c
  have hBUg := normalizes_conjugate_of_centralizes B D.U C hBU hBC g hg
  have hBI : B ≤ normalizer (D.I g : Set G) :=
    (le_inf hBU hBUg).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hBS : B ≤ normalizer (D.S g : Set G) := hBI.trans
    (normalizer_le_normalizer_characteristic_image (D.I g) (pCore 2 (D.I g)))
  have hBW : B ≤ normalizer (D.W g : Set G) :=
    (le_inf hBU hBS).trans inf_normalizer_le_normalizer_inf
  exact ⟨hBU,hBUg,hBI,hBS,hBW,
    normalizes_conjugate_of_centralizes B (D.W g) C hBW hBC g hg,
    (le_inf hBU hBUg).trans inf_normalizer_le_normalizer_inf⟩

theorem right_cartan_commutator_le_core
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let D := setup T (centralizer ({z} : Set G)) C z
    ⁅D.I g,B⁆ ≤ D.S g := by
  intro D
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨_,_,_,hi,hgI⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨hBU,_,_,_,hBW,_,_⟩ := right_cartan_normalizes_opposite_geometry c d g hg
  have hUW := commutator_le_of_normalized_index_two D.U (D.W g) B inf_le_left hi hBU hBW
  have hUgS : ⁅conjugate D.U g,B⁆ ≤ D.S g := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hUW.trans inf_le_right)
    rw [map_commutator] at hh
    have hBmap : B.map (MulAut.conj g⁻¹).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp
        (((le_centralizer_iff.mp (right_cartan_centralizes_cubic c)).trans
          (Subgroup.centralizer_le_normalizer _)) (C.inv_mem hg))
    have hSmap : (D.S g).map (MulAut.conj g⁻¹).toMonoidHom = D.S g :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.binary_core_normalized g ((D.I g).inv_mem hgI))
    rwa [hBmap,hSmap] at hh
  have hN : D.I g ≤ normalizer (D.S g : Set G) := D.binary_core_normalized g
  have hu := le_commutatorPreimage (show D.U ≤ D.I g from le_sup_left)
    (hUW.trans (show D.W g ≤ D.S g from inf_le_right))
  have hug := le_commutatorPreimage (show conjugate D.U g ≤ D.I g from le_sup_right) hUgS
  exact (commutator_mono (sup_le hu hug) le_rfl).trans
    (commutator_commutatorPreimage_le (D.I g) B (D.S g) hN)

theorem right_cartan_normalizes_opposite_image
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (g : G) (hg : g ∈ C) :
    let D := setup T (centralizer ({z} : Set G)) C z
    (B.subgroupOf D.H).map (SpanAction.projection s) ≤
      normalizer ((((conjugate (D.W g) g).subgroupOf D.H).map
        (SpanAction.projection s)) : Set (SpanAction.Actor s)) := by
  intro D
  have hBN := (right_cartan_normalizes_opposite_geometry c d g hg).2.2.2.2.2.1
  exact (map_mono ((comap_mono hBN).trans
    ((conjugate (D.W g) g).le_normalizer_comap D.H.subtype))).trans
      (((conjugate (D.W g) g).subgroupOf D.H).le_normalizer_map (SpanAction.projection s))

omit [Finite G] in
private theorem normalizer_le_normalizer_derived (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp hx]

/-- The part of the original derived core outside the plane is detected
by an actual C-fixed elementary subgroup, invariant under the original B. -/
theorem core_commutator_fixed_split
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let D := setup T (centralizer ({z} : Set G)) C z
    let F := D.V ⊔ ⁅D.S g,D.S g⁆
    let X := F ⊓ centralizer (C : Set G)
    F = D.V ⊔ X ∧ IsElementaryAbelian 2 F ∧ X ≤ D.S₂ g ∧
      B ≤ normalizer (X : Set G) := by
  intro D F X
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨hN,hA,_σ,a,_,_,hVE,_hES,_,_hVN,_,hEC,hEE,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  let := hN
  let := hA
  have hderived : ⁅D.S g,D.S g⁆ ≤ D.S₂ g := by
    apply commutator_le.mpr
    intro x hx y hy
    apply (a.coordinates_eq_one_iff (⁅(⟨x,hx⟩ : D.S g),⟨y,hy⟩⁆)).mp
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hFE : F ≤ D.S₂ g := sup_le hVE hderived
  let : IsElementaryAbelian 2 (D.S₂ g) := hEE
  have hF : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le hFE
  let := hF
  have hCI : C ≤ D.I g := (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans hI.ge)
  have hCV : C ≤ normalizer (D.V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCS : C ≤ normalizer (D.S g : Set G) := hCI.trans (D.binary_core_normalized g)
  have hCF : C ≤ normalizer (F : Set G) :=
    (le_inf hCV (hCS.trans (normalizer_le_normalizer_derived _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hcomm : ⁅F,C⁆ ≤ D.V := (commutator_mono hFE hCI).trans hEC
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using c.cubic_card)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime F C hCF inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) C F hthree (IsElementaryAbelian.isPGroup 2 F))
  have hFX : F = D.V ⊔ X := by
    apply le_antisymm
    · calc
        F = ⁅F,C⁆ ⊔ X := hsplit
        _ ≤ D.V ⊔ X := sup_le_sup_right hcomm X
    · exact sup_le le_sup_left inf_le_left
  have hBS := (right_cartan_normalizes_opposite_geometry c d g hg).2.2.2.1
  have hBV : B ≤ normalizer (D.V : Set G) :=
    (right_cartan_centralizes_plane c d).trans (Subgroup.centralizer_le_normalizer _)
  have hBF : B ≤ normalizer (F : Set G) :=
    (le_inf hBV (hBS.trans (normalizer_le_normalizer_derived _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hBX : B ≤ normalizer (X : Set G) :=
    (le_inf hBF ((right_cartan_centralizes_cubic c).trans
      (centralizer (C : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  exact ⟨hFX,hF,inf_le_left.trans hFE,hBX⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
