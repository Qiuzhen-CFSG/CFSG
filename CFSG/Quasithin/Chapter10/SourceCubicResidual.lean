module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.SpecificGroups.Janko1.Model.Certification
/-!
# The cubic residual in the original nonnormal component configuration

The full maximal normalizer M=N_G(L₀) is SQTK and contains L as a genuine
nonnormal C-component. The four-model source classification therefore applies
inside M. When three divides |L/O₂(L)|, Suzuki is excluded, and the remaining
models have simple quotient. The existing two-orbit residual theorem then
identifies O^{3′}(M) with the actual original Sylow orbit L₀=⟨Lᵀ⟩.

Consequently a subgroup normalizer whose intersection with L₀ has order prime
to three has the same property in M. This is the cubic-order exclusion used
in the A₅ branch of 10.2.1. The model-dependent intersection bound is kept
explicit; the full normalization theorem 10.0.1 still requires its source
module and weak-closure arguments.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 10.1.3 and the proof of 10.2.1, printed pp.742–743, using 1.2.1–2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
private theorem simple_of_linear {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hz : center Q = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem simple_of_three_dvd_model {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (hm : NonnormalCComponentModel Q) (hd : 3 ∣ Nat.card Q) :
    IsSimpleGroup Q := by
  cases hm with
  | linear_even n hn he => exact simple_of_linear he
  | linear_prime p hp ho he => exact simple_of_linear he
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd).elim
  | janko he => exact he.some.isSimpleGroup

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The cubic instance of original 10.1.3, with the same L, T and M.
The source quotient model supplies the displayed divisibility condition. -/
theorem source_nonnormal_cubic_residual
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    (primeToResidual 3 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_, hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := by
    intro ha
    exact hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi, hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let e := subgroupOfEquivOfLe hLM
  let eqt := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqt.symm
  have hdA : 3 ∣ Nat.card (A ⧸ pCore 2 A) := (Nat.card_congr eqt.toEquiv).symm ▸ hd
  let := simple_of_three_dvd_model hm hdA
  have hr := nonnormal_component_threeResidual D.component_in_maximalLocal hi hdA
    (hlocal.stronglyQuasithin 3 (by decide) (by decide)) hm
  rw [hr, map_conjugateSpanBy, map_subgroupOf_eq_of_le hLM]
  have htop : (⊤ : Subgroup M).map M.subtype = M := by
    ext g
    exact ⟨fun ⟨m, _, he⟩ => he ▸ m.property, fun hg => ⟨⟨g, hg⟩, mem_top _, rfl⟩⟩
  rw [htop]
  apply le_antisymm (conjugateSpanBy_le (le_componentOrbit L T) le_rfl)
  change (⨆ t : (T : Subgroup G), L.map (MulAut.conj (t : G)).toMonoidHom) ≤ _
  apply iSup_le
  intro t x hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact subset_closure ⟨t, hTM t.property, l, hl, rfl⟩


/-- The normalizer consequence used in source 10.2.1: the quotient M/L₀
adds no cubic factor to the original normalizer intersection. -/
theorem source_nonnormal_normalizer_three_free
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (S : Subgroup G)
    (hc : Nat.Coprime 3 (Nat.card (localOrbit T L ⊓ normalizer (S : Set G) : Subgroup G))) :
    Nat.Coprime 3 (Nat.card (D.maximalLocal ⊓ normalizer (S : Set G) : Subgroup G)) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let K := M ⊓ normalizer (S : Set G)
  have hR : R.subgroupOf M = primeToResidual 3 M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le R.le_normalizer, source_nonnormal_cubic_residual D hn hd]
  have hi : Nat.Coprime 3 (R.relIndex K) := by
    have hh := (primeToResidual_index_coprime (G := M) 3).coprime_dvd_right
      ((primeToResidual 3 M).relIndex_dvd_index_of_normal (K.subgroupOf M))
    rw [← hR, relIndex_subgroupOf (show K ≤ M from inf_le_left)] at hh
    exact hh
  have he : R ⊓ K = R ⊓ normalizer (S : Set G) := by
    change R ⊓ (M ⊓ normalizer (S : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr R.le_normalizer]
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (R ⊓ K) K bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right] at hcard
  change Nat.Coprime 3 (Nat.card K)
  rw [← hcard, he]
  exact hc.mul_right hi

end CFSG.Quasithin.Chapter10
