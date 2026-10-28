module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryFaithfulSection
public import Theory.GroupAction.FrattiniSeed

/-!
# The omega-span action on the retained binary Frattini layer

Let X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, E = U intersect O₂(X), and N = ⟨Eˣ⟩.
Both N and U lie in the original Sylow T. Its normalization of U and
X's normalization of N give [N,U] ≤ E. Since U is elementary abelian,
this is a quadratic action, and [N,B] centralizes U because B fixes U.

On the SAME N/Φ(N), every U-displacement lies in the literal seed image,
which U fixes pointwise. Elements of E lie in N and thus act internally;
they disappear from this Frattini action. The earlier |U| ≤ 4|E| bound
therefore gives an action image of order at most four, with its full
kernel retained. The same quotient still has at least 2^24 elements.

This does not assert that the small action is nontrivial, that U is
X-invariant, or that N lies in U. Excluding this remaining configuration
and constructing the exceptional-component witness remain open.
Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638,
refs/quasithin.pdf, with the three-subgroups and Burnside-basis lemmas.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]
/-- The retained span and the original omega-span normalize each other.
Their commutator lies in the exact retained kernel, and the seven-moved
part of the retained span centralizes the whole omega-span. -/
theorem original_binary_triality_kernel_mutual_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    N ≤ normalizer (U : Set G) ∧ U ≤ normalizer (N : Set G) ∧
      ⁅N,U⁆ ≤ E ∧ ⁅⁅N,U⁆,U⁆ = ⊥ ∧ ⁅N,B⁆ ≤ centralizer (U : Set G) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨hu,_,_,hb,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hNQ,hXN,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hNU : N ≤ normalizer (U : Set G) :=
    (hNQ.trans hQT).trans (le_sup_right.trans (reduced_normalizes hu.reduced))
  have hUN : U ≤ normalizer (N : Set G) :=
    (hu.reduced_le_sylow.trans le_sup_right).trans hXN
  let := hu.reduced.2.1
  obtain ⟨hc,hq,hb⟩ := Subgroup.FrattiniSeed.commutator_control N U B hNU hUN inferInstance hb
  exact ⟨hNU,hUN,hc.trans (le_inf inf_le_right (inf_le_left.trans hNQ)),hq,hb⟩

/-- The original omega-span acts quadratically on the same Frattini layer.
The full action kernel contains E, its image has order at most four, and
all displacements lie in the literal seed image, fixed pointwise by U. -/
theorem original_binary_triality_kernel_quadratic_frattini
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    ∃ a : U →* MulAut N,
      (∀ (u : U) (v : N), ((a u v : N) : G) =
        (u : G) * (v : G) * (u : G)⁻¹) ∧
      let d := (quotientAut (frattini N)).comp a
      let q := QuotientGroup.mk' (frattini N)
      let V := (E.subgroupOf N).map q
      (∀ (u : U) (v : N ⧸ frattini N), d u v * v⁻¹ ∈ V) ∧
      (∀ (u : U) (v : V), d u v = v) ∧
      (∀ (u w : U) (v : N ⧸ frattini N),
        d u (d w v * v⁻¹) = d w v * v⁻¹) ∧
      E.subgroupOf U ≤ d.ker ∧ Nat.card d.range ≤ 4 ∧
      Nat.card V ≤ 256 ∧ 2^24 ≤ Nat.card (N ⧸ frattini N) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨_,hUN,hc,_,_⟩ := original_binary_triality_kernel_mutual_action
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let := hu.reduced.2.1
  obtain ⟨a,ha,hd,hf,hquad⟩ := Subgroup.FrattiniSeed.quotient_seed_action N U E
    inf_le_left hUN inferInstance hc
  obtain ⟨_,_,hsmall,_,_⟩ := original_binary_triality_kernel_frattini_seed
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hNQ,_,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let d := (quotientAut (frattini N)).comp a
  have hk : E.subgroupOf U ≤ d.ker :=
    (comap_mono (le_conjugateSpanBy E X)).trans
      (Subgroup.FrattiniSeed.frattini_conjugation_kernel N U ((isPGroup_pCoreIn 2 X).to_le hNQ) a ha)
  have hkcard : Nat.card E ≤ Nat.card d.ker := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe (show E ≤ U from inf_le_left)).toEquiv]
    exact card_le_of_le hk
  have hcount : Nat.card d.ker * Nat.card d.range = Nat.card U := by
    rw [←index_ker,d.ker.card_mul_index]
  have hbound := (original_binary_triality_elementary_kernel_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.1
  change Nat.card U ≤ 4 * Nat.card E at hbound
  have hkpos : 0 < Nat.card d.ker := Nat.card_pos
  have hdc : Nat.card d.range ≤ 4 := by nlinarith
  exact ⟨a,ha,hd,hf,hquad,hk,hdc,hsmall,original_binary_triality_kernel_frattini_twentyfour
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
