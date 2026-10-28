module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.SourceStructure.Action
public import Theory.GroupTheory.CentralPrimeQuotientJoin
/-!
# The source normalizer invariants for the J₂ root product

The local core orbit gives |C_G(E)| = 192. Its characteristic Sylow
subgroup R has order 64, so N_G(E) = N_G(R). The two cores induce distinct
involutions in Aut(E), giving its full order-six action and |N_G(R)| = 1152.

Write C = C_G(E). Relative normality gives [Q,C] ≤ Q ∩ C ≤ R and the
corresponding bound for the conjugate core. The full action yields
N_G(E) = ⟨Q,Q^g,C⟩. Since C/R has order three, its image is central in
N_G(R)/R. A nonidentity image gives the required central cubic coset.
The intrinsic-center action is transported through the actual equality
E = Z(R), and `image_invariants_of_localCensus` applies the result to the
literal conjugation image in any supplied root coordinates.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(5), 46.2–46.3 and
46.14, printed pp.29–30, 251, 257–258. The V of 8.15 is our marked E.
No normalizer complement, ambient group order, or second centralizer is used.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem normalizer_E_action_surjective (L : LocalCensus D) :
    Function.Surjective P.E.normalizerMonoidHom := by
  intro b
  obtain ⟨x, hx⟩ := coreJoinAction_surjective P L b
  exact ⟨inclusion (coreJoin_le_normalizer_E P L) x, hx⟩

theorem normalizer_E_card (L : LocalCensus D) :
    Nat.card (normalizer (P.E : Set G)) = 1152 := by
  let : IsKleinFour P.E := E_kleinFour P
  have hker : Nat.card P.E.normalizerMonoidHom.ker = 192 := by
    rw [normalizerMonoidHom_ker]
    exact (Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P.E : Set G))).toEquiv).trans
      (centralizer_E_card P)
  have hrange := MonoidHom.range_eq_top.mpr (normalizer_E_action_surjective P L)
  have hh := P.E.normalizerMonoidHom.ker.card_mul_index
  rw [hker, index_ker, hrange, card_top, IsKleinFour.card_mulAut] at hh
  exact hh.symm

theorem normalizer_R_card (L : LocalCensus D) :
    Nat.card (normalizer (P.R : Set G)) = 1152 := by
  rw [← normalizer_E_eq_normalizer_R P L]
  exact normalizer_E_card P L

noncomputable def centerEquivE : center P.R ≃* P.E :=
  ((center P.R).equivMapOfInjective P.R.subtype P.R.subtype_injective).trans
    (MulEquiv.subgroupCongr (E_center P))

theorem full_center_action (L : LocalCensus D) :
    ∀ b : MulAut (center P.R), ∃ n : normalizer (P.R : Set G),
      ∀ z : center P.R, P.R.normalizerMonoidHom n z = (b z : P.R) := by
  intro b
  let e := centerEquivE P
  obtain ⟨n, hn⟩ := normalizer_E_action_surjective P L (MulAut.congr e b)
  refine ⟨⟨n, (normalizer_E_eq_normalizer_R P L) ▸ n.property⟩, ?_⟩
  intro z
  apply Subtype.ext
  have hz := congrArg (fun t : P.E => (t : G)) (MulEquiv.congr_fun hn (e z))
  change (n : G) * ((z : P.R) : G) * (n : G)⁻¹ = ((b (e.symm (e z)) : P.R) : G) at hz
  rw [e.symm_apply_apply] at hz
  exact hz

theorem normalizer_E_eq_coreJoin_sup_centralizer (L : LocalCensus D) :
    normalizer (P.E : Set G) = coreJoin P ⊔ centralizer (P.E : Set G) := by
  apply le_antisymm
  · intro n hn
    obtain ⟨x, hx⟩ := coreJoinAction_surjective P L (P.E.normalizerMonoidHom ⟨n, hn⟩)
    let xN := inclusion (coreJoin_le_normalizer_E P L) x
    have he : P.E.normalizerMonoidHom xN = P.E.normalizerMonoidHom ⟨n, hn⟩ := hx
    have hk : xN⁻¹ * ⟨n, hn⟩ ∈ P.E.normalizerMonoidHom.ker := by
      change P.E.normalizerMonoidHom (xN⁻¹ * ⟨n, hn⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [normalizerMonoidHom_ker] at hk
    change (x : G)⁻¹ * n ∈ centralizer (P.E : Set G) at hk
    have hh := (coreJoin P ⊔ centralizer (P.E : Set G)).mul_mem
      (mem_sup_left x.property) (mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (coreJoin_le_normalizer_E P L) (Subgroup.centralizer_le_normalizer _)

theorem core_commutator_centralizer_le_R :
    ⁅ambientCore D.z, centralizer (P.E : Set G)⁆ ≤ P.R := by
  apply le_trans _ (show P.leftCore ≤ P.R from le_sup_left)
  rw [← core_inf_centralizer_E P]
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    rw [D.localType.normalizer_core, centralizer_E_eq]
    exact inf_le_left
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (core_le_normalizer_E P).trans (normalizer_le_normalizer_centralizer P.E)

theorem conjugateCore_commutator_centralizer_le_R (L : LocalCensus D) :
    ⁅P.conjugateCore, centralizer (P.E : Set G)⁆ ≤ P.R := by
  apply le_trans _ (show P.rightCore ≤ P.R from le_sup_right)
  rw [← conjugateCore_inf_centralizer_E P]
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    rw [P.normalizer_conjugateCore, centralizer_E_eq]
    exact inf_le_right
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (conjugateCore_le_normalizer_E P L).trans (normalizer_le_normalizer_centralizer P.E)

/-- A nonidentity central cubic coset in the literal normalizer quotient. -/
theorem central_cubic (L : LocalCensus D) :
    ∃ c : normalizer (P.R : Set G), (c : G) ∉ P.R ∧ (c : G) ^ 3 ∈ P.R ∧
      ∀ n : normalizer (P.R : Set G), ⁅(c : G), (n : G)⁆ ∈ P.R := by
  let N := normalizer (P.R : Set G)
  let C := centralizer (P.E : Set G)
  let T := P.R.subgroupOf N
  let A := (ambientCore D.z).subgroupOf N
  let B := P.conjugateCore.subgroupOf N
  let C' := C.subgroupOf N
  let π := QuotientGroup.mk' T
  have hQN : ambientCore D.z ≤ N :=
    (core_le_normalizer_E P).trans (normalizer_E_eq_normalizer_R P L).le
  have hBN : P.conjugateCore ≤ N :=
    (conjugateCore_le_normalizer_E P L).trans (normalizer_E_eq_normalizer_R P L).le
  have hCN : C ≤ N := centralizer_E_le_normalizer_R P
  have hgen : A ⊔ B ⊔ C' = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le hQN, map_subgroupOf_eq_of_le hBN,
      map_subgroupOf_eq_of_le hCN, ← MonoidHom.range_eq_map, N.range_subtype]
    exact (normalizer_E_eq_coreJoin_sup_centralizer P L).symm.trans
      (normalizer_E_eq_normalizer_R P L)
  have hc : Nat.card (C'.map π) = 3 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    change (P.R.subgroupOf N).relIndex (C.subgroupOf N) = 3
    rw [relIndex_subgroupOf hCN]
    change (P.R.subgroupOf C).index = 3
    have hr : Nat.card (P.R.subgroupOf C) = 64 :=
      (Nat.card_congr (subgroupOfEquivOfLe (R_le_centralizer_E P)).toEquiv).trans (P.R_card L)
    have hh := (P.R.subgroupOf C).card_mul_index
    rw [hr, centralizer_E_card P] at hh
    omega
  have ha : ⁅A, C'⁆ ≤ π.ker := by
    rw [QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro a ha c hc
    exact core_commutator_centralizer_le_R P
      (commutator_mem_commutator (show (a : G) ∈ ambientCore D.z from ha)
        (show (c : G) ∈ C from hc))
  have hb : ⁅B, C'⁆ ≤ π.ker := by
    rw [QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro b hb c hc
    exact conjugateCore_commutator_centralizer_le_R P L
      (commutator_mem_commutator (show (b : G) ∈ P.conjugateCore from hb)
        (show (c : G) ∈ C from hc))
  obtain ⟨c, _, hcout, hc3, hcomm⟩ :=
    exists_central_prime_coset_of_generators π A B C' hgen hc ha hb
  rw [QuotientGroup.ker_mk'] at hcout hc3 hcomm
  exact ⟨c, hcout, hc3, hcomm⟩

/-- The source invariants, for the literal normalizer action and quotient.
No root coordinates or splitting assumption is required. -/
theorem sourceInvariants (L : LocalCensus D) : SourceInvariants P :=
  ⟨normalizer_R_card P L, full_center_action P L, central_cubic P L⟩

/-- The source invariant producer applied to the parent's literal image contract. -/
theorem image_invariants_of_localCensus (L : LocalCensus D)
    (e : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    Matrix.PSL3Four.RootNormalizerModel.AutomizerInvariants (conjugation P e).range :=
  image_invariants P e (sourceInvariants P L)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
