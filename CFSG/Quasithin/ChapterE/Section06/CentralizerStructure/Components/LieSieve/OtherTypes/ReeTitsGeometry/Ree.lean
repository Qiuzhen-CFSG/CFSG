module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.ReeModels
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.QuotientTransport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.BlockTransport
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoPowerStability

/-!
# Ree invariant parabolics for E.6.8

Mark the component Sylow as the standard positive subgroup of the genuine
Ree carrier. Conjugation by its relative normalizer in Q has two-power order
and preserves this Sylow, so the proved model stability fixes each full
parabolic, including its complementary torus. The two parabolics generate
the component and their images generate its image in the literal quotient
(L Q)/O₂(L Q).

The intrinsic self-centralizing two-cores give characteristic two for the
lifted joins with Q. The Suzuki join is three-free. For the linear join,
relative subnormality and two-perfection place a hypothetical chi-zero block
in the full linear parabolic, where the actual core-action rigidity excludes
it. The quotient-preimage identity retains the entire two-core kernel.

`ree_geometry` combines this construction with the proved component
normalization. It requires no additional model, stability, block-exclusion
or earlier Chapter 1 premise. The full E.6.7 application and final exclusion
remain with the OtherTypes assembly.

Source: Aschbacher–Smith, E.6.8, printed pp.247–248 (PDF pp.258–259),
F.1.12(I)(5) and (II), printed pp.263–264, and 2.3.9(7), printed p.526,
in `refs/quasithin.pdf` (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
open ReeF4 LargeLocalSeeds
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

omit [Finite G] in
/-- The relative Q-normalizer fixes both marked full parabolics. Its action
has two-power order because it comes from the actual two-group Q. -/
theorem reeParabolic_invariant {m : ℕ} (hm : 1 ≤ m)
    (e : L ≃* Model m)
    (he : (Q.subgroupOf L).map e.toMonoidHom = ConverseParabolics.unipotent m)
    (hQp : IsPGroup 2 Q) (s : Side) :
    componentNormalizer Q L ≤ normalizer ((reeParabolic e s).map L.subtype : Set G) := by
  intro q hq
  let n : normalizer (L : Set G) := ⟨q, hq.2⟩
  let a := L.normalizerMonoidHom n
  have ha : ∃ k : ℕ, a ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hQp.exists_pow_pow_eq_one (⟨q, hq.1⟩ : Q)
    refine ⟨k, ?_⟩
    have hg : q ^ (2 ^ k) = 1 := congrArg (fun z : Q => (z : G)) hk
    have hn : n ^ (2 ^ k) = 1 := Subtype.ext hg
    dsimp only [a]
    rw [← map_pow, hn, map_one]
  have hS : ∀ x : L, x ∈ Q.subgroupOf L ↔ a x ∈ Q.subgroupOf L := by
    intro x
    change (x : G) ∈ Q ↔ (L.normalizerMonoidHom n x : G) ∈ Q
    rw [normalizerMonoidHom_apply_apply_coe]
    change (x : G) ∈ Q ↔ q * (x : G) * q⁻¹ ∈ Q
    constructor
    · intro hx
      exact Q.mul_mem (Q.mul_mem hq.1 hx) (Q.inv_mem hq.1)
    · intro hx
      have hmem := Q.mul_mem (Q.mul_mem (Q.inv_mem hq.1) hx) hq.1
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hmem
  have hp := ConverseParabolics.marked_parabolic_invariant_of_twoPower hm e
    (Q.subgroupOf L) he a ha hS s
  have hmap : (reeParabolic e s).map a.toMonoidHom = reeParabolic e s := by
    ext x
    rw [mem_map_equiv]
    simpa only [reeParabolic, MulEquiv.apply_symm_apply] using hp (a.symm x)
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hf : ((MulAut.conj q : MulAut G) : G →* G).comp L.subtype =
      L.subtype.comp a.toMonoidHom := by
    ext x
    exact (normalizerMonoidHom_apply_apply_coe L n x).symm
  rw [Subgroup.map_map, hf, ← Subgroup.map_map, hmap]

/-- Construct the source quotient family, retaining the relative block
condition in each lifted join with Q. All intrinsic model premises are proved. -/
theorem ree_family_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At L m)
    (hN : Q ≤ normalizer (L : Set G)) : Nonempty (BlockFreeQuotientFamily Q L) := by
  obtain ⟨e, he⟩ := ree_sylow_marking h hU hL hQ hmodel
  have hcore := extension_core_le_Q h hU hL hQ hN
  have hQp : IsPGroup 2 Q := by rw [hQ]; exact T.isPGroup'.to_le inf_le_left
  let side : Fin 2 → Side := ![.suzuki, .linear]
  have hinv (i : Fin 2) : Q ≤ normalizer ((reeParabolic e (side i)).map L.subtype : Set G) := by
    simpa only [componentNormalizer_eq hN] using reeParabolic_invariant hm e he hQp (side i)
  let ep (i : Fin 2) : (reeParabolic e (side i)).map L.subtype ≃*
      ConverseParabolics.parabolic m (side i) :=
    ((reeParabolic e (side i)).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
      (e.symm.subgroupMap _).symm
  refine ⟨{
    count := 2
    subgroup := fun i => parabolicImage Q L (reeParabolic e (side i))
    le_component := fun i => parabolicImage_le _
    invariant := fun i => parabolicImage_invariant _ (reeParabolic_invariant hm e he hQp (side i))
    characteristic_two := ?_
    no_blocks := ?_
    generate := ?_ }⟩
  · intro i
    rw [preimage_join_eq _ hcore]
    apply join_characteristicTwo (hinv i) hQp
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (ep i)).mpr
    exact ConverseParabolics.parabolic_centralizer_pCore_le hm (side i)
  · intro i
    rw [preimage_join_eq _ hcore]
    fin_cases i
    · apply noChiZeroBlocks_of_three_free
      apply join_three_free (hinv 0) _ hQp
      rw [Nat.card_congr (ep 0).toEquiv]
      exact ConverseParabolics.suzuki_parabolic_three_free hm
    · apply noChiZeroBlocks_of_coreSection (coreSectionOfJoin (hinv 1) hQp (ep 1))
      exact ConverseParabolics.CoreActionRigidity.linear_rigidity hm
  · have hgen := congrArg (parabolicImage Q L) (reeParabolic_generate e)
    rw [parabolicImage_sup, parabolicImage_top] at hgen
    rw [← hgen]
    exact sup_le
      (le_iSup (fun i : Fin 2 => parabolicImage Q L (reeParabolic e (side i))) 0)
      (le_iSup (fun i : Fin 2 => parabolicImage Q L (reeParabolic e (side i))) 1)

/-- The Ree invariant-parabolic output of E.6.8 for the exact carrier in
`RankTwoTheoremC.ree`, with component normalization and every model premise
discharged. -/
theorem ree_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At L m) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hn := ree_normalizes h hU hL hQ hmodel
  exact ⟨hn, ree_family_of_normalizes h hU hL hQ hm hmodel hn⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
