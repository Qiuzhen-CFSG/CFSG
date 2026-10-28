module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceRadicals
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Actor
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.CentralAction

/-!
# The selected Hermitian core actor is the canonical offender

The intrinsic E.2.10 actor A is contained in the original Sylow subgroup.
Its action is nontrivial by E.2.10(9), and its corank in the original
conjugate is the rank k of the selected quotient image. Consequently w ≤ k.
If the preceding parameter bounds give k ≤ w, corank additivity and the
minimality of w force A to equal the whole offender normalizer. The
E.2.10 kernel identity now applies to that exact offender. No separate
normalizer, kernel, offender-existence or Sylow-placement input is needed.

The final theorem combines this identification with Hermitian saturation
and the plane-root-group calculation. It retains n = 1, relative normality
inside the original T, and centralization by the original selected I.
The source right conjugator i is represented by left conjugation with i⁻¹.

This is a conditional application of 8.2.3–5. Selection from the normalized
chosen-module hypotheses, the bounds n ≤ w, k ≤ n, r ≥ 4n and H.4.4(3)
remain to be proved. They, the n > 1 exclusion and the field-four endgame
remain with qt-d-1222-nonmathieu-hermitian-exclusion. In particular this
module does not assert the complete source exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.10(9),
E.3.27–28 and 8.2.2–5, printed pp.222–225, 236–237 and714–717
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem selected_generator_proper
    (s : Selected H T M V I k i S) : V.subgroupOf I ≠ ⊤ := by
  intro he
  have hS : (S : Subgroup I) = ⊤ := top_unique (he ▸ s.twoConjugate.le_sylow)
  have hp : IsPGroup 2 (⊤ : Subgroup I) := hS ▸ S.isPGroup'
  have hc : pCore 2 I = ⊤ := top_unique (le_sSup ⟨inferInstance, hp⟩)
  have hq : coreImage I V = ⊥ := by
    apply bot_unique
    rintro _ ⟨v, hv, rfl⟩
    change QuotientGroup.mk' (pCore 2 I) v = 1
    apply (QuotientGroup.eq_one_iff v).mpr
    rw [hc]
    exact mem_top _
  have hr := s.rank_eq
  rw [hq, Representation.BinaryOffender.rank_bot] at hr
  have hk := s.positive
  omega

/-- The selected core actor lies in T, acts nontrivially and has corank k.
Its literal kernel is the central intersection, so it bounds w above. -/
theorem selected_core_actor_data (s : Selected H T M V I k i S)
    (hT : HypothesisE322 V T) :
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    A ≤ T ∧ ¬ A ≤ centralizer (V : Set G) ∧
      subgroupCorank (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom) A = k ∧
      A ⊓ centralizer (V : Set G) = V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ∧
      globalW V T ≤ k := by
  let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAT : A ≤ T := by
    have hm := map_mono (f := I.subtype) (pCore_isPGroup.le_sylow_of_normal S)
    rw [s.sylow_eq, subgroupOf_map_subtype] at hm
    exact inf_le_right.trans (hm.trans inf_le_left)
  have hAC : ¬ A ≤ centralizer (V : Set G) := by
    intro hc
    apply s.twoConjugate.commutator_V_A_ne_bot (selected_generator_proper s)
      s.characteristic_two
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro a ha v hv
    apply Subtype.ext
    have ham : (a : G) ∈ A := by
      dsimp only [A]
      rw [← selected_actor_image I M V hVI S i s.twoConjugate]
      exact mem_map_of_mem I.subtype ha
    exact hc ham v.val hv
  have hcor : subgroupCorank (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom) A = k := by
    rw [conjugate_core_corank I V i.val i.property,
      ← quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  refine ⟨hAT, hAC, hcor, selected_actor_kernel I M V hVI S i s.twoConjugate, ?_⟩
  rw [← hcor]
  exact globalW_le_corank_of_noncentralizing_normalizes hT i.val⁻¹
    (le_inf inf_le_left (hAT.trans hT.normalizes)) hAC

private theorem normalizer_eq_of_attaining_corank
    (hT : HypothesisE322 V T) (g : G) (A : Subgroup G)
    (hAN : A ≤ offenderNormalizer V g) (hAC : ¬ A ≤ centralizer (V : Set G))
    (hw : globalW V T = (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞)) :
    A = offenderNormalizer V g ∧ IsWOffenderAt V T g := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hNC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G) :=
    fun hc => hAC (hAN.trans hc)
  have hl := globalW_le_corank_of_noncentralizing_normalizes hT g le_rfl hNC
  rw [hw] at hl
  have hle := ENat.natCast_le_natCast.mp hl
  change subgroupCorank W A ≤ subgroupCorank W (offenderNormalizer V g) at hle
  have hsum := offender_corank_add (W := W) hAN
    (show offenderNormalizer V g ≤ W from inf_le_left)
  have hcor : subgroupCorank W (offenderNormalizer V g) = subgroupCorank W A := by omega
  let : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    offender_elementary_of_le (show offenderNormalizer V g ≤ W from inf_le_left)
  refine ⟨subgroup_eq_of_corank_zero hAN (by omega), ?_, ?_⟩
  · intro hc
    exact hAC ((hAN.trans inf_le_left).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))
  · exact hw.trans (congrArg (fun x : ℕ => (x : ℕ∞)) hcor.symm)

/-- Attainment of the weak-closure minimum identifies the selected actor
with the whole offender normalizer, retaining its kernel and original T. -/
theorem selected_offender_of_parameter_bound
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (hw : (k : ℕ∞) ≤ globalW V T) :
    globalW V T = k ∧ IsWOffenderAt V T i.val⁻¹ ∧
      offenderNormalizer V i.val⁻¹ =
        V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      offenderNormalizer V i.val⁻¹ ≤ T ∧
      offenderNormalizer V i.val⁻¹ ⊓ centralizer (V : Set G) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨hAT,hAC,hcor,hker,hupper⟩ := selected_core_actor_data s hT
  have hew := le_antisymm hupper hw
  obtain ⟨he,hOff⟩ := normalizer_eq_of_attaining_corank hT i.val⁻¹ _
    (le_inf inf_le_left (hAT.trans hT.normalizes)) hAC (by rw [hcor]; exact hew)
  exact ⟨hew,hOff,he.symm,he ▸ hAT,he ▸ hker⟩

/-- The preceding lower bound on w and upper bound on k force k = w = n
and identify the canonical offender without an E.2.11 normalizer callback. -/
theorem selected_hermitian_parameters
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ)
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n) :
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧
      offenderNormalizer V i.val⁻¹ ≤ T ∧
      offenderNormalizer V i.val⁻¹ ⊓ centralizer (V : Set G) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  have hupper := (selected_core_actor_data s hT).2.2.2.2
  have hnk : n ≤ k := ENat.natCast_le_natCast.mp (hw.trans hupper)
  have he : k = n := le_antisymm hk hnk
  obtain ⟨hew,hOff,_,hAT,hker⟩ := selected_offender_of_parameter_bound s hT (he ▸ hw)
  exact ⟨he,hew.trans (congrArg (fun x : ℕ => (x : ℕ∞)) he),hOff,hAT,hker⟩

/-- Saturation, cubic action, relative normality and centralization for the
same selected pair, with the offender and kernel inputs discharged. -/
theorem selected_hermitian_fixed_subgroup
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) :
    let A := offenderNormalizer V i.val⁻¹
    let U := V ⊓ centralizer (A : Set G)
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧ A ≤ T ∧
      A = V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      ⁅⁅⁅V,A⁆,A⁆,A⁆ = ⊥ ∧ rank (inducedAutomizer V A) = 4*n ∧ rank U = 4*n ∧
      globalR V ≤ ((5*n : ℕ) : ℕ∞) ∧
      U = A ⊓ centralizer (V : Set G) ∧ U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) := by
  obtain ⟨hkn,hew,hOff,hAT,hker⟩ := selected_hermitian_parameters s hT n hw hk
  have hkw : (k : ℕ∞) ≤ globalW V T := by rw [hkn,hew]
  have hA := (selected_offender_of_parameter_bound s hT hkw).2.2.1
  obtain ⟨ha,hu,_,hrupper⟩ := offender_parameters_of_coordinates V T n e j hj he
    hgeometry i.val⁻¹ hT hOff hew hr hker
  obtain ⟨huA,huZ,huT,huN,hIC⟩ := offender_fixed_normal_of_coordinates V T n e j hj he
    hgeometry i.val⁻¹ hT hOff hew hr hker hAT
  have hc := selected_actor_cubic I M V (s.generate ▸ le_sup_left) S i s.twoConjugate
  rw [← hA] at hc
  rw [s.generate] at hIC
  exact ⟨hkn,hew,hOff,hAT,hA,hc,ha,hu,hrupper,huA,huZ,huT,huN,hIC⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
