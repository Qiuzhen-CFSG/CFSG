module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherNormalizer
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# The faithful radical action in the dimension-three branch of 12.2.25

Set R=C_T(U), retaining the original ambient subgroups. The common
centralizer calculation makes R elementary abelian. Its Sylow centralizer
is R, so characteristic two in N_G(R) and C_G(R) gives C_G(R)=R.
The literal quotient N_G(R)/R consequently acts faithfully on R.
The disjoint splitting R=U C_T(L) gives |R|=16 or 32. Orbit counting for
the prime-order action on U also gives |P|=3 or 5. The quotient Sylow
is the image of the original T, and the original H normalizes R.

Once the transfer calculation identifies C_T(L) with C_T(I), their
already trivial intersection kills both. The existing dimension-independent
normalizer proof then gives N_G(L)=L, O₂(L)=V and C_G(U)=U. The last
application feeds actual parabolic factors into the existing Gaschütz
consumer. The transfer, involution fusion, small linear-group recognition,
and construction of those factors remain explicit source obligations;
this module does not assert completion of 12.2.25.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.25--26, printed p.806, using the common calculation on p.805.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

namespace ThreeRigidity

/-- The elementary radical used in the original dimension-three argument. -/
abbrev radical (T : Sylow 2 G) (U : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer (U : Set G)

/-- The quotient by R inside its own normalizer, rather than inside G. -/
abbrev NormalizerQuotient (T : Sylow 2 G) (U : Subgroup G) :=
  HigherRigidity.NormalizerQuotient (radical T U)

/-- The canonical quotient map for the faithful radical action. -/
def quotient (T : Sylow 2 G) (U : Subgroup G) :
    normalizer (radical T U : Set G) →* NormalizerQuotient T U :=
  HigherRigidity.quotient (radical T U)

omit [Finite G] in
theorem quotient_surjective : Function.Surjective (quotient T U) :=
  QuotientGroup.mk'_surjective _

/-- The literal image of a subgroup intersected with the radical normalizer. -/
def image (T : Sylow 2 G) (U K : Subgroup G) : Subgroup (NormalizerQuotient T U) :=
  (K.subgroupOf (normalizer (radical T U : Set G))).map (quotient T U)

/-- Fixed-point-free prime-order conjugation on U forces p to divide fifteen. -/
theorem odd_prime_three_or_five (C : CyclicLocalAnalysis T L V 3 H P U) :
    Nat.card P = 3 ∨ Nat.card P = 5 := by
  let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
  have hP : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  have hn : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hc := card_modEq_card_inf_centralizer P U hP hn
  have hU : Nat.card U = 16 := by simpa using C.dimension
  rw [hU, C.fixed, card_bot] at hc
  have hd : Nat.card P ∣ 15 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 16)).mp hc.symm
  rcases C.prime_order.dvd_mul.mp (show Nat.card P ∣ 3 * 5 from hd) with h3 | h5
  · exact Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h3 |>.resolve_left
      C.prime_order.ne_one)
  · exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp h5 |>.resolve_left
      C.prime_order.ne_one)

omit [Finite G] in
theorem sylow_normalizes_radical (C : CyclicLocalAnalysis T L V 3 H P U) :
    (T : Subgroup G) ≤ normalizer (radical T U : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
    inf_normalizer_le_normalizer_inf

theorem overgroup_normalizes_radical (C : CyclicLocalAnalysis T L V 3 H P U) :
    H ≤ normalizer (radical T U : Set G) := by
  let := C.elementary
  rw [C.overgroup]
  refine sup_le ?_ (sylow_normalizes_radical C)
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [C.sylow_centralizer_core_commutator (by decide)]
  exact le_inf C.core_le_sylow (le_centralizer U)

/-- The Sylow subgroup of N_G(R)/R induced by the original T. -/
def quotientSylow (C : CyclicLocalAnalysis T L V 3 H P U) :
    Sylow 2 (NormalizerQuotient T U) :=
  (T.subtype (sylow_normalizes_radical C)).mapSurjective quotient_surjective

theorem quotientSylow_coe (C : CyclicLocalAnalysis T L V 3 H P U) :
    (quotientSylow C : Subgroup (NormalizerQuotient T U)) = image T U (T : Subgroup G) := rfl

theorem radical_selfCentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    centralizer (radical T U : Set G) = radical T U := by
  let R := radical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let : IsElementaryAbelian 2 U := C.elementary
  have hUR : U ≤ R := le_inf C.core_le_sylow (le_centralizer U)
  have hne : R ≠ ⊥ := ne_bot_of_le_ne_bot (C.core_ne_bot (by decide)) hUR
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := sylow_normalizes_radical C
  have hRC : R ≤ centralizer (R : Set G) := le_centralizer R
  have he : (T : Subgroup G) ⊓ centralizer (R : Set G) = R :=
    le_antisymm (inf_le_inf_left _ (centralizer_le hUR)) (le_inf inf_le_left hRC)
  have hN : normalizer (R : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      ⟨R, hne, T.isPGroup'.to_le inf_le_left, rfl⟩ hTR
  have hCN : centralizer (R : Set G) ≤ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hC : centralizer (R : Set G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hN (ne_bot_of_le_ne_bot hne hRC) hCN
      (normal_subgroupOf_centralizer_normalizer (R : Set G)).isSubnormal
  have hcoreT : (normalizer (R : Set G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTR] using
      pCoreIn_le_sylow (normalizer (R : Set G)) (T.subtype hTR)
  have hcoreR : (centralizer (R : Set G)).pCoreIn 2 ≤ R := by
    apply (le_inf ?_ (pCoreIn_le 2 _)).trans he.le
    exact (pCoreIn_mono_of_normalizes hCN (normalizer_le_normalizer_centralizer R)).trans hcoreT
  exact le_antisymm
    ((le_inf le_rfl (centralizer_le hcoreR)).trans (hC.trans hcoreR)) hRC

theorem radical_card (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    Nat.card (radical T U) = 16 ∨ Nat.card (radical T U) = 32 := by
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZR : Z ≤ radical T U := le_sup_right.trans B.centralizer_split.symm.le
  have hn : Z ≤ normalizer (U : Set G) :=
    (hZR.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hc : Nat.card (radical T U) = Nat.card U * Nat.card Z := by
    rw [show radical T U = U ⊔ Z from B.centralizer_split]
    exact card_sup_eq_mul_of_normalizes_of_disjoint U Z hn B.centralizer_disjoint
  have hU : Nat.card U = 16 := by simpa using C.dimension
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have hsmall : Nat.card Z ≤ 2 := B.component_centralizer_card
  rw [hU] at hc
  omega

/-- The faithful source action, marked on every representative, in rank four or five. -/
theorem faithful_radical_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    ∃ k : ℕ, (k = 4 ∨ k = 5) ∧ Nat.card (radical T U) = 2 ^ k ∧
      ∃ a : NormalizerQuotient T U →* MulAut (radical T U),
        Function.Injective a ∧ ∀ (g : normalizer (radical T U : Set G))
          (r : radical T U), (a (quotient T U g) r : G) =
            (g : G) * (r : G) * (g : G)⁻¹ := by
  have he := radical_selfCentralizing h C B
  have ha : ∃ a : NormalizerQuotient T U →* MulAut (radical T U),
      Function.Injective a ∧ ∀ (g : normalizer (radical T U : Set G))
        (r : radical T U), (a (quotient T U g) r : G) =
          (g : G) * (r : G) * (g : G)⁻¹ :=
    ⟨HigherRigidity.action (radical T U) he.symm.le,
      HigherRigidity.action_injective (radical T U) he,
      HigherRigidity.action_quotient (radical T U) he.symm.le⟩
  rcases radical_card C B with hc | hc
  · exact ⟨4, Or.inl rfl, hc, ha⟩
  · exact ⟨5, Or.inr rfl, hc, ha⟩

end ThreeRigidity

omit [Finite G] in
theorem three_kernel_vanishing_of_centralizer_equality
    (B : LocalRigidityCentralizers T L V U P)
    (he : (T : Subgroup G) ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  simpa only [← he, inf_idem] using B.common_trivial

/-- The transfer conclusion discharges the central kernel in the original source setup. -/
theorem three_rigidity_of_centralizer_equality
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (he : (T : Subgroup G) ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      centralizer (U : Set G) = U := by
  have hzero := three_kernel_vanishing_of_centralizer_equality B he
  exact ⟨higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero,
    (higher_kernel_vanishing_consequences D B hzero).2.1,
    (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hzero).2⟩

/-- Public application to the existing parabolic and Gaschütz consumer. The
centralizer equality and parabolic factorization still require source proofs. -/
theorem three_split_of_centralizer_equality_and_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (he : (T : Subgroup G) ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G))
    (F : ParabolicFactorization L V U P) : SplitLinearConfiguration L V 3 := by
  have hh := three_rigidity_of_centralizer_equality h D structural A C B he
  exact splitLinearConfiguration_of_cyclic_factorization D A C (Or.inl rfl) hh.1 hh.2.1 F

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
