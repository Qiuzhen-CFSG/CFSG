module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicDefs
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The cyclic specialization of the invariant odd-subgroup analysis

Once 12.2.23 gives prime order, the selected element generates P. The
characteristic two-core of its pair is therefore P-invariant, forcing
W = ⟨Uᴾ⟩ = U. The literal two-residual and T-invariance of V make the
pair normal in H. Its two disjoint axes give the order of U, and inversion
of the selected generator extends to all of P.

Finally Q = C_T(V) and U normalize each other, so [Q,U] lies in
U ∩ C_G(V) = U ∩ V. This is the core-displacement calculation preceding
12.2.24. Prime order, the invariant-odd construction and block recognition
remain explicit source obligations; no unconditional source theorem is
claimed here.
Source: Aschbacher--Smith, 12.2.21--24, printed pp.802--804.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

omit [Finite G] in
theorem generator_ne_one : g ≠ 1 := by
  intro he
  have hp := S.generator_order
  rw [he, orderOf_one] at hp
  exact S.prime.ne_one hp.symm

theorem cyclic_eq_of_prime_order (hc : Nat.card P = p) : zpowers g = P := by
  apply eq_of_le_of_card_ge (zpowers_le.mpr S.generator_mem)
  rw [Nat.card_zpowers, S.generator_order, hc]

omit [Finite G] in
theorem core_le_module : U ≤ W := by
  rw [S.generated]
  exact le_componentOrbit U P

theorem module_eq_of_prime_order (hc : Nat.card P = p) : W = U := by
  let I := cyclicPairJoin (zpowers g) U V
  have hPI : zpowers g ≤ I := le_sup_left.trans le_sup_left
  have hIn : I ≤ normalizer (U : Set G) := by
    rw [← S.pair_core]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPU : P ≤ normalizer (U : Set G) :=
    (S.cyclic_eq_of_prime_order hc) ▸ hPI.trans hIn
  rw [S.generated]
  exact le_antisymm
    (iSup_conjugates_le_of_le_normalizer U P U le_rfl hPU) (le_componentOrbit U P)

theorem inverts_of_prime_order (hc : Nat.card P = p) :
    ∀ x ∈ P, v * x * v⁻¹ = x⁻¹ := by
  intro x hx
  rw [← S.cyclic_eq_of_prime_order hc] at hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← conj_zpow, S.inverts_generator, inv_zpow]

theorem pair_normal_of_prime_order (hc : Nat.card P = p)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    H ≤ normalizer (cyclicPairJoin P U V : Set G) := by
  have he : (pResidual 2 H).map H.subtype = P ⊔ U := by
    rw [S.residual, S.module_eq_of_prime_order hc]
  have hTK : (T : Subgroup G) ≤ normalizer ((P ⊔ U : Subgroup G) : Set G) := by
    rw [← he]
    exact (S.overgroup ▸ (le_sup_right : (T : Subgroup G) ≤ P ⊔ (T : Subgroup G))).trans
      (le_normalizer_embedded_pResidual 2 H)
  rw [S.overgroup]
  exact sup_le
    ((le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
      (cyclicPairJoin P U V).le_normalizer)
    ((le_inf hTK hTV).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))

omit [Finite G] in
theorem core_card : Nat.card U = 2 ^ (2 * (d - 1)) := by
  let B := U ⊓ V
  let B' := B.map (MulAut.conj g).toMonoidHom
  have hBU : B ≤ U := inf_le_left
  have hB'U : B' ≤ U := S.core_generated ▸ (le_sup_right : B' ≤ B ⊔ B')
  let : IsElementaryAbelian 2 W := S.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le S.core_le_module
  have hn : B' ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact (le_centralizer U) (hB'U hb) a (hBU ha)
  have hd : Disjoint B B' := S.pair_disjoint.mono inf_le_right (map_mono inf_le_right)
  calc
    Nat.card U = Nat.card (B ⊔ B' : Subgroup G) :=
      congrArg (fun B : Subgroup G => Nat.card B) S.core_generated
    _ = Nat.card B * Nat.card B' := card_sup_eq_mul_of_normalizes_of_disjoint B B' hn hd
    _ = 2 ^ (2 * (d - 1)) := by
      rw [show Nat.card B' = Nat.card B from
        card_map_of_injective (MulAut.conj g).injective]
      rw [show Nat.card B = 2 ^ (d - 1) from S.hyperplane, ← pow_add]
      congr 1
      omega

/-- The commutator calculation immediately preceding 12.2.24. -/
theorem core_displacement_of_prime_order (hc : Nat.card P = p)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTH : (T : Subgroup G) ≤ H :=
    S.overgroup ▸ (le_sup_right : (T : Subgroup G) ≤ P ⊔ (T : Subgroup G))
  have hUc : U ≤ H.pCoreIn 2 := S.module_eq_of_prime_order hc ▸ S.in_core
  have hUT : U ≤ (T : Subgroup G) := by
    apply hUc.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    hTH.trans (S.module_eq_of_prime_order hc ▸ S.normalizes)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  have h1 : ⁅Q, U⁆ ≤ U :=
    le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hTU)
  have h2 : ⁅Q, U⁆ ≤ Q :=
    le_normalizer_iff_commutator_le_left.mp (hUT.trans hTQ)
  exact (le_inf h1 (h2.trans inf_le_right)).trans_eq S.action_kernel


theorem cyclic_of_prime_order (hc : Nat.card P = p)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hb : ChapterC.IsLinearTwoBlock L d) : CyclicLocalAnalysis T L V d H P U := by
  have hWU := S.module_eq_of_prime_order hc
  have hgP := S.cyclic_eq_of_prime_order hc
  refine {
    hstar := S.hstar
    prime_order := hc ▸ S.prime
    odd_order := hc ▸ S.odd_prime
    escapes := S.escapes
    overgroup := S.overgroup
    elementary := ?_
    in_core := hWU ▸ S.in_core
    core := hgP ▸ S.pair_core
    residual := hWU ▸ S.residual
    pair_normal := S.pair_normal_of_prime_order hc hTV
    pair := ⟨g, S.generator_mem, S.generator_ne_one,
      hgP ▸ S.pair_generated, S.core_generated⟩
    inverted := ⟨v, S.inverter_mem, S.inverter_outside, S.inverts_of_prime_order hc⟩
    moved := hWU ▸ S.moved
    fixed := hgP ▸ S.pair_fixed
    transvections := hWU ▸ S.transvections
    action_kernel := S.action_kernel
    hyperplane := S.hyperplane
    dimension := S.core_card
    block := hb }
  exact hWU ▸ S.elementary
end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

