module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.SylowCoreRestriction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PPerfectHom

/-!
# Centralizer core restriction and the full faithful action

TI and point-centralizer control place the kernel on the diagonal span in
the original moved-factor normalizer. The local seed calculation puts the
span in the central two-core. The Frattini and residual arguments then prove
reducedness for the entire faithful centralizer action. If the full module
centralizes the span, relative normality puts it in the centralizer two-core.

This adapts the indicated `SourceLinearThreeReplacement/Geometry/CoreReduced`
proofs to the earlier natural pair. Local seed and full-action inputs are
explicit here and discharged in this directory's `Seed` and `FullAction`.
Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

public noncomputable section
-- Adapted from Geometry/Inputs.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The required parts of source 10.2.11(2--3), on literal fixed vectors
and literal X, K_z and V_z. The source hypotheses preceding that lemma are
explicit here, rather than replaced by an already constructed CentralizerData. -/
@[expose] def CoreReducedAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    (∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆) →
    ∀ a b : G, a ∈ ⁅D.fullModule,L⁆ →
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom →
      a ≠ 1 → b ≠ 1 →
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      a * b ∈ centerIn (T : Subgroup G) → orderOf (a * b) = 2 →
      D.fullModule ≤ (centralizer ({a * b} : Set G)).pCoreIn 2 ∧
      (centralizerSeed T L (a * b) < componentSpan T L (a * b) →
        IsPReduced 2 ((centralizerModule a b).subgroupOf
          (centralizer ({a * b} : Set G))))


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry

-- Adapted from Geometry/CoreReduced/Preparation.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- Precisely the earlier inputs of CoreReducedAt, on the original vectors. -/
structure Configuration (s : SourceLinearThreePair T D) (a b : G) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  fixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥
  ti : ∀ g : G, ⁅D.fullModule,L⁆ ⊓
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆
  first_mem : a ∈ ⁅D.fullModule,L⁆
  second_mem : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom
  first_ne : a ≠ 1
  second_ne : b ≠ 1
  first_fixed : a ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  second_fixed : b ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  central : a * b ∈ centerIn (T : Subgroup G)
  order : orderOf (a * b) = 2

namespace Configuration
variable (c : Configuration s a b)
include c

theorem full_le : D.fullModule ≤ centralizer ({a*b} : Set G) :=
  pair_full_le_diagonal_centralizer s c.first_mem c.second_mem

theorem span_le : centralizerModule a b ≤ centralizer ({a*b} : Set G) :=
  pair_centralizerModule_le s c.first_mem c.second_mem

omit [Finite G] c in
theorem seed_le : centralizerSeed T L (a*b) ≤ centralizer ({a*b} : Set G) :=
  (map_subtype_le _).trans inf_le_right

theorem sylow_le : (T : Subgroup G) ≤ centralizer ({a*b} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (c.central.2 t ht)

omit [Finite G] c in
theorem span_normal :
    ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

theorem kernel_le : centralizer ({a*b} : Set G) ⊓
    centralizer (centralizerModule a b : Set G) ≤ D.maximalLocal :=
  centralizerModule_centralizer_le s c.first_mem c.first_ne

omit [Finite G] c in
theorem kernel_normalized : centralizer ({a*b} : Set G) ≤ normalizer
    ((centralizer ({a*b} : Set G) ⊓ centralizer (centralizerModule a b : Set G) :
      Subgroup G) : Set G) :=
  (le_inf (centralizer ({a*b} : Set G)).le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

/-- The full source bound C_Gz(V_z) ≤ N_M(V₁), using TI rather than
only the weaker point-centralizer bound C_G(a) ≤ M. -/
theorem kernel_le_moved_normalizer : centralizer ({a*b} : Set G) ⊓
    centralizer (centralizerModule a b : Set G) ≤
      D.maximalLocal ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  refine le_inf c.kernel_le ?_
  intro g hg
  have ha : a ∈ centralizerModule a b :=
    le_conjugateSpanBy _ _ (mem_sup_left (mem_zpowers a))
  have hfix : (MulAut.conj g) a = a := by
    change g*a*g⁻¹ = a
    rw [← hg.2 a ha, mul_inv_cancel_right]
  rcases c.ti g with hd | he
  · have hai : a ∈ ⁅D.fullModule,L⁆ ⊓
        (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom :=
      ⟨c.first_mem, hfix ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom c.first_mem⟩
    exact (c.first_ne (mem_bot.mp (hd ▸ hai))).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr he

/-- The involution centralizer has a self-centralizing intrinsic two-core. -/
theorem characteristic_two :
    centralizer ({a*b} : Set G) ⊓
      centralizer ((centralizer ({a*b} : Set G)).pCoreIn 2 : Set G) ≤
        (centralizer ({a*b} : Set G)).pCoreIn 2 := by
  have hp : IsPGroup 2 (zpowers (a*b)) := by
    let : IsElementaryAbelian 2 (zpowers (a*b)) := IsElementaryAbelian.zpowers_of_pow_eq_one
      (by rw [← c.order]; exact pow_orderOf_eq_one _)
    exact IsElementaryAbelian.isPGroup 2 _
  have hn : zpowers (a*b) ≠ ⊥ := by
    intro he
    have hz : a*b = 1 := mem_bot.mp (he ▸ mem_zpowers (a*b))
    have hh := c.order
    rw [hz, orderOf_one] at hh
    omega
  have ht : IsTwoLocal (centralizer ({a*b} : Set G)) := by
    refine ⟨zpowers (a*b), hn, hp, ?_⟩
    exact (normalizer_zpowers_eq_centralizer_of_order_two _ c.order).symm
  exact Chapter1.twoLocal_mem_He_of_sylow_le T
    (D.simpleQTKE.evenCharacteristic T) ht c.sylow_le

/-- The opening reduction of 10.2.11(3): if V centralizes V_z, it is
normal in C_Gz(V_z), and hence lies in O₂(G_z). -/
theorem full_core_of_centralizes
    (hc : D.fullModule ≤ centralizer (centralizerModule a b : Set G)) :
    D.fullModule ≤ (centralizer ({a*b} : Set G)).pCoreIn 2 := by
  let H := centralizer ({a*b} : Set G)
  let C := H ⊓ centralizer (centralizerModule a b : Set G)
  have hVC : D.fullModule ≤ C := le_inf c.full_le hc
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hVN : C ≤ normalizer (D.fullModule : Set G) :=
    c.kernel_le.trans D.maximalLocal_normalizes_fullModule
  have hVQ : D.fullModule ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hVC hVN
  have hHN : H ≤ normalizer (C : Set G) := kernel_normalized
  exact hVQ.trans (pCoreIn_mono_of_normalizes inf_le_left hHN)

/-- The general A.1.6 restriction, before the specific X T calculation. -/
theorem core_le_seedJoin_core : (centralizer ({a*b} : Set G)).pCoreIn 2 ≤
    (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 :=
  pCoreIn_le_of_sylow_le T le_sup_right (sup_le (seed_le (T := T) (L := L) (a := a) (b := b)) c.sylow_le)

/-- The local core bound O₂(XT) ≤ T₁ supplies all of 10.2.11(1)'s
central-core containment. The local model calculation is kept explicit. -/
theorem span_central_core_of_seedJoin_core
    (hcore : (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) := by
  let H := centralizer ({a*b} : Set G)
  let Q := H.pCoreIn 2
  let E := zpowers a ⊔ zpowers b
  have hQC : E ≤ centralizer (Q : Set G) := sup_le
    (zpowers_le.mpr (centralizer_le (c.core_le_seedJoin_core.trans hcore) c.first_fixed))
    (zpowers_le.mpr (centralizer_le (c.core_le_seedJoin_core.trans hcore) c.second_fixed))
  have hHQ : H ≤ normalizer (Q : Set G) := by
    simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hWC : centralizerModule a b ≤ centralizer (Q : Set G) :=
    conjugateSpanBy_le hQC (hHQ.trans (normalizer_le_normalizer_centralizer _))
  exact le_inf ((le_inf c.span_le hWC).trans c.characteristic_two) hWC

/-- Once in the central core, the literal span is elementary abelian;
its exponent follows from its original two involution generators. -/
theorem span_elementary_of_central_core
    (hc : centralizerModule a b ≤
      centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2)) :
    IsElementaryAbelian 2 (centralizerModule a b) := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hEV : zpowers a ⊔ zpowers b ≤ D.fullModule :=
    sup_le (zpowers_le.mpr (pair_moved_le s c.first_mem))
      (zpowers_le.mpr (pair_partner_le s c.second_mem))
  have hcomm : IsMulCommutative (centralizerModule a b) :=
    le_centralizer_iff_isMulCommutative.mp
      ((hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left)))
  unfold centralizerModule conjugateSpanBy at hcomm ⊢
  let := hcomm
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨g, _, e, he, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian e (hEV he), mul_one, mul_inv_cancel]

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced

-- Adapted from Geometry/CoreReduced/Inputs.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- Local seed calculations, before either reducedness or the V-core bound.
The normality clause is the consequence of X = O^{3'}(G_z ∩ M) on a
normal intermediate subgroup, not an assumption that X is normal in G_z. -/
structure SeedAnalysis (c : Configuration s a b) : Prop where
  core_bound : (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    (T : Subgroup G) ⊓ normalizer (L : Set G)
  commutator : ∀ R : Subgroup G, R ≤ (T : Subgroup G) →
    (T : Subgroup G) ≤ normalizer (R : Set G) →
    ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ⁅centralizerSeed T L (a*b), R⁆ = centralizerSeed T L (a*b)
  normal_in_kernel : ∀ C : Subgroup G,
    C ≤ centralizer ({a*b} : Set G) ⊓ D.maximalLocal →
    centralizer ({a*b} : Set G) ≤ normalizer (C : Set G) →
    centralizerSeed T L (a*b) ≤ C →
      centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)
  fixes : centralizerSeed T L (a*b) ≤ centralizer
    ((zpowers a ⊔ zpowers b : Subgroup G) : Set G)
  generates : D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔
    (zpowers a ⊔ zpowers b)

/-- The independent original local-group calculation. -/
@[expose] def SeedAnalysisAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D) (a b : G) (c : Configuration s a b),
      SeedAnalysis c

/-- The final representation contradiction in 10.2.11(3). The independent
local calculation remains an explicit premise, allowing its producer to run
alongside this conditional consumer. Reducedness
belongs to the entire literal G_z action; it is not transferred to K_z T.
The conclusion states the centralization needed by the proved core reduction. -/
@[expose] def FullActionCentralizationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D) (a b : G) (c : Configuration s a b),
    SeedAnalysis c →
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) →
    centralizerSeed T L (a*b) < componentSpan T L (a*b) →
    IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) →
    D.fullModule ≤ centralizer (centralizerModule a b : Set G)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced

-- Adapted from Geometry/CoreReduced/Reduced.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}
namespace Configuration
variable (c : Configuration s a b) (h : SeedAnalysis c)
include c

omit [Finite G] c in
/-- The literal seed is normal exactly when its G_z span is itself. -/
theorem seed_span_eq_of_normalizes
    (hn : centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)) :
    componentSpan T L (a*b) = centralizerSeed T L (a*b) :=
  le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)

include h in
/-- The seed normality case of the full-module centralization argument. -/
theorem full_centralizes_of_seed_normalizes
    (hn : centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)) :
    D.fullModule ≤ centralizer (centralizerModule a b : Set G) := by
  have hXW : centralizerSeed T L (a*b) ≤ centralizer (centralizerModule a b : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hn h.fixes
  have hCW : centralizer ({a*b} : Set G) ≤
      normalizer (centralizer (centralizerModule a b : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  have hVW := (commutator_mono le_rfl hXW).trans
    (le_normalizer_iff_commutator_le_right.mp (c.full_le.trans hCW))
  have hcentral := c.span_central_core_of_seedJoin_core h.core_bound
  have hWW : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hcentral.trans inf_le_right).trans (centralizer_le (hcentral.trans inf_le_left))
  exact h.generates.le.trans (sup_le hVW ((le_conjugateSpanBy _ _).trans hWW))

include h in
/-- Source 10.2.11(2), with its full faithful action quotient. -/
theorem reduced_of_seedAnalysis
    (hlt : centralizerSeed T L (a*b) < componentSpan T L (a*b)) :
    IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) := by
  let H := centralizer ({a*b} : Set G)
  let W := centralizerModule a b
  let X := centralizerSeed T L (a*b)
  let U := W.subgroupOf H
  let : U.Normal := span_normal
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let P := pCore 2 (H ⧸ C)
  let N := P.comap q
  let J := N.map H.subtype
  let R := J ⊓ (T : Subgroup G)
  have hHJ : H ≤ normalizer (J : Set G) := by
    simpa only [J, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using N.le_normalizer_map H.subtype
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (c.sylow_le.trans hHJ) (T : Subgroup G).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hJU : R ≤ (T : Subgroup G) := inf_le_right
  have hWJ : W ≤ centralizer (J : Set G) := by
    by_cases hR : R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)
    · have hEJ : zpowers a ⊔ zpowers b ≤ centralizer (J : Set G) := by
        have hPC : P ≤ ((T.subtype c.sylow_le : Sylow 2 H) : Subgroup H).map q :=
          pCore_isPGroup.le_sylow_of_normal
            ((T.subtype c.sylow_le).mapSurjective (QuotientGroup.mk'_surjective C))
        have hER : zpowers a ⊔ zpowers b ≤ centralizer (R : Set G) :=
          sup_le (zpowers_le.mpr (centralizer_le hR c.first_fixed))
            (zpowers_le.mpr (centralizer_le hR c.second_fixed))
        intro e he j hj
        obtain ⟨n, hn, rfl⟩ := hj
        obtain ⟨t, ht, heq⟩ := hPC hn
        have htN : t ∈ N := by
          change q t ∈ P
          rw [heq]
          exact hn
        have htJ : (t:G) ∈ J := mem_map_of_mem H.subtype htN
        have htR : (t:G) ∈ R := ⟨htJ, ht⟩
        have hnC : t⁻¹*n ∈ C := by
          apply (QuotientGroup.eq_one_iff _).mp
          change q (t⁻¹*n) = 1
          rw [map_mul, map_inv, heq, inv_mul_cancel]
        have heW : e ∈ W := le_conjugateSpanBy _ _ he
        have hc := congrArg Subtype.val (hnC (⟨e,c.span_le heW⟩ : H) heW)
        have hte := hER he t htR
        change e * ((t:G)⁻¹ * (n:G)) = ((t:G)⁻¹ * (n:G)) * e at hc
        calc
          (n:G) * e = (t:G) * (((t:G)⁻¹ * (n:G)) * e) := by group
          _ = (t:G) * (e * ((t:G)⁻¹ * (n:G))) := by rw [hc]
          _ = e * (n:G) := by rw [← mul_assoc, hte]; group
      exact conjugateSpanBy_le hEJ (hHJ.trans (normalizer_le_normalizer_centralizer _))
    · have hXR : ⁅X,R⁆ = X := h.commutator R hJU hTR hR
      have hXJ : X ≤ J := hXR.symm.le.trans
        ((commutator_mono le_rfl (show R ≤ J from inf_le_left)).trans
          (le_normalizer_iff_commutator_le_right.mp ((seed_le (T := T) (L := L) (a := a) (b := b)).trans hHJ)))
      let f : X →* P := (q.comp (inclusion (seed_le (T := T) (L := L) (a := a) (b := b)))).codRestrict P (by
        intro x
        obtain ⟨n, hn, he⟩ := hXJ x.property
        have hn' : n = inclusion (seed_le (T := T) (L := L) (a := a) (b := b)) x := Subtype.ext he
        change q (inclusion (seed_le (T := T) (L := L) (a := a) (b := b)) x) ∈ P
        rw [← hn']
        exact hn)
      have hf : f = 1 := (isPPerfect_embedded_pResidual 2 _).hom_eq_one_of_isPGroup
        pCore_isPGroup f
      have hXC : X ≤ H ⊓ centralizer (W : Set G) := by
        intro x hx
        refine ⟨(seed_le (T := T) (L := L) (a := a) (b := b)) hx, ?_⟩
        have hh := congrArg (fun k : X →* P => ((k ⟨x,hx⟩ : P) : H ⧸ C)) hf
        have hk : (⟨x,(seed_le (T := T) (L := L) (a := a) (b := b)) hx⟩ : H) ∈ C := (QuotientGroup.eq_one_iff _).mp hh
        intro w hw
        exact congrArg Subtype.val (hk (⟨w,c.span_le hw⟩ : H) hw)
      have hnorm := h.normal_in_kernel (H ⊓ centralizer (W : Set G))
        (le_inf inf_le_left (c.kernel_le_moved_normalizer.trans inf_le_left))
        kernel_normalized hXC
      exact (hlt.ne (seed_span_eq_of_normalizes hnorm).symm).elim
  have hP : P = ⊥ := by
    apply bot_unique
    intro y hy
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C y
    apply (QuotientGroup.eq_one_iff _).mpr
    intro u hu
    exact Subtype.ext ((hWJ hu g (mem_map_of_mem H.subtype hy)).symm)
  let : IsElementaryAbelian 2 W :=
    c.span_elementary_of_central_core (c.span_central_core_of_seedJoin_core h.core_bound)
  exact ⟨inferInstance, IsElementaryAbelian.subgroupOf c.span_le, hP⟩

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced

-- Adapted from Geometry/CoreReduced/Assembly.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Discharge exactly the CoreReducedAt contract from its two source branches. -/
theorem coreReduced_of_source_inputs
    (hseed : SeedAnalysisAt T) (haction : FullActionCentralizationAt T) : CoreReducedAt T := by
  intro hmany L D s hfixed hti a b ha hb hane hbne haf hbf hz ho
  let c : Configuration s a b := ⟨hmany,hfixed,hti,ha,hb,hane,hbne,haf,hbf,hz,ho⟩
  have h := hseed L D s a b c
  have hcentral := c.span_central_core_of_seedJoin_core h.core_bound
  have hr := c.reduced_of_seedAnalysis h
  refine ⟨c.full_core_of_centralizes ?_, hr⟩
  by_cases he : centralizerSeed T L (a*b) = componentSpan T L (a*b)
  · have hn : centralizer ({a*b} : Set G) ≤
        normalizer (centralizerSeed T L (a*b) : Set G) := by
      rw [he]
      exact le_normalizer_conjugateSpanBy _ _
    exact c.full_centralizes_of_seed_normalizes h hn
  · have hlt : centralizerSeed T L (a*b) < componentSpan T L (a*b) :=
      lt_of_le_of_ne (le_conjugateSpanBy _ _) he
    exact haction L D s a b c h hcentral hlt (hr hlt)


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
