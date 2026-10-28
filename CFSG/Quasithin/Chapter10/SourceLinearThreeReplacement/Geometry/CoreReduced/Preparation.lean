module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Inputs
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.SylowCoreRestriction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original diagonal centralizer in 10.2.11

The configuration records only the earlier hypotheses supplied to CoreReducedAt.
The TI property strengthens the point-centralizer bound to N_M([V,L]).
The diagonal centralizer has characteristic two, and its literal conjugate
span is relatively normal. Centralization by V suffices for V to lie in its
two-core. A local bound on O₂(XT) further puts the span in Z(O₂(G_z)).

Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- Precisely the earlier inputs of CoreReducedAt, on the original vectors. -/
structure Configuration (s : SourceLinearThreeSurvivor T D) (a b : G) : Prop where
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
  survivor_full_le_diagonal_centralizer s c.first_mem c.second_mem

theorem span_le : centralizerModule a b ≤ centralizer ({a*b} : Set G) :=
  survivor_centralizerModule_le s c.first_mem c.second_mem

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
    sup_le (zpowers_le.mpr (survivor_moved_le s c.first_mem))
      (zpowers_le.mpr (survivor_partner_le s c.second_mem))
  have hcomm : IsMulCommutative (centralizerModule a b) :=
    le_centralizer_iff_isMulCommutative.mp
      ((hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left)))
  unfold centralizerModule conjugateSpanBy at hcomm ⊢
  let := hcomm
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨g, _, e, he, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian e (hEV he), mul_one, mul_inv_cancel]

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
