module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Seed
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryTransvectionGroups.Basic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Recognition
public import Theory.Representation.SpecialLinearNatural.BinaryPointStabilizer

/-!
# The full-action contradiction before weak closure

The natural point centralizer is transitive outside its fixed line. Thus if
the full module does not centralize the diagonal span, the moved factor's
fixed subgroup is exactly that line, yielding a four-group of transvections.
The exchanger puts the two diagonal coordinates in the same orbit. Corrected
G.3.1 for the full faithful action with trivial two-core rules out their
nonzero fixed sum, forcing centralization by the full module.

The proofs adapt the indicated `SourceLinearThreeReplacement/Geometry/CoreReduced`
modules. The representation-only root and fixed-sum theorems are reused
unchanged. Reducedness is never transferred to a smaller acting subgroup.
Source: Aschbacher--Smith 10.2.11(3), printed p.754.
-/

public noncomputable section
-- Adapted from Geometry/CoreReduced/FullAction/Inputs.lean.
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction
open Subgroup Theory.GroupTheory
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The local fixed-subgroup calculation used by the full-action argument. -/
@[expose] def MovedFactorFixedAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D) (a b : G) (c : Configuration s a b),
    SeedAnalysis c →
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) →
    ¬ D.fullModule ≤ centralizer (centralizerModule a b : Set G) →
    ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction

-- Adapted from Geometry/CoreReduced/FullAction/Orbit.lean.
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}
namespace Configuration
variable (c : Configuration s a b)
include c

theorem exchange_first : (MulAut.conj s.exchange) a = b := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let e := MulAut.conj s.exchange
  have hd : Disjoint A B := pair_pair_disjoint s c.fixed
  have he : B.map e.toMonoidHom = A := by
    have hcomp : e.toMonoidHom.comp e.toMonoidHom =
        (MulAut.conj (s.exchange*s.exchange)).toMonoidHom := by
      ext x
      simp [e, MulAut.conj_apply, mul_assoc]
    have hpair := pair_moved_pair s (s.exchange*s.exchange)
      (le_normalizer_componentOrbit L T ((T : Subgroup G).mul_mem s.exchange_mem s.exchange_mem))
    have hBB : B.map e.toMonoidHom = A.map
        (MulAut.conj (s.exchange*s.exchange)).toMonoidHom := by
      change (A.map e.toMonoidHom).map e.toMonoidHom = _
      rw [map_map,hcomp]
    rw [hBB]
    rcases hpair with h | h
    · exact h
    · have hh : B.map e.toMonoidHom = A.map e.toMonoidHom := by
        rw [hBB]
        exact h
      have hBA := map_injective e.injective hh
      have ha : a ∈ A ⊓ B := ⟨c.first_mem,hBA.symm ▸ c.first_mem⟩
      exact (c.first_ne (mem_bot.mp (hd.eq_bot ▸ ha))).elim
  have haB : e a ∈ B := mem_map_of_mem e.toMonoidHom c.first_mem
  have hbA : e b ∈ A := he ▸ mem_map_of_mem e.toMonoidHom c.second_mem
  have hprod : e b * e a = a*b := by
    have hz : e (a*b) = a*b := by
      change s.exchange*(a*b)*s.exchange⁻¹=a*b
      rw [c.central.2 s.exchange s.exchange_mem,mul_inv_cancel_right]
    rw [map_mul] at hz
    have hab : Commute a b := by
      let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      exact congrArg Subtype.val (mul_comm
        (⟨a,pair_moved_le s c.first_mem⟩ : D.fullModule)
        ⟨b,pair_partner_le s c.second_mem⟩)
    exact (hab.map e.toMonoidHom).eq.symm.trans hz
  have hh : ((⟨e b,hbA⟩ : A),(⟨e a,haB⟩ : B)) =
      (⟨a,c.first_mem⟩,⟨b,c.second_mem⟩) := mul_injective_of_disjoint hd hprod
  exact congrArg (fun p : A × B => (p.2:G)) hh

theorem span_normalizes_moved
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2)) :
    centralizerModule a b ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hab : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  exact (le_inf c.span_le hab).trans (c.kernel_le_moved_normalizer.trans inf_le_right)

theorem moved_displacement_le_line
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hfix : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    ⁅⁅D.fullModule,L⁆,centralizerModule a b⁆ ≤ zpowers a := by
  have hab : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  have hAW : ⁅D.fullModule,L⁆ ≤ normalizer (centralizerModule a b : Set G) :=
    ((pair_moved_le s).trans c.full_le).trans (le_normalizer_conjugateSpanBy _ _)
  rw [← hfix]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp (c.span_normalizes_moved hc))
    ((le_normalizer_iff_commutator_le_right.mp hAW).trans hab)

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced

-- Adapted from Geometry/CoreReduced/FullAction/Action.lean.
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

variable (c : Configuration s a b)
variable [IsElementaryAbelian 2 (centralizerModule a b)]

@[expose] noncomputable def action (_c : Configuration s a b) : centralizer ({a*b} : Set G) →*
    BinaryLinear.GL (Additive (centralizerModule a b)) :=
  let lin : MulAut (centralizerModule a b) →* BinaryLinear.GL (Additive (centralizerModule a b)) :=
    { toFun := fun e => { e.toAdditive with map_smul' := ZMod.map_smul e.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  lin.comp ((centralizerModule a b).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy _ _)))

theorem action_apply (g : centralizer ({a*b} : Set G))
    (w : Additive (centralizerModule a b)) :
    ((action c g w).toMul : G) = (g:G) * (w.toMul:G) * (g:G)⁻¹ := rfl

theorem action_ker : (action c).ker =
    centralizer (((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) :
      Set (centralizer ({a*b} : Set G))) := by
  ext g
  change action c g = 1 ↔ _
  constructor
  · intro hg w hw
    have hh := congrArg (fun e => ((e (Additive.ofMul ⟨w.val,hw⟩)).toMul:G)) hg
    change (g:G)*(w:G)*(g:G)⁻¹ = (w:G) at hh
    exact Subtype.ext ((mul_inv_eq_iff_eq_mul.mp hh).symm)
  · intro hg
    ext w
    have hh := congrArg Subtype.val (hg ⟨w.toMul,c.span_le w.toMul.property⟩ w.toMul.property)
    change (w.toMul:G)*(g:G) = (g:G)*(w.toMul:G) at hh
    change (g:G)*(w.toMul:G)*(g:G)⁻¹ = (w.toMul:G)
    rw [← hh,mul_inv_cancel_right]

theorem action_twoCore
    (hr : IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G)))) :
    pCore 2 (action c).range = ⊥ := by
  let := hr.normal
  let e := (QuotientGroup.quotientMulEquivOfEq (action_ker c).symm).trans
    (QuotientGroup.quotientKerEquivRange (action c))
  rw [← pCore_map_iso 2 e, hr.quotient_pCore_eq_bot, Subgroup.map_bot]

@[expose] noncomputable def firstVector : Additive (centralizerModule a b) :=
  Additive.ofMul ⟨a,le_conjugateSpanBy _ _ (mem_sup_left (mem_zpowers a))⟩

@[expose] noncomputable def movedAction : (⁅D.fullModule,L⁆ : Subgroup G) →*
    BinaryLinear.GL (Additive (centralizerModule a b)) :=
  (action c).comp (inclusion ((pair_moved_le s).trans c.full_le))

include c in
omit [IsElementaryAbelian 2 (centralizerModule a b)] in
theorem first_order : orderOf a = 2 := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  exact orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian a (pair_moved_le s c.first_mem),c.first_ne⟩

theorem movedAction_card_ge_four
    (hk : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    4 ≤ Nat.card (movedAction c).range := by
  have hc := s.natural.card_section
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc
  norm_num at hc
  change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
    8 * Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) at hc
  have hn : 0 < Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) :=
    Nat.card_pos
  have hker : (movedAction c).ker = (zpowers a).subgroupOf ⁅D.fullModule,L⁆ := by
    ext v
    change action c (inclusion ((pair_moved_le s).trans c.full_le) v) = 1 ↔ _
    rw [← MonoidHom.mem_ker, action_ker c]
    change (∀ w : centralizer ({a*b} : Set G), (w:G) ∈ centralizerModule a b →
      w * inclusion ((pair_moved_le s).trans c.full_le) v =
        inclusion ((pair_moved_le s).trans c.full_le) v * w) ↔ _
    constructor
    · intro hv
      have hh : (v:G) ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) := by
        refine ⟨v.property,?_⟩
        intro w hw
        exact congrArg Subtype.val (hv ⟨w,c.span_le hw⟩ hw)
      exact hk ▸ hh
    · intro hv w hw
      have hh : (v:G) ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) :=
        hk.symm ▸ hv
      exact Subtype.ext (hh.2 w hw)
  have hcount := (movedAction c).ker.card_mul_index
  rw [index_ker, hker, Nat.card_congr
    (subgroupOfEquivOfLe (zpowers_le.mpr c.first_mem)).toEquiv,
    Nat.card_zpowers, first_order c] at hcount
  omega

theorem movedAction_le_roots
    (hd : ⁅⁅D.fullModule,L⁆,centralizerModule a b⁆ ≤ zpowers a) :
    (movedAction c).range ≤ rootGroup (action c).range (firstVector (a := a) (b := b)) := by
  rintro f ⟨v,rfl⟩
  refine ⟨⟨inclusion ((pair_moved_le s).trans c.full_le) v,rfl⟩,?_,?_⟩
  · intro w hw
    rcases (mem_centerLine_iff _ _).mp hw with rfl | rfl
    · exact map_zero _
    · apply Subtype.ext
      let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      have hh := congrArg Subtype.val (mul_comm
        (⟨v,pair_moved_le s v.property⟩ : D.fullModule)
        ⟨a,pair_moved_le s c.first_mem⟩)
      change (v:G)*a = a*(v:G) at hh
      change (v:G)*a*(v:G)⁻¹=a
      rw [hh,mul_inv_cancel_right]
  · intro w
    have hh := hd (commutator_mem_commutator v.property w.toMul.property)
    have hp : ⁅(v:G),(w.toMul:G)⁆ = 1 ∨ ⁅(v:G),(w.toMul:G)⁆ = a := by
      classical
      rw [mem_zpowers_iff_mem_range_orderOf, first_order c] at hh
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
      have hn2 : n < 2 := Finset.mem_range.mp hn
      interval_cases n <;> simp_all
    apply (mem_centerLine_iff _ _).mpr
    rcases hp with hp | hp
    · apply Or.inl
      apply Subtype.ext
      change ((v:G)*(w.toMul:G)*(v:G)⁻¹) / (w.toMul:G) = 1
      simpa only [commutatorElement_def,div_eq_mul_inv] using hp
    · apply Or.inr
      apply Subtype.ext
      change ((v:G)*(w.toMul:G)*(v:G)⁻¹) / (w.toMul:G) = a
      simpa only [commutatorElement_def,div_eq_mul_inv] using hp

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction

-- Adapted from Geometry/CoreReduced/FullAction/Source.lean.
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
open Subgroup Theory.GroupTheory BinaryTransvectionGroups
open scoped IsMulCommutative
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}


theorem contradiction_of_moved_factor (c : Configuration s a b)
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hr : IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))))
    (hker : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    False := by
  let : IsElementaryAbelian 2 (centralizerModule a b) := c.span_elementary_of_central_core hc
  let H := (action c).range
  let x := firstVector (a := a) (b := b)
  let y : Additive (centralizerModule a b) :=
    Additive.ofMul ⟨b,le_conjugateSpanBy _ _ (mem_sup_right (mem_zpowers b))⟩
  have hx : x ≠ 0 := fun hh => c.first_ne (congrArg (fun v => (v.toMul:G)) hh)
  have hroot : 2 < Nat.card (rootGroup H x) := by
    have hle := movedAction_le_roots c (c.moved_displacement_le_line hc hker)
    have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    have hfour := (movedAction_card_ge_four c hker).trans hbound
    change 4 ≤ Nat.card (rootGroup H x) at hfour
    omega
  have hH := root_hypotheses_of_card hx (action_twoCore c hr) hroot
  have hy : y ∈ MulAction.orbit H x := by
    let t : centralizer ({a*b} : Set G) := ⟨s.exchange,c.sylow_le s.exchange_mem⟩
    refine MulAction.mem_orbit_iff.mpr ⟨⟨action c t,⟨t,rfl⟩⟩,?_⟩
    exact Subtype.ext c.exchange_first
  have hzero := fixed_sum_eq_zero hH (action_twoCore c hr)
    (MulAction.mem_orbit_self x) hy (by
      rintro g ⟨t,rfl⟩
      apply Subtype.ext
      change (t:G)*(a*b)*(t:G)⁻¹ = a*b
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property))
  have hz : a*b=1 := congrArg (fun v : Additive (centralizerModule a b) => (v.toMul:G)) hzero
  have ho := c.order
  rw [hz,orderOf_one] at ho
  omega

theorem fullActionCentralization_of_moved_factor (hlocal : MovedFactorFixedAt T) :
    FullActionCentralizationAt T := by
  intro L D s a b c hseed hcentral _hlt hred
  by_contra hn
  exact contradiction_of_moved_factor c hcentral hred (hlocal L D s a b c hseed hcentral hn)

theorem coreReduced_of_moved_factor (hseed : SeedAnalysisAt T)
    (hlocal : MovedFactorFixedAt T) : Geometry.CoreReducedAt T :=
  coreReduced_of_source_inputs hseed (fullActionCentralization_of_moved_factor hlocal)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction

-- Adapted from Geometry/CoreReduced/FullAction/Natural/PointAction.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction.Natural
open Chapter3.Section02

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The literal point centralizer is transitive on the first factor outside its fixed line. -/
theorem exists_pointCentralizer_conjugating (c : Configuration s a b)
    (x y : (⁅D.fullModule,L⁆ : Subgroup G))
    (hx : (x : G) ≠ 1) (hxa : (x : G) ≠ a)
    (hy : (y : G) ≠ 1) (hya : (y : G) ≠ a) :
    ∃ g : G, g ∈ L ∧ g ∈ centralizer ({a} : Set G) ∧ (MulAut.conj g) (x : G) = y := by
  let f := s.natural.coordinates
  have hi : Function.Injective f := (Seed.natural_coordinates_bijective c).1
  have hn (v : (⁅D.fullModule,L⁆ : Subgroup G)) (hv : (v : G) ≠ 1) :
      (f v).toAdd ≠ 0 := by
    intro he
    exact hv (congrArg Subtype.val (hi (he.trans (map_one f).symm)))
  have hne (v : (⁅D.fullModule,L⁆ : Subgroup G)) (hv : (v : G) ≠ a) :
      (f v).toAdd ≠ (f ⟨a,c.first_mem⟩).toAdd :=
    fun he => hv (congrArg Subtype.val (hi he))
  obtain ⟨m, hma, hmx⟩ := Representation.BinaryPointStabilizer.exists_point_fixer
    (f ⟨a,c.first_mem⟩).toAdd (f x).toAdd (f y).toAdd
    (hn _ c.first_ne) (hn x hx) (hn y hy) (hne x hxa) (hne y hya)
  obtain ⟨q,hq⟩ := s.quotient.surjective m
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have heq : s.quotient (QuotientGroup.mk' (pCore 2 L) g) = m := by rw [hg,hq]
  have he (v : (⁅D.fullModule,L⁆ : Subgroup G)) :
      (f ⟨g * v * (g : G)⁻¹,
        (mem_normalizer_iff.mp (s.natural.normalized g.property) v).mp v.property⟩).toAdd =
      Representation.specialLinearNatural 3 m (f v).toAdd := by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, heq]
      using s.natural.equivariant g v
  have ha : (g : G) * a * (g : G)⁻¹ = a :=
    congrArg Subtype.val (hi ((he ⟨a,c.first_mem⟩).trans hma))
  refine ⟨g,g.property,?_,?_⟩
  · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp ha)
  · exact congrArg Subtype.val (hi ((he x).trans hmx))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction.Natural

-- Adapted from Geometry/CoreReduced/FullAction/Natural/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

theorem pointCentralizer_le_diagonal (c : Configuration s a b) :
    L ⊓ centralizer ({a} : Set G) ≤ centralizer ({a*b} : Set G) := by
  intro g hg
  have ha : Commute g a := mem_centralizer_singleton_iff.mp hg.2
  have hb : Commute g b := s.crossed c.second_mem g hg.1
  exact mem_centralizer_singleton_iff.mpr (ha.mul_right hb).eq

theorem moved_fixed_eq_line (c : Configuration s a b)
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hn : ¬ D.fullModule ≤ centralizer (centralizerModule a b : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a := by
  have hWC : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  have haC : a ∈ centralizer (centralizerModule a b : Set G) :=
    hWC (le_conjugateSpanBy _ _ (mem_sup_left (mem_zpowers a)))
  have hnorm : centralizer ({a*b} : Set G) ≤
      normalizer (centralizer (centralizerModule a b : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  apply le_antisymm ?_ (zpowers_le.mpr
    (show a ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) from
      ⟨c.first_mem, haC⟩))
  intro x hx
  by_contra hxline
  have hx1 : x ≠ 1 := fun he => hxline (he ▸ (zpowers a).one_mem)
  have hxa : x ≠ a := fun he => hxline (he ▸ mem_zpowers a)
  have hAC : ⁅D.fullModule,L⁆ ≤ centralizer (centralizerModule a b : Set G) := by
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ (centralizer (centralizerModule a b : Set G)).one_mem
    by_cases hya : y = a
    · exact hya ▸ haC
    obtain ⟨g, hgL, hga, hgy⟩ := exists_pointCentralizer_conjugating c
      ⟨x,hx.1⟩ ⟨y,hy⟩ hx1 hxa hy1 hya
    have hgN := hnorm (pointCentralizer_le_diagonal c ⟨hgL,hga⟩)
    have hh := (mem_normalizer_iff.mp hgN x).mp hx.2
    change g * x * g⁻¹ = y at hgy
    exact hgy ▸ hh
  apply hn
  rw [s.generated]
  refine sup_le hAC ?_
  rintro _ ⟨y,hy,rfl⟩
  exact (mem_normalizer_iff.mp (hnorm (c.sylow_le s.exchange_mem)) y).mp (hAC hy)

/-- The fixed-line input, with no irreducibility or fixed-subgroup premise. -/
theorem movedFactorFixedAt (T : Sylow 2 G) : MovedFactorFixedAt T := by
  intro L D s a b c _hseed hc hn
  exact moved_fixed_eq_line c hc hn

/-- The full-action contradiction now has its original natural input proved. -/
theorem fullActionCentralizationAt (T : Sylow 2 G) : FullActionCentralizationAt T :=
  fullActionCentralization_of_moved_factor (movedFactorFixedAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.FullAction.Natural
