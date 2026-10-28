module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverage
public import Theory.SpecificGroups.PSL3.LinearThreeNaturalScalars
public import Theory.GroupTheory.CoprimeSubgroupLift

/-!
# The original odd torus in every nonbinary degree

Lift diag(a²,a⁻¹,a⁻¹), for a in the multiplicative group of the marked binary
field, through the original K→SL₃ map. Schur–Zassenhaus gives a subgroup of K
with exactly this action, of order 2ⁿ−1. Squaring is faithful in characteristic
two, so its action on the marked root is faithful. Every nonidentity element
has zero fixed space on the natural module and its dual. The two original
sections of Q then give C_Q(Y)=1 and [Q,Y]=Q.

This torus construction precedes, and does not assume, Q=O₂(KS). After that
source identity, the proved coverage R₂=Q O₂(K₂) shows that Y normalizes R₂.
The all-degree source constructor uses this torus, the original component
embedding and the same normalQuotientAction, and discharges whole-radical
generation without imposing the unsupported whole-radical torus movement.

MSData, the marked parabolic images and the remaining core/component geometry
are earlier-source inputs; their construction and the final nonblock
contradiction remain with `qt-d-1222-rankone-uniqueness-nonblock`.
Source: Aschbacher–Smith, original 4.3.10–15, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

omit [Finite G] in
private theorem units_order_odd (d : MSData c n) (hn : 1 < n) :
    Odd (Nat.card d.field.Carrierˣ) := by
  rw [Nat.card_units,d.field.card_eq,d.degree_eq]
  have he : Even (2 ^ n) := (by decide : Even 2).pow_of_ne_zero (by omega)
  obtain ⟨k,hk⟩ := he
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  exact ⟨k-1,by omega⟩

private theorem exists_point_torus_lift (d : MSData c n) (hn : 1 < n) :
    ∃ σ : d.field.Carrierˣ →* K c,
      Function.Injective σ ∧
      ∀ a, linearThreeActor d.model (σ a) = Scalar.pointTorus d.field.Carrier a := by
  let t := Scalar.pointTorus d.field.Carrier
  let f := linearThreeActor d.model
  let e := MonoidHom.ofInjective (Scalar.pointTorus_injective d.field.Carrier)
  have hk : f.ker = pCore 2 (K c) := by
    ext x
    change d.model (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 (K c)
    rw [←d.model.map_one, d.model.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card t.range) := by
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := K c)).exists_card_eq
    rw [hk,hj,←Nat.card_congr e.toEquiv]
    exact (units_order_odd d hn).coprime_two_left.pow_left j
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel
    (d.model.surjective.comp (QuotientGroup.mk'_surjective _)) t.range hcop
  let σ := s.comp e.toMonoidHom
  have he (a : d.field.Carrierˣ) : f (σ a) = t a :=
    DFunLike.congr_fun hs (e a)
  refine ⟨σ,?_,he⟩
  intro a b hab
  apply Scalar.pointTorus_injective d.field.Carrier
  rw [←he,←he,hab]

omit [Finite G] in
private theorem section_fixed_mem_bottom {F A V : Type*} [Field F] [Group A]
    [AddCommGroup V] [Module F V] {J B E : Subgroup G}
    {actor : J →* A} {ρ : Representation F A V}
    (h : HasSectionModel J B E actor ρ) (x : J)
    (hfix : ∀ v : V, ρ (actor x) v = v → v = 0)
    {b : G} (hb : b ∈ B) (hc : x * b * (x : G)⁻¹ = b) : b ∈ E := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  let := hn
  let b' : B := ⟨b, hb⟩
  have hf := he x b' b' hc.symm
  have hz := hfix _ hf.symm
  have hz' : e (QuotientGroup.mk' _ b') = 1 := Multiplicative.toAdd.injective hz
  have heq : QuotientGroup.mk' _ b' = 1 := e.injective (hz'.trans e.map_one.symm)
  exact (QuotientGroup.eq_one_iff b').mp heq

private theorem dual_fixed_zero {F A V : Type*} [Field F] [Group A]
    [AddCommGroup V] [Module F V] [Finite V]
    (ρ : Representation F A V) (a : A)
    (hfix : ∀ v, ρ a v = v → v = 0) (f : Module.Dual F V)
    (hf : ρ.dual a f = f) : f = 0 := by
  let g : V →ₗ[F] V := ρ a - LinearMap.id
  have hg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    exact hfix v (sub_eq_zero.mp hv)
  have hs : Function.Surjective g := Finite.surjective_of_injective hg
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := hs v
  have h := LinearMap.congr_fun hf (ρ a w)
  change f (ρ a⁻¹ (ρ a w)) = f (ρ a w) at h
  rw [Representation.inv_self_apply] at h
  change f (ρ a w - w) = 0
  rw [map_sub,←h,sub_self]

omit [Finite G] in
private theorem point_torus_core_fixed (d : MSData c n) (x : K c)
    (a : d.field.Carrierˣ) (ha : a ≠ 1)
    (hx : linearThreeActor d.model x = Scalar.pointTorus d.field.Carrier a)
    {b : G} (hb : b ∈ Q c) (hc : (x : G) * b * (x : G)⁻¹ = b) : b = 1 := by
  have hn : ∀ v, Representation.specialLinearNatural 3 (linearThreeActor d.model x) v = v → v = 0 := by
    rw [hx]
    exact Scalar.pointTorus_fixed_eq_zero d.field.Carrier ha
  have hbU : b ∈ U c := section_fixed_mem_bottom d.doubleDual x
    (fun v hv => Prod.ext
      (dual_fixed_zero _ _ hn v.1 (congrArg Prod.fst hv))
      (dual_fixed_zero _ _ hn v.2 (congrArg Prod.snd hv))) hb hc
  exact section_fixed_mem_bottom d.natural x hn hbU hc

namespace RootCoordinates
variable (m : RootCoordinates d)
include m

omit [Finite G] in
private theorem point_torus_normalizes_root (x : K c) (a : d.field.Carrierˣ)
    (hx : linearThreeActor d.model x = Scalar.pointTorus d.field.Carrier a) :
    (x : G) ∈ rootNormalizer c := by
  have h (x : K c) (a : d.field.Carrierˣ)
      (hx : linearThreeActor d.model x = Scalar.pointTorus d.field.Carrier a)
      (u : G) (hu : u ∈ root c) : (x : G) * u * (x : G)⁻¹ ∈ root c := by
    let v : U c := ⟨u,d.root_le_center hu⟩
    let v' : U c := ⟨x * u * (x : G)⁻¹,
      (mem_normalizer_iff.mp (d.natural.2.1 x.property) u).mp v.property⟩
    obtain ⟨b,hb⟩ := (m.root_coordinates v).mp hu
    have hc := m.compatible x v v' rfl
    apply (m.root_coordinates v').mpr
    refine ⟨(a : d.field.Carrier)^2 * b,?_⟩
    rw [hc,hb,hx,Representation.specialLinearNatural_apply,Scalar.pointTorus_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply]
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · exact h x a hx u
  · intro hu
    have hh := h x⁻¹ a⁻¹ (by rw [map_inv,hx,map_inv]) _ hu
    simpa only [Subgroup.coe_inv,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

omit [Finite G] in
private theorem point_torus_faithful (σ : d.field.Carrierˣ →* K c)
    (hσ : ∀ a, linearThreeActor d.model (σ a) = Scalar.pointTorus d.field.Carrier a)
    {a : d.field.Carrierˣ} (ha : (σ a : G) ∈ centralizer (root c : Set G)) : a = 1 := by
  have hf := (m.centralizer_iff (σ a)).mp ha
  rw [hσ,mem_pointLocalSL_iff] at hf
  have hh : (a : d.field.Carrier)^2 = 1 := by simpa [Scalar.pointTorus_val] using hf.1
  apply Units.ext
  change (a : d.field.Carrier) = 1
  exact (sq_eq_one_iff.mp hh).elim id (fun he => by simpa only [CharTwo.neg_eq] using he)

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

private theorem point_torus_secondary_commutator (hn : 1 < n)
    (σ : d.field.Carrierˣ →* K c)
    (hσ : ∀ a, linearThreeActor d.model (σ a) = Scalar.pointTorus d.field.Carrier a) :
    ⁅secondary c, ((K c).subtype.comp σ).range⁆ ≤ (secondary c).pCoreIn 2 := by
  let Y := ((K c).subtype.comp σ).range
  have hYK : Y ≤ K c := by rintro _ ⟨a,rfl⟩; exact (σ a).property
  have hYr : Y ≤ rootNormalizer c := by
    rintro _ ⟨a,rfl⟩
    exact m.point_torus_normalizes_root (σ a) a (hσ a)
  have hnY := original_normalizes_secondary hYK hYr
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro y ⟨a,rfl⟩ k hk
  have hz : ⁅((σ a : K c) : G),k⁆ ∈ secondary c :=
    le_normalizer_iff_commutator_le_right.mp hnY
      (commutator_mem_commutator (show (σ a : G) ∈ Y from ⟨a,rfl⟩) hk)
  let z : secondary c := ⟨⁅(σ a : G),k⁆,hz⟩
  have hp : m.secondaryProjection z ∈ pCore 2 (pointLocalSL d.field.Carrier) := by
    apply (mem_map_iff_mem (pointLocalSL d.field.Carrier).subtype_injective).mp
    change (m.secondaryProjection z : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) ∈
      (pointLocalSL d.field.Carrier).pCoreIn 2
    have he : (m.secondaryProjection z : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) =
        ⁅Scalar.pointTorus d.field.Carrier a,
          (m.secondaryProjection ⟨k,hk⟩ : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)⁆ := by
      change linearThreeActor d.model ⁅σ a,(⟨k,secondary_le_original hk⟩ : K c)⁆ = _
      rw [map_commutatorElement,hσ]
      rfl
    rw [he]
    exact commutator_commutatorPreimage_le _ _ _
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
      (commutator_mem_commutator (Scalar.pointTorus_section d.field.Carrier a)
        (m.secondaryProjection ⟨k,hk⟩).property)
  have hzcore : z ∈ pCore 2 (secondary c) := by
    rw [←m.secondaryProjection.comap_pCore_of_ker_isPGroup
      (m.secondaryProjection_surjective hn) m.secondaryProjection_kernel]
    exact hp
  exact mem_map_of_mem (secondary c).subtype hzcore

/-- The odd torus in the original K has the full source order and a faithful
root action. Its natural and doubled-dual actions move all of Q. This construction
does not assume the later identity Q=O₂(KS). -/
theorem exists_moving_root_torus (hn : 1 < n) :
    ∃ Y : Subgroup G, IsCyclic Y ∧ Nat.card Y = 2 ^ n - 1 ∧
      Y ≤ K c ∧ Y ≤ rootNormalizer c ∧
      Y ⊓ centralizer (root c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (Y : Set G) = ⊥ ∧
      ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2 ∧
      ⁅Q c,Y⁆ = Q c := by
  obtain ⟨σ,hσi,hσ⟩ := exists_point_torus_lift d hn
  let f := (K c).subtype.comp σ
  let Y := f.range
  have hfi : Function.Injective f := (K c).subtype_injective.comp hσi
  let e := MonoidHom.ofInjective hfi
  have hYcard : Nat.card Y = 2 ^ n - 1 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_units,d.field.card_eq,d.degree_eq]
  have hYK : Y ≤ K c := by rintro _ ⟨a,rfl⟩; exact (σ a).property
  have hYr : Y ≤ rootNormalizer c := by
    rintro _ ⟨a,rfl⟩
    exact m.point_torus_normalizes_root (σ a) a (hσ a)
  have hfaith : Y ⊓ centralizer (root c : Set G) = ⊥ := by
    apply bot_unique
    rintro y ⟨⟨a,rfl⟩,ha⟩
    have he := m.point_torus_faithful σ hσ ha
    change f a = 1
    rw [he,map_one]
  have hf : Q c ⊓ centralizer (Y : Set G) = ⊥ := by
    have hc : 1 < Nat.card d.field.Carrierˣ := by
      rw [Nat.card_units,d.field.card_eq,d.degree_eq]
      have hh : 4 ≤ 2 ^ n := (show 4 = 2^2 from rfl).trans_le
        (Nat.pow_le_pow_right (by decide) hn)
      omega
    have : Nontrivial d.field.Carrierˣ := Finite.one_lt_card_iff_nontrivial.mp hc
    obtain ⟨a,ha⟩ := exists_ne (1 : d.field.Carrierˣ)
    apply bot_unique
    intro b hb
    apply point_torus_core_fixed d (σ a) a ha (hσ a) hb.1
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hb.2 (f a) ⟨a,rfl⟩)
  have hmove : ⁅Q c,Y⁆ = Q c := by
    have hp : IsPGroup 2 (Q c) := (T.isPGroup'.to_le
      ((core_le_sylow c).trans inf_le_left))
    have hcop : Nat.Coprime (Nat.card Y) (Nat.card (Q c)) := by
      obtain ⟨j,hj⟩ := hp.exists_card_eq
      rw [←Nat.card_congr e.toEquiv,hj]
      exact (units_order_odd d hn).coprime_two_right.pow_right j
    let : Group.IsNilpotent (Q c) := hp.isNilpotent
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime (Q c) Y
      (hYK.trans d.doubleDual.2.1) inferInstance hcop
    simpa only [hf,sup_bot_eq] using hh.symm
  exact ⟨Y,isCyclic_of_surjective e.toMonoidHom e.surjective,hYcard,hYK,hYr,hfaith,hf,
    m.point_torus_secondary_commutator hn σ hσ,hmove⟩

/-- After the source core identity, the same torus normalizes the full
secondary radical, by the proved coverage R₂=Q O₂(K₂). -/
theorem exists_source_torus (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) :
    ∃ Y : Subgroup G, IsCyclic Y ∧ Nat.card Y = 2 ^ n - 1 ∧
      Y ≤ K c ∧ Y ≤ rootNormalizer c ∧
      Y ⊓ centralizer (root c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (Y : Set G) = ⊥ ∧
      ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2 ∧
      Y ≤ normalizer (R₂ c : Set G) ∧ ⁅Q c,Y⁆ = Q c := by
  obtain ⟨Y,hcyc,hcard,hYK,hYr,hfaith,hfix,hsecY,hmove⟩ :=
    m.exists_moving_root_torus hn
  have hRY : Y ≤ normalizer (R₂ c : Set G) := by
    have he : R₂ c = Q c ⊔ (secondary c).pCoreIn 2 :=
      le_antisymm (m.radical_coverage hn D hcore)
        (sup_le (core_le_radical c) (secondary_core_le_radical D))
    rw [he]
    exact (le_inf (hYK.trans d.doubleDual.2.1)
      ((original_normalizes_secondary hYK hYr).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact ⟨Y,hcyc,hcard,hYK,hYr,hfaith,hfix,hsecY,hRY,hmove⟩

end RootCoordinates

/-- The all-degree source constructor supplies the torus instead of assuming it.
The component, core and normalizer geometry remain explicit earlier-source
inputs of the nonblock assembly owner. Whole-radical generation is derived
through this witness's very same quotient action. -/
theorem MSData.exists_secondarySourceData_of_marked_parabolic
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n, s.component = B ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨_,hmodel,hstrict,haction⟩ := d.secondary_structure_of_marked_parabolic hn D
    hL hSL B hB hBn hsec henlarged (hnorm.trans inf_le_right)
  obtain ⟨Y,hcyc,hcard,hYK,hYr,hfaith,hfix,hsecY,hRY,hmove⟩ :=
    m.exists_source_torus hn D hcore
  let s : SecondarySourceData c n := {
    component := B
    torus := Y
    isComponent := hB
    normal := hBn
    quasisimple := hBq
    secondary_le := hsec
    secondary_lt := hstrict
    secondary_model := hmodel
    torus_le := hYr
    torus_cyclic := hcyc
    torus_card := hcard
    torus_faithful := hfaith
    torus_secondary := hsecY
    torus_normalizes_radical := hRY
    core_eq := hcore
    core_moved := hmove
    radical_le := radical_le_root_normalizer D
    radical_normalizer := hnorm
    enlarged_core_le := henlarged
    core_enlarges := henlarges
    radical_action := haction }
  exact ⟨s,rfl,hYK,hfix,m.source_action_generation hn D s⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
