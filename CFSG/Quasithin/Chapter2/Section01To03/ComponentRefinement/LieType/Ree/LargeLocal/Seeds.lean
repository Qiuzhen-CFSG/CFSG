module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.RootSubgroups
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.GroupTheory.Amalgam.LocalStructure
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LocalPair
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local

/-!
# Transport of concrete Ree local seeds to a component

The component meets the supplied Sylow subgroup in a Sylow subgroup of its
own. Sylow conjugacy therefore adjusts the given model isomorphism to carry
this intersection to the standard positive fixed subgroup, whose Sylow
property follows from fixed Bruhat geometry. Stability under automorphisms preserving that
subgroup, restricted to automorphisms of two-power order, then gives exactly
N_S(L)-invariance, even when S permutes components.

For Aschbacher–Smith 2.3.9(7), printed p.526, using F.1.12(I)(5) and (II),
printed pp.263–264, the final theorem constructs the invariant pair from the
supplied exceptional endomorphism and actual component equivalence. The
component supplies simplicity. The concrete root calculations discharge
generation, invariance, intrinsic two-cores, quotient equivalences, perfectness
and the nonzero iterated commutator, which are transported through the aligned
isomorphism. The earlier conditional APIs remain available. The parent uses
these seeds to construct the local overgroups and exclude the Ree case.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

open Subgroup ReeF4.LargeLocalSeeds Theory.GroupTheory

variable {G : Type*} [Group G] {L S : Subgroup G}
  {m : ℕ} (d : ReeF4.LocalBlockInput m)

/-- The actual inverse image of the root-defined fixed local subgroup. -/
noncomputable def modelSeed (e : L ≃* d.fixedGroup) (s : Side) : Subgroup L :=
  (standardSeed d s).comap e.toMonoidHom

/-- Restriction of the model equivalence to a local factor. -/
noncomputable def modelSeedEquiv (e : L ≃* d.fixedGroup) (s : Side) :
    modelSeed d e s ≃* standardSeed d s :=
  LocalCoreTransport.subgroupEquiv e
    (map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective _)

/-- Quotient transport is by the intrinsic cores of the two actual groups. -/
noncomputable def modelSeedCoreQuotientEquiv (e : L ≃* d.fixedGroup) (s : Side) :
    (modelSeed d e s ⧸ pCore 2 (modelSeed d e s)) ≃*
      (standardSeed d s ⧸ pCore 2 (standardSeed d s)) :=
  LocalCoreTransport.quotientEquiv 2 (modelSeedEquiv d e s)

/-- The linear quotient is simple after the concrete quotient map is supplied.
The target is PSL₂ over the specified Ree field, whose simplicity is proved
independently of any Ree simplicity assumption. -/
theorem modelSeed_linear_quotient_simple (hm : 1 ≤ m) (e : L ≃* d.fixedGroup)
    (q : (standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
      LinearQuotient m) :
    IsSimpleGroup (modelSeed d e .linear ⧸ pCore 2 (modelSeed d e .linear)) := by
  let := linearQuotient_simple m hm
  exact ((modelSeedCoreQuotientEquiv d e .linear).trans q).isSimpleGroup

theorem component_sylow_le_modelSeed (e : L ≃* d.fixedGroup)
    (he : (S.subgroupOf L).map e.toMonoidHom = standardUnipotent d) (s : Side) :
    S.subgroupOf L ≤ modelSeed d e s := by
  intro x hx
  apply standardUnipotent_le_seed d s
  rw [← he]
  exact mem_map_of_mem _ hx

/-- Align the original component intersection, without assuming L normal in S. -/
theorem exists_aligned_model_equiv {H M : Subgroup G} {T : Sylow 2 H} {z : G}
    (h : LocalSetup H L M T z) (e : L ≃* d.fixedGroup)
    (U : Sylow 2 d.fixedGroup) (hU : (U : Subgroup d.fixedGroup) = standardUnipotent d) :
    ∃ f : L ≃* d.fixedGroup,
      (((T : Subgroup H).map H.subtype).subgroupOf L).map f.toMonoidHom =
        standardUnipotent d := by
  let := h.finite
  obtain ⟨R, hR⟩ := h.component_sylow
  let R' : Sylow 2 d.fixedGroup := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq d.fixedGroup R' U
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [← hR]
  change (R : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map]
  change (R' : Subgroup d.fixedGroup).map (MulAut.conj g).toMonoidHom = _
  rw [← hU, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

private theorem modelSeed_invariant (hS2 : IsPGroup 2 S) (e : L ≃* d.fixedGroup)
    (he : (S.subgroupOf L).map e.toMonoidHom = standardUnipotent d) (s : Side)
    (hstable : ∀ a : MulAut d.fixedGroup,
      (∃ n : ℕ, a ^ (2 ^ n) = 1) →
      (∀ x, x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d) →
      ∀ x, x ∈ standardSeed d s ↔ a x ∈ standardSeed d s) :
    S ⊓ normalizer (L : Set G) ≤ normalizer ((modelSeed d e s).map L.subtype : Set G) := by
  intro g hg
  let aL : MulAut L := L.normalizerMonoidHom ⟨g, hg.2⟩
  let a := (MulAut.congr e) aL
  obtain ⟨n, hn⟩ := hS2.exists_pow_pow_eq_one (⟨g, hg.1⟩ : S)
  have hnG : g ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hnN : (⟨g, hg.2⟩ : normalizer (L : Set G)) ^ (2 ^ n) = 1 :=
    Subtype.ext hnG
  have hnL : aL ^ (2 ^ n) = 1 := by
    change (L.normalizerMonoidHom ⟨g, hg.2⟩) ^ (2 ^ n) = 1
    rw [← map_pow, hnN, map_one]
  have hna : a ^ (2 ^ n) = 1 := by
    change ((MulAut.congr e) aL) ^ (2 ^ n) = 1
    rw [← map_pow, hnL, map_one]
  have hS (x : L) : x ∈ S.subgroupOf L ↔ aL x ∈ S.subgroupOf L := by
    change (x : G) ∈ S ↔ g * (x : G) * g⁻¹ ∈ S
    exact mem_normalizer_iff.mp (S.le_normalizer hg.1) x
  have hU (x : d.fixedGroup) :
      x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d := by
    rw [← he, mem_map_equiv, mem_map_equiv]
    change e.symm x ∈ S.subgroupOf L ↔
      e.symm (e (aL (e.symm x))) ∈ S.subgroupOf L
    rw [e.symm_apply_apply]
    exact hS _
  have hK (x : L) : x ∈ modelSeed d e s ↔ aL x ∈ modelSeed d e s := by
    have hk := hstable a ⟨n, hna⟩ hU (e x)
    change e x ∈ standardSeed d s ↔ e (aL x) ∈ standardSeed d s
    simpa only [a, MulAut.congr_apply, MulEquiv.trans_apply,
      e.symm_apply_apply] using hk
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨aL y, (hK y).mp hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hxL : x ∈ L := (mem_normalizer_iff.mp hg.2 x).mpr (hxy ▸ y.property)
    have hya : aL ⟨x, hxL⟩ = y := Subtype.ext hxy.symm
    refine ⟨⟨x, hxL⟩, (hK ⟨x, hxL⟩).mpr ?_, rfl⟩
    rwa [hya]

/-- Assembly of a genuine invariant pair from checked model geometry.
The model generation and stability hypotheses must still be discharged. -/
noncomputable def pairOfModelGeometry (hS2 : IsPGroup 2 S) (e : L ≃* d.fixedGroup)
    (he : (S.subgroupOf L).map e.toMonoidHom = standardUnipotent d)
    (hgenerate : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤)
    (hstable : ∀ (s : Side) (a : MulAut d.fixedGroup),
      (∃ n : ℕ, a ^ (2 ^ n) = 1) →
      (∀ x, x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d) →
      ∀ x, x ∈ standardSeed d s ↔ a x ∈ standardSeed d s) : InvariantPair L S where
  left := modelSeed d e .suzuki
  right := modelSeed d e .linear
  generate := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, modelSeed, modelSeed,
      map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, hgenerate,
      map_top_of_surjective _ e.surjective]
  invariant_left := by
    exact modelSeed_invariant d hS2 e he .suzuki (hstable .suzuki)
  invariant_right := by
    exact modelSeed_invariant d hS2 e he .linear (hstable .linear)

private theorem core_ne_bot_transport {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) (h : pCore 2 B ≠ ⊥) : pCore 2 A ≠ ⊥ := by
  intro hbot
  have he := pCore_map_iso 2 f
  rw [hbot, Subgroup.map_bot] at he
  exact h he.symm

private theorem core_centralizer_transport {A B : Type*} [Group A] [Group B]
    (f : A ≃* B)
    (hc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B) :
    centralizer (pCore 2 A : Set A) ≤ pCore 2 A := by
  intro x hx
  have hx' : f x ∈ pCore 2 B := by
    apply hc
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [← pCore_map_iso 2 f] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact (f.map_mul a x).symm.trans
      ((congrArg f (mem_centralizer_iff.mp hx a ha)).trans (f.map_mul x a))
  rw [← pCore_map_iso 2 f, mem_map_equiv] at hx'
  simpa only [f.symm_apply_apply] using hx'

private theorem core_commutator_transport {A B : Type*} [Group A] [Group B]
    (f : A ≃* B)
    (h : ⁅⁅pCore 2 B, (⊤ : Subgroup B)⁆, pCore 2 B⁆ ≠ ⊥) :
    ⁅⁅pCore 2 A, (⊤ : Subgroup A)⁆, pCore 2 A⁆ ≠ ⊥ := by
  intro hbot
  have he : (⁅⁅pCore 2 A, (⊤ : Subgroup A)⁆, pCore 2 A⁆).map f.toMonoidHom =
      ⁅⁅pCore 2 B, (⊤ : Subgroup B)⁆, pCore 2 B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, pCore_map_iso,
      map_top_of_surjective _ f.surjective]
  rw [hbot, Subgroup.map_bot] at he
  exact h he.symm



/-- Nontriviality of the intrinsic two-core survives restriction of the model isomorphism. -/
theorem modelSeed_core_ne_bot (e : L ≃* d.fixedGroup) (s : Side)
    (hcore : pCore 2 (standardSeed d s) ≠ ⊥) :
    pCore 2 (modelSeed d e s) ≠ ⊥ :=
  core_ne_bot_transport (modelSeedEquiv d e s) hcore

/-- The centralizer condition is transported inside each local factor. -/
theorem modelSeed_selfCentralizing_core (e : L ≃* d.fixedGroup) (s : Side)
    (hc : centralizer (pCore 2 (standardSeed d s) : Set (standardSeed d s)) ≤
      pCore 2 (standardSeed d s)) :
    centralizer (pCore 2 (modelSeed d e s) : Set (modelSeed d e s)) ≤
      pCore 2 (modelSeed d e s) :=
  core_centralizer_transport (modelSeedEquiv d e s) hc

/-- Perfectness passes through the actual local-factor isomorphism. -/
theorem modelSeed_perfect (e : L ≃* d.fixedGroup) (s : Side)
    (hp : Group.IsPerfect (standardSeed d s)) : Group.IsPerfect (modelSeed d e s) := by
  let := hp
  exact Group.IsPerfect.ofSurjective (f := (modelSeedEquiv d e s).symm.toMonoidHom)
    (modelSeedEquiv d e s).symm.surjective

/-- The iterated commutator is computed inside the factor on both sides. -/
theorem modelSeed_core_commutator_ne_bot (e : L ≃* d.fixedGroup) (s : Side)
    (hc : ⁅⁅pCore 2 (standardSeed d s), (⊤ : Subgroup (standardSeed d s))⁆,
      pCore 2 (standardSeed d s)⁆ ≠ ⊥) :
    ⁅⁅pCore 2 (modelSeed d e s), (⊤ : Subgroup (modelSeed d e s))⁆,
      pCore 2 (modelSeed d e s)⁆ ≠ ⊥ :=
  core_commutator_transport (modelSeedEquiv d e s) hc

/-- Conditional assembly: the hypotheses concern the specified root subgroups,
whereas the conclusion concerns an invariant pair inside the supplied component.
The final theorem below discharges all model geometry and radical hypotheses. -/
theorem exists_pair_of_model_calculations {H M : Subgroup G} {T : Sylow 2 H} {z : G}
    (h : LocalSetup H L M T z) (hm : 1 ≤ m) (e : L ≃* d.fixedGroup)
    (U : Sylow 2 d.fixedGroup) (hU : (U : Subgroup d.fixedGroup) = standardUnipotent d)
    (hgenerate : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤)
    (hstable : ∀ (s : Side) (a : MulAut d.fixedGroup),
      (∃ n : ℕ, a ^ (2 ^ n) = 1) →
      (∀ x, x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d) →
      ∀ x, x ∈ standardSeed d s ↔ a x ∈ standardSeed d s)
    (hne : ∀ s : Side, pCore 2 (standardSeed d s) ≠ ⊥)
    (hcentral : ∀ s : Side,
      centralizer (pCore 2 (standardSeed d s) : Set (standardSeed d s)) ≤
        pCore 2 (standardSeed d s))
    (qSuzuki : (standardSeed d .suzuki ⧸ pCore 2 (standardSeed d .suzuki)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hperfect : Group.IsPerfect (standardSeed d .linear))
    (qLinear : (standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
      LinearQuotient m)
    (hcomm : ⁅⁅pCore 2 (standardSeed d .linear),
        (⊤ : Subgroup (standardSeed d .linear))⁆,
      pCore 2 (standardSeed d .linear)⁆ ≠ ⊥) :
    ∃ p : InvariantPair L ((T : Subgroup H).map H.subtype),
      ((T : Subgroup H).map H.subtype).subgroupOf L ≤ p.left ∧
      ((T : Subgroup H).map H.subtype).subgroupOf L ≤ p.right ∧
      pCore 2 p.left ≠ ⊥ ∧
      centralizer (pCore 2 p.left : Set p.left) ≤ pCore 2 p.left ∧
      pCore 2 p.right ≠ ⊥ ∧
      centralizer (pCore 2 p.right : Set p.right) ≤ pCore 2 p.right ∧
      Nonempty ((p.left ⧸ pCore 2 p.left) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      Group.IsPerfect p.right ∧
      Nonempty ((p.right ⧸ pCore 2 p.right) ≃* LinearQuotient m) ∧
      IsSimpleGroup (p.right ⧸ pCore 2 p.right) ∧
      ⁅⁅pCore 2 p.right, (⊤ : Subgroup p.right)⁆, pCore 2 p.right⁆ ≠ ⊥ := by
  obtain ⟨f, hf⟩ := exists_aligned_model_equiv d h e U hU
  have hT : IsPGroup 2 ((T : Subgroup H).map H.subtype) :=
    T.isPGroup'.map H.subtype
  let p := pairOfModelGeometry d hT f hf hgenerate hstable
  refine ⟨p, component_sylow_le_modelSeed d f hf .suzuki,
    component_sylow_le_modelSeed d f hf .linear,
    modelSeed_core_ne_bot d f .suzuki (hne .suzuki),
    modelSeed_selfCentralizing_core d f .suzuki (hcentral .suzuki),
    modelSeed_core_ne_bot d f .linear (hne .linear),
    modelSeed_selfCentralizing_core d f .linear (hcentral .linear),
    ⟨(modelSeedCoreQuotientEquiv d f .suzuki).trans qSuzuki⟩,
    modelSeed_perfect d f .linear hperfect,
    ⟨(modelSeedCoreQuotientEquiv d f .linear).trans qLinear⟩,
    modelSeed_linear_quotient_simple d hm f qLinear,
    modelSeed_core_commutator_ne_bot d f .linear hcomm⟩

/-- The concrete large Ree local seeds inside the source component. The supplied
component simplicity and exceptional endomorphism are the only model inputs:
the fixed geometry and radical calculations are proved for the actual root
subgroups. Invariance is under `N_T(L)`, allowing `T` to permute components.
The inner action of `z` is not needed for this seed construction. -/
theorem exists_pair_of_localBlockInput {H M : Subgroup G} {T : Sylow 2 H} {z : G}
    (h : LocalSetup H L M T z) [IsSimpleGroup L] (hm : 1 ≤ m)
    (e : L ≃* d.fixedGroup) :
    ∃ p : InvariantPair L ((T : Subgroup H).map H.subtype),
      ((T : Subgroup H).map H.subtype).subgroupOf L ≤ p.left ∧
      ((T : Subgroup H).map H.subtype).subgroupOf L ≤ p.right ∧
      pCore 2 p.left ≠ ⊥ ∧
      centralizer (pCore 2 p.left : Set p.left) ≤ pCore 2 p.left ∧
      pCore 2 p.right ≠ ⊥ ∧
      centralizer (pCore 2 p.right : Set p.right) ≤ pCore 2 p.right ∧
      Nonempty ((p.left ⧸ pCore 2 p.left) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      Group.IsPerfect p.right ∧
      Nonempty ((p.right ⧸ pCore 2 p.right) ≃* LinearQuotient m) ∧
      IsSimpleGroup (p.right ⧸ pCore 2 p.right) ∧
      ⁅⁅pCore 2 p.right, (⊤ : Subgroup p.right)⁆, pCore 2 p.right⁆ ≠ ⊥ := by
  let : IsSimpleGroup d.fixedGroup := e.symm.isSimpleGroup
  obtain ⟨U, hU, hgenerate, hstable⟩ := exists_standardSylow_with_seed_geometry hm d
  exact exists_pair_of_model_calculations d h hm e U hU hgenerate hstable
    (fun s => by
      cases s
      · exact suzuki_core_ne_bot hm d
      · exact linearCore_ne_bot hm d)
    (fun s => by
      cases s
      · exact suzuki_core_centralizer_le hm d
      · exact linearCore_centralizer_le hm d)
    (suzuki_coreQuotientEquiv hm d) (linearSeed_perfect hm d)
    (linearCoreQuotientEquiv hm d) (linearCore_iterated_commutator_ne_bot hm d)


end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
