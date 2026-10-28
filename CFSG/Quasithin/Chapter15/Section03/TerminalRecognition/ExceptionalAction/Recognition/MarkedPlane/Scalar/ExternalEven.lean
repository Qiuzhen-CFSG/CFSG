module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Scalar.Core
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.Representation.HexacodeAction.Cover

/-!
# The external residual commutes with the even hexacode group

The source subgroup `Y_E` normalizes `V`, and `G₀` normalizes `Y_E`.
Consequently `Y_E` preserves each `G₀`-conjugate of `V` and their normal
closure. Transporting this actual ambient conjugation through the given
coordinates defines its binary linear action, even for actors outside `G₀`.

The two-core fixes the normal closure by `Scalar.Core`. Thus the action
image is a quotient of `Y_E/O₂(Y_E)`, which has order three, and is cyclic.
The full hexacode group normalizes that image. Its even subgroup is perfect,
so its conjugation action on this cyclic image is trivial, proving the
required commutation identity.

This is a conditional helper with the source configuration and hexacode
coordinates as inputs. Identifying the external action with scalars remains
the responsibility of the scalar-recognition assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
setup on printed pp.1121–1122, the quotient in 15.3.67(3) on pp.1152–1154,
relative normalization in 15.3.68(1) on p.1154, and the normal-closure module
and core bound in the final proof of 15.3.1 on p.1155.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}

private theorem closure_conj_mem (g : G₀) {x : G}
    (hx : x ∈ ambientClosure G₀ V) :
    (g : G) * x * (g : G)⁻¹ ∈ ambientClosure G₀ V := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact mem_map_of_mem G₀.subtype
    ((inferInstance : (moduleClosure (V.subgroupOf G₀)).Normal).conj_mem v hv g)

private theorem residual_conj_mem (cfg : SourceConfiguration G₀ M V d)
    {y : G} (hy : y ∈ cfg.YE) {x : G} (hx : x ∈ ambientClosure G₀ V) :
    y * x * y⁻¹ ∈ ambientClosure G₀ V := by
  have hYV : cfg.YE ≤ normalizer (V : Set G) :=
    (cfg.first_residual_le.trans cfg.residual_le).trans d.normalizes
  have h : moduleClosure (V.subgroupOf G₀) ≤
      (ambientClosure G₀ V).comap ((MulAut.conj y).toMonoidHom.comp G₀.subtype) := by
    change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).mpr
    intro a ha
    obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp ha
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hy' : (g : G)⁻¹ * y * (g : G) ∈ cfg.YE :=
      (mem_normalizer_iff''.mp (cfg.first_residual_normalized g.property) y).mp hy
    have hv' : ((g : G)⁻¹ * y * (g : G)) * (v : G) *
        ((g : G)⁻¹ * y * (g : G))⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hYV hy') v).mp hv
    have hvW : ((g : G)⁻¹ * y * (g : G)) * (v : G) *
        ((g : G)⁻¹ * y * (g : G))⁻¹ ∈ ambientClosure G₀ V :=
      mem_map_of_mem G₀.subtype (le_normalClosure (show
        (⟨_, cfg.vector_le hv'⟩ : G₀) ∈ V.subgroupOf G₀ from hv'))
    simpa [mul_assoc] using closure_conj_mem g hvW
  obtain ⟨v, hv, rfl⟩ := hx
  exact h hv

/-- The external first residual preserves the actual normal-closure module. -/
theorem first_residual_normalizes_closure (cfg : SourceConfiguration G₀ M V d) :
    cfg.YE ≤ normalizer (ambientClosure G₀ V : Set G) := by
  intro y hy
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact residual_conj_mem cfg hy
  · intro hx
    simpa [mul_assoc] using residual_conj_mem cfg (cfg.YE.inv_mem hy) hx

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)

private noncomputable def closureAut
    (y : normalizer (ambientClosure G₀ V : Set G)) :
    MulAut (moduleClosure (V.subgroupOf G₀)) :=
  let e := Subgroup.equivMapOfInjective (moduleClosure (V.subgroupOf G₀))
    G₀.subtype G₀.subtype_injective
  (e.trans ((ambientClosure G₀ V).normalizerMonoidHom y)).trans e.symm

private noncomputable def coordinateAut
    (y : normalizer (ambientClosure G₀ V : Set G)) :
    Atlas.Codes.hexacode ≃ₗ[ZMod 2] Atlas.Codes.hexacode :=
  c.vectors.symm.trans ((LinearEquiv.ofBijective
    ((closureAut y).toMonoidHom.toAdditive.toZModLinearMap 2)
    (closureAut y).toAdditive.bijective).trans c.vectors)

private theorem coordinateAut_ambient
    (y : normalizer (ambientClosure G₀ V : Set G)) (w : Atlas.Codes.hexacode) :
    ambientVector c (coordinateAut c y w) =
      (y : G) * ambientVector c w * (y : G)⁻¹ := by
  simp only [coordinateAut, LinearEquiv.trans_apply,
    ambientVector, LinearEquiv.symm_apply_apply]
  let e := Subgroup.equivMapOfInjective (moduleClosure (V.subgroupOf G₀))
    G₀.subtype G₀.subtype_injective
  exact congrArg (fun v : ambientClosure G₀ V => (v : G))
    (e.apply_symm_apply ((ambientClosure G₀ V).normalizerMonoidHom y
      (e (c.vectors.symm w).toMul)))

/-- Conjugation by the external residual, in the specified binary coordinates. -/
noncomputable def externalAction (cfg : SourceConfiguration G₀ M V d) :
    cfg.YE →* (Atlas.Codes.hexacode ≃ₗ[ZMod 2] Atlas.Codes.hexacode) where
  toFun y := coordinateAut c ⟨y, first_residual_normalizes_closure cfg y.property⟩
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply ambientVector_injective c
    rw [coordinateAut_ambient]
    simp
  map_mul' y z := by
    apply LinearEquiv.ext
    intro w
    apply ambientVector_injective c
    change ambientVector c (coordinateAut c _ w) =
      ambientVector c (coordinateAut c _ (coordinateAut c _ w))
    simp only [coordinateAut_ambient, coe_mul, mul_inv_rev]
    group

/-- This is the literal ambient conjugation action, including external actors. -/
theorem externalAction_ambient (cfg : SourceConfiguration G₀ M V d)
    (y : cfg.YE) (w : Atlas.Codes.hexacode) :
    ambientVector c (externalAction c cfg y w) =
      (y : G) * ambientVector c w * (y : G)⁻¹ :=
  coordinateAut_ambient c _ w

/-- The residual's two-core is in the kernel of its binary action. -/
theorem externalAction_core_le_ker (cfg : SourceConfiguration G₀ M V d) :
    pCore 2 cfg.YE ≤ (externalAction c cfg).ker := by
  intro y hy
  apply LinearEquiv.ext
  intro w
  apply ambientVector_injective c
  rw [externalAction_ambient]
  exact first_residual_core_fixes_coordinates c cfg (mem_map_of_mem cfg.YE.subtype hy) w

/-- The image is a quotient of the source cyclic group of order three. -/
theorem externalAction_range_isCyclic (cfg : SourceConfiguration G₀ M V d) :
    IsCyclic (externalAction c cfg).range := by
  let _ : IsCyclic (cfg.YE ⧸ pCore 2 cfg.YE) :=
    isCyclic_of_prime_card cfg.first_residual_quotient_card
  let f := (externalAction c cfg).rangeRestrict
  have hk : pCore 2 cfg.YE ≤ f.ker := by
    simpa only [f, MonoidHom.ker_rangeRestrict] using externalAction_core_le_ker c cfg
  exact isCyclic_of_surjective (QuotientGroup.lift _ f hk)
    (QuotientGroup.lift_surjective_of_surjective _ f
      (externalAction c cfg).rangeRestrict_surjective hk)

/-- Conjugation of the external action agrees with conjugation of its actors. -/
theorem externalAction_conjugate (cfg : SourceConfiguration G₀ M V d)
    (g : G₀) (y : cfg.YE) :
    Atlas.Codes.hexAction (actorHom c g) * externalAction c cfg y *
        (Atlas.Codes.hexAction (actorHom c g))⁻¹ =
      externalAction c cfg (cfg.YE.normalizerMonoidHom
        ⟨g, cfg.first_residual_normalized g.property⟩ y) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply LinearEquiv.ext
  intro w
  apply ambientVector_injective c
  change ambientVector c (Representation.Hexacode.action (actorHom c g)
    (externalAction c cfg y w)) =
    ambientVector c (externalAction c cfg _
      (Representation.Hexacode.action (actorHom c g) w))
  rw [ambientVector_action, externalAction_ambient, externalAction_ambient,
    ambientVector_action]
  change (g : G) * ((y : G) * ambientVector c w * (y : G)⁻¹) * (g : G)⁻¹ =
    ((g : G) * (y : G) * (g : G)⁻¹) *
      ((g : G) * ambientVector c w * (g : G)⁻¹) *
      ((g : G) * (y : G) * (g : G)⁻¹)⁻¹
  group

private theorem actorHom_surjective : Function.Surjective (actorHom c) :=
  c.actor.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The full hexacode group normalizes the image of the external action. -/
theorem externalAction_range_normalized (cfg : SourceConfiguration G₀ M V d)
    (a : Atlas.Codes.HexAutomorphisms) :
    Atlas.Codes.hexAction a ∈ normalizer ((externalAction c cfg).range : Set _) := by
  have hp : ∀ a : Atlas.Codes.HexAutomorphisms,
      ∀ x ∈ (externalAction c cfg).range,
      Atlas.Codes.hexAction a * x * (Atlas.Codes.hexAction a)⁻¹ ∈
        (externalAction c cfg).range := by
    intro a x hx
    obtain ⟨g, rfl⟩ := actorHom_surjective c a
    obtain ⟨y, rfl⟩ := hx
    rw [externalAction_conjugate]
    exact ⟨_, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hp a x
  · intro hx
    simpa [mul_assoc] using hp a⁻¹ _ hx

/-- Perfectness of the even cover forces it to centralize the cyclic image. -/
theorem externalAction_commutes_even (cfg : SourceConfiguration G₀ M V d)
    (y : cfg.YE) (g : Atlas.Codes.HexEvenAutomorphisms) (w : Atlas.Codes.hexacode) :
    externalAction c cfg y (Representation.Hexacode.action g.val w) =
      Representation.Hexacode.action g.val (externalAction c cfg y w) := by
  let N := (externalAction c cfg).range
  let _ : IsCyclic N := externalAction_range_isCyclic c cfg
  let _ := (IsCyclic.mulAutMulEquiv N).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv N).injective
  let _ : Group.IsPerfect Atlas.Codes.HexEvenAutomorphisms :=
    Representation.Hexacode.even_isPerfect
  let f : Atlas.Codes.HexEvenAutomorphisms →* normalizer
      (N : Set (Atlas.Codes.hexacode ≃ₗ[ZMod 2] Atlas.Codes.hexacode)) :=
    { toFun := fun a => ⟨Atlas.Codes.hexAction a.val,
        externalAction_range_normalized c cfg a.val⟩
      map_one' := Subtype.ext (map_one Atlas.Codes.hexAction)
      map_mul' := fun a b => Subtype.ext (map_mul Atlas.Codes.hexAction a.val b.val) }
  have hg : (N.normalizerMonoidHom.comp f) g = 1 :=
    Abelianization.commutator_subset_ker (N.normalizerMonoidHom.comp f)
      Group.IsPerfect.mem_commutator
  have he := congrArg (fun a : MulAut N => (a ⟨externalAction c cfg y,
    ⟨y, rfl⟩⟩ : (Atlas.Codes.hexacode ≃ₗ[ZMod 2]
      Atlas.Codes.hexacode))) hg
  change Atlas.Codes.hexAction g.val * externalAction c cfg y *
      (Atlas.Codes.hexAction g.val)⁻¹ = externalAction c cfg y at he
  have he' := mul_inv_eq_iff_eq_mul.mp he
  exact (congrArg (fun a : Atlas.Codes.hexacode ≃ₗ[ZMod 2] Atlas.Codes.hexacode =>
    a w) he').symm

/-- The external residual has a binary linear action compatible with ambient
conjugation and commuting with every even hexacode automorphism. -/
theorem exists_externalAction_commuting_even (cfg : SourceConfiguration G₀ M V d) :
    ∃ ρ : cfg.YE →* (Atlas.Codes.hexacode ≃ₗ[ZMod 2] Atlas.Codes.hexacode),
      (∀ y w, ambientVector c (ρ y w) =
        (y : G) * ambientVector c w * (y : G)⁻¹) ∧
      (∀ y (g : Atlas.Codes.HexEvenAutomorphisms) w,
        ρ y (Representation.Hexacode.action g.val w) =
          Representation.Hexacode.action g.val (ρ y w)) :=
  ⟨externalAction c cfg, externalAction_ambient c cfg, externalAction_commutes_even c cfg⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
