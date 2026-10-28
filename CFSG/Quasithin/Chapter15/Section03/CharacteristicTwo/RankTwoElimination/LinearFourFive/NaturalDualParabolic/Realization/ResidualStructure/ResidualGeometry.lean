module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.CoreReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.CenterObstruction

/-!
# Natural-dual geometry inside the intrinsic residual core

Let P be the actual point parabolic and D = O²(P). Perfectness of the
marked point stabilizer makes the restriction of the quotient action to D
surjective. Hence every coordinate displacement already lies in
K = [O₂(D),D], using the relative C-component comparison with [O₂(P),D].
The full seven-dimensional moved space embeds in K. The natural fixed
line and dual annihilator give a subgroup of order sixteen in Z(K): it
lies in K and centralizes the larger [O₂(P),P]. Thus |K| ≥ 128 and
|Z(K)| ≥ 16 without asserting equality of these two commutator cores.

These intrinsic bounds allow the later C.1.34 sieve to use its literal
core. They do not prove the separate equality requested by the old MSData
interface. No C.1.34 alternative or core-shape classification is used here.
Relative theta-normality also discharges U_L ≤ O₂(L) from the earlier
Sylow and elementary-span hypotheses, keeping both choices of 15.3.10.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130; C.1.31–34, printed pp.135–137.
-/

public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

private theorem finite_perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Relative theta-normality and the actual V ≤ S put U_L in the old core. -/
theorem spanCommutator_le_componentCore_of_theta
    [IsElementaryAbelian 2 (d.componentSpan L)] {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I) :
    spanCommutator d L ≤ L.pCoreIn 2 := by
  have hVS : d.V ≤ d.S := d.action.le_planeStabilizer d.T d.sylow_le
    (localModule_le d.T d.sylow_le) 1
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hLI : L ≤ I := hθ ▸ theta_le I
  have hWI : d.componentSpan L ≤ I :=
    conjugateSpanBy_le (hVS.trans hSI) (hLI.trans I.le_normalizer)
  exact spanCommutator_le_componentCore (hWI.trans (normalizes_of_eq_theta hθ))

/-- Every element of the marked point stabilizer lifts from the actual residual. -/
theorem pointActor_residual_image (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    (pResidual 2 (point h x)).map (pointActor h x) = ⊤ := by
  let _ : Finite (pointStabilizer x) :=
    Finite.of_surjective (pointActor h x) (pointActor_surjective h x)
  let _ := point_isPerfect (by decide : 4 ≤ 4) hx
  rw [map_pResidual_of_surjective 2 _ (pointActor_surjective h x)]
  exact (pResidual_eq_top_iff 2 _).mpr finite_perfect_twoPerfect

/-- Displacements already lie in the intrinsic residual core. -/
theorem displacement_mem_residualCore (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (g : pointStabilizer x) (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    embed h (Multiplicative.ofAdd (BinaryLinear.NaturalDualFlag.action g.val v - v)) ∈
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ := by
  have hg : g ∈ (pResidual 2 (point h x)).map (pointActor h x) := by
    rw [pointActor_residual_image h hx]
    exact mem_top _
  obtain ⟨p, hp, he⟩ := hg
  have hpD : (p : G) ∈ Stellmacher.twoResidualAmbient (point h x) := by
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact mem_map.mpr ⟨p, hp, rfl⟩
  rw [residual_core_commutator_eq h hx, commutator_comm]
  have hc := commutator_mem_commutator hpD (hU (embed_mem h v))
  have hactor : linearAction (by decide) h.model ⟨p, point_le h x p.property⟩ = g.val :=
    congrArg Subtype.val he
  change ⁅(p : G), embed h (Multiplicative.ofAdd v)⁆ ∈ _ at hc
  rw [commutatorElement_def,
    embed_conj h (⟨p, point_le h x p.property⟩ : L) v, hactor] at hc
  simpa only [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv] using hc

/-- The complete seven-dimensional moved subspace lies in the intrinsic core. -/
theorem movedSpace_mem_residualCore (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) (hv : v.2 ∈ annihilator x) :
    embed h (Multiplicative.ofAdd v) ∈
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ := by
  let K := ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
    Stellmacher.twoResidualAmbient (point h x)⁆
  let W : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)) :=
    AddSubgroup.toZModSubmodule 2 ((K.comap (embed h)).toAddSubgroup')
  have hw : Representation.Coinvariants.ker (pointRepresentation x) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩, rfl⟩
    change embed h (Multiplicative.ofAdd
      (BinaryNaturalDual.naturalDualRepresentation g.val w - w)) ∈ K
    have he : BinaryNaturalDual.naturalDualRepresentation g.val w =
        BinaryLinear.NaturalDualFlag.action g.val w := by
      rw [BinaryNaturalDual.naturalDualRepresentation_apply]
      apply Prod.ext
      · exact (BinaryLinear.NaturalDualFlag.action_fst g.val w).symm
      · apply LinearMap.ext
        intro y
        exact (BinaryLinear.NaturalDualFlag.action_snd g.val w y).symm
    rw [he]
    exact displacement_mem_residualCore h hx hU g w
  rw [point_commutator (by simp [Space]) hx] at hw
  exact hw ⟨Submodule.mem_top, hv⟩

/-- Intrinsic residual commutators are contained in the original parabolic core. -/
theorem residualCore_le_coreCommutator (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ ≤ coreCommutator (point h x) := by
  rw [residual_core_commutator_eq h hx]
  exact commutator_mono le_rfl (map_subtype_le _)

/-- The same concrete central subgroup of order sixteen lies in the smaller core. -/
theorem centralSubgroup_le_residualCore_center (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    centralSubgroup h x ≤
      (center (⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ : Subgroup G)).map
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆.subtype := by
  let K := ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
    Stellmacher.twoResidualAmbient (point h x)⁆
  rintro _ ⟨v, hv, rfl⟩
  have hm : embed h v ∈ K := movedSpace_mem_residualCore h hx hU v.toAdd hv.2
  have hz := centralSubgroup_le_center h hx hU (mem_map.mpr ⟨v, hv, rfl⟩)
  obtain ⟨z, hz, he⟩ := hz
  change (z : G) = embed h v at he
  refine mem_map.mpr ⟨⟨embed h v, hm⟩, ?_, rfl⟩
  rw [mem_center_iff]
  intro q
  have hq : (q : G) ∈ coreCommutator (point h x) :=
    residualCore_le_coreCommutator h hx q.property
  have hh := (mem_center_iff.mp hz) (⟨q, hq⟩ : coreCommutator (point h x))
  apply Subtype.ext
  have hh' := congrArg (fun a : coreCommutator (point h x) => (a : G)) hh
  simpa only [coe_mul, he] using hh'

/-- The intrinsic residual core has centre of order at least sixteen. -/
theorem residualCore_center_card_ge_sixteen (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    16 ≤ Nat.card (center (⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ : Subgroup G)) := by
  let K := ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
    Stellmacher.twoResidualAmbient (point h x)⁆
  have hc := card_le_of_le (centralSubgroup_le_residualCore_center h hx hU)
  rw [centralSubgroup_card h hx, ← Nat.card_congr
    ((center K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv] at hc
  exact hc

/-- The intrinsic residual core has order at least 128. -/
theorem residualCore_card_ge (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    128 ≤ Nat.card (⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ : Subgroup G) := by
  let K := ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
    Stellmacher.twoResidualAmbient (point h x)⁆
  let f : (Space 4 × annihilator x) → K := fun v =>
    ⟨embed h (Multiplicative.ofAdd (v.1, v.2.val)),
      movedSpace_mem_residualCore h hx hU _ v.2.property⟩
  have hf : Function.Injective f := by
    intro v w he
    have hh := embed_injective h (congrArg (fun z : K => (z : G)) he)
    have hh' := congrArg Multiplicative.toAdd hh
    apply Prod.ext
    · exact congrArg (fun z : Space 4 × Module.Dual (ZMod 2) (Space 4) => z.1) hh'
    · apply Subtype.ext
      exact congrArg (fun z : Space 4 × Module.Dual (ZMod 2) (Space 4) => z.2) hh'
  have hc := Nat.card_le_card_of_injective f hf
  have ha : Nat.card (annihilator x) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, annihilator_finrank hx]
    decide
  simpa only [Nat.card_prod, ha, show Nat.card (Space 4) = 16 by
    simp [Space, Nat.card_eq_fintype_card]] using hc
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
