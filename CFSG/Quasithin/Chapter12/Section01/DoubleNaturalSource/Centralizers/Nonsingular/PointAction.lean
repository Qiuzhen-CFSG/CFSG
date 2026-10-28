module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Residual
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The full action of a nonsingular point-residual join

The source stabilizer is Aut(L_(n-1)(2)), with trivial two-core. Its actual
embedded two-residual is the marked inner stabilizer. The original L_w maps
onto that residual, and the image of the relative Sylow C_T(w) supplements it.
Consequently L_w C_T(w) maps onto the whole source stabilizer.

These are the literal action inputs to the common-core calculation in
12.1.1. No Sylow assertion about C_G(w) is used.
Source: Aschbacher--Smith H.9.1(4) and 12.1.1, printed pp.390,788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryNaturalDual.ModelOrbits.AutomorphismModel
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

/-- The full source point stabilizer has exactly the published inner two-residual. -/
theorem nonsingular_stabilizer_residual (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    (pResidual 2 (S.setup.stabilizer (Additive.ofMul w))).map
      (S.setup.stabilizer (Additive.ofMul w)).subtype = S.setup.residual (Additive.ofMul w) := by
  have hv : (S.setup.model.coordinates (Additive.ofMul w)).2
      (S.setup.model.coordinates (Additive.ofMul w)).1 = 1 := by
    have hh : S.setup.quadratic (Additive.ofMul w) = 1 := by rwa [S.quadratic_eq]
    simpa only [S.setup.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hh
  apply map_injective (f := S.setup.model.group.toMonoidHom) S.setup.model.group.injective
  rw [map_embedded_pResidual, S.setup.stabilizer_map,
    fullStabilizer_embedded_twoResidual S.setup.degree _ hv,
    S.setup.residual_eq_innerStabilizer (by rwa [S.quadratic_eq]),
    S.setup.innerStabilizer_map]

omit [Finite G] in
/-- The actual nonsingular stabilizer has trivial two-core. -/
theorem nonsingular_stabilizer_twoCore (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    pCore 2 (S.setup.stabilizer (Additive.ofMul w)) = ⊥ := by
  have hn : 3 ≤ n-1 := by have := B.degree; omega
  have hp : 0 < n-1 := by omega
  let : IsQuasisimple (LinearGroup (n-1)) := IsQuasisimple.of_mulEquiv
    (ModelOrbits.AutomorphismModel.innerEquiv hp).symm
    (hG := (ModelOrbits.AutomorphismModel.inner_isComponent hn).2)
  let : Finite (LinearGroup (n-1)) := Finite.of_injective
    (fun g : LinearGroup (n-1) => (g : Space (n-1) → Space (n-1))) DFunLike.coe_injective
  have hcore : pCore 2 (LinearGroup (n-1)) = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center (G := LinearGroup (n-1)) 2).trans_eq
      (linear_center_eq_bot hp))
  have hau := automorphism_core_eq_bot 2
    (conj_injective_of_center_eq_bot (linear_center_eq_bot hp)) hcore ⊤ (fun _ => mem_top _)
  have haut : pCore 2 (MulAut (LinearGroup (n-1))) = ⊥ := by
    simpa only [pCore_map_iso, Subgroup.map_bot] using congrArg
      (map (Subgroup.topEquiv : (⊤ : Subgroup (MulAut (LinearGroup (n-1)))) ≃*
        MulAut (LinearGroup (n-1))).toMonoidHom) hau
  obtain ⟨e⟩ := (ChapterH.NaturalDual.SourceSetup.nonsingular_structure S.setup
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rwa [S.quadratic_eq])).2.2.1
  let e' := e.trans (MulAut.congr (projectiveEquivLinear hp))
  apply map_injective (f := e'.toMonoidHom) e'.injective
  rw [pCore_map_iso, Subgroup.map_bot]
  exact haut

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

/-- The literal action of C_M(w), with codomain the original source stabilizer. -/
@[expose] def localPointAction (w : componentOrbit V (T : Subgroup G)) :
    B.localPointCentralizer w →* S.setup.stabilizer (Additive.ofMul w) :=
  (B.actionProjection.comp (inclusion inf_le_left)).codRestrict _ (fun x => by
    have hh : inclusion inf_le_left x ∈
        (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := by
      rw [S.stabilizer_comap]
      exact x.property.2
    exact hh)

omit [Finite G] in
/-- Every source stabilizer element lifts to C_M(w). -/
theorem localPointAction_surjective (w : componentOrbit V (T : Subgroup G)) :
    Function.Surjective (S.localPointAction w) := by
  intro a
  obtain ⟨m,hm⟩ := B.actionProjection_surjective a
  have hh : m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := by
    change B.actionProjection m ∈ S.setup.stabilizer (Additive.ofMul w)
    rw [hm]
    exact a.property
  rw [S.stabilizer_comap] at hh
  exact ⟨⟨m, m.property,hh⟩,Subtype.ext hm⟩

/-- The original point residual maps onto the full stabilizer two-residual. -/
theorem residual_localPointAction (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    ((B.pointResidual w).subgroupOf (B.localPointCentralizer w)).map
      (S.localPointAction w) = pResidual 2 (S.setup.stabilizer (Additive.ofMul w)) := by
  apply map_injective (S.setup.stabilizer (Additive.ofMul w)).subtype_injective
  rw [S.nonsingular_stabilizer_residual w hw, ← S.pointResidual_action_range w]
  ext a
  constructor
  · rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨⟨r,hr⟩,rfl⟩
  · rintro ⟨r,rfl⟩
    have hrM : (r : G) ∈ B.localPointCentralizer w :=
      ⟨B.pointResidual_le_normalizer w r.property,
        (B.pointResidual_le w r.property).2⟩
    exact ⟨S.localPointAction w ⟨r,hrM⟩,⟨⟨r,hrM⟩,r.property,rfl⟩,rfl⟩

/-- The original residual and relative Sylow cover the entire source stabilizer. -/
theorem adapted_pointJoin_action_surjective
    (w : componentOrbit V (T : Subgroup G)) (hw : B.AdaptedPoint S w)
    (hPM : B.pointSylow w ≤ B.localPointCentralizer w) :
    Function.Surjective ((S.localPointAction w).comp
      (inclusion (sup_le (le_inf (B.pointResidual_le_normalizer w)
        ((B.pointResidual_le w).trans inf_le_right)) hPM))) := by
  let M := B.localPointCentralizer w
  let J := B.pointResidual w ⊔ B.pointSylow w
  have hJM : J ≤ M := sup_le (le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)) hPM
  let f := S.localPointAction w
  let q := f.comp (inclusion hJM)
  obtain ⟨P,hP⟩ := hw.local_sylow
  let Q := P.mapSurjective (S.localPointAction_surjective w)
  have hr : pResidual 2 (S.setup.stabilizer (Additive.ofMul w)) ≤ q.range := by
    rw [← S.residual_localPointAction w hw.nonsingular]
    rintro _ ⟨r,hr,rfl⟩
    exact ⟨⟨r,mem_sup_left hr⟩,rfl⟩
  have hq : (Q : Subgroup _) ≤ q.range := by
    rintro _ ⟨p,hp,rfl⟩
    have hp' : (p : G) ∈ B.pointSylow w := hP ▸ mem_map_of_mem M.subtype hp
    exact ⟨⟨p,mem_sup_right hp'⟩,rfl⟩
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top Q]
  exact sup_le hr hq

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

