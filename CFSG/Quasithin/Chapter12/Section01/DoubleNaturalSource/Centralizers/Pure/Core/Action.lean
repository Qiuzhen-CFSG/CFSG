module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Contracts
public import Theory.GroupTheory.PCoreRestriction

/-!
# The action of the literal pure-point core

The original point-centralizer core embeds in the relative normalizer core
using the marked ambient Sylow subgroup. The H.9 action then puts its natural
displacements in the point line and fixes the dual polar hyperplane. The moving
subgroup contains a nonsingular vector, so its centralizer equals the centralizer
of the whole doubled module.

Source: Aschbacher--Smith, 12.1.6, printed pp.791--792.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open BinaryNaturalDual.VectorStabilizers
variable {n : ℕ} {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup n M E)

theorem pure_core_natural_displacement (u : S.natural) (hu : (u : E) ≠ 0)
    (a : S.stabilizer u) (ha : a ∈ pCore 2 (S.stabilizer u))
    (v : E) (hv : v ∈ S.natural) :
    S.representation a.val v - v ∈ Submodule.span (ZMod 2) {(u : E)} := by
  let e := S.purePointEquiv u hu
  have he : e a ∈ pCore 2 (Pure.pointStabilizer (S.naturalCoordinates u)) := by
    rw [← pCore_map_iso 2 e]
    exact mem_map_of_mem _ ha
  rw [Pure.point_twoCore] at he
  have hd := (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff _ _).mp he
    (S.naturalCoordinates ⟨v,hv⟩)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hd
  have hU : S.naturalEmbedding (S.naturalCoordinates u) = (u : E) :=
    congrArg Subtype.val (S.naturalCoordinates.symm_apply_apply u)
  have hV : S.naturalEmbedding (S.naturalCoordinates ⟨v,hv⟩) = v :=
    congrArg Subtype.val (S.naturalCoordinates.symm_apply_apply ⟨v,hv⟩)
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  calc
    c • (u : E) = S.naturalEmbedding (c • S.naturalCoordinates u) := by rw [map_smul, hU]
    _ = S.naturalEmbedding ((e a).val (S.naturalCoordinates ⟨v,hv⟩) -
        S.naturalCoordinates ⟨v,hv⟩) := congrArg S.naturalEmbedding hc
    _ = S.representation a.val v - v := by
      rw [map_sub, ← S.pure_natural_action u hu, hV]

theorem pure_core_dualHyperplane_fixed (u : S.natural) (hu : (u : E) ≠ 0)
    (a : S.stabilizer u) (ha : a ∈ pCore 2 (S.stabilizer u))
    (v : E) (hv : v ∈ S.dualHyperplane u) : S.representation a.val v = v := by
  rw [S.dualHyperplane_eq_map] at hv
  obtain ⟨f,hf,rfl⟩ := hv
  have he : QuotientGroup.mk' (pCore 2 (S.stabilizer u)) a = 1 :=
    (QuotientGroup.eq_one_iff a).mpr ha
  have h := S.pureQuotientEquiv_action u hu a ⟨f,hf⟩
  rw [he,map_one] at h
  exact h

theorem pure_dual_displacement (u : S.natural) (hu : (u : E) ≠ 0)
    (a : S.stabilizer u) (v : E) (hv : v ∈ S.dual) :
    S.representation a.val v - v ∈ S.dualHyperplane u := by
  rw [← (S.pure_commutators u hu).2]
  exact Submodule.subset_span ⟨a.val, (S.pure_stabilizer_eq_residual u hu).1 ▸ a.property,
    v, hv, rfl⟩

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

namespace SourceModel
variable (S : B.SourceModel)

noncomputable def pureLocalAction (w : componentOrbit V (T : Subgroup G)) :
    (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) →*
      S.setup.stabilizer (Additive.ofMul w) where
  toFun m := ⟨B.actionProjection ⟨m, m.property.1⟩, by
    change (⟨m, m.property.1⟩ : normalizer (L : Set G)) ∈
      (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection
    rw [S.stabilizer_comap]
    exact m.property.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (B.actionProjection.map_mul
    ⟨x,x.property.1⟩ ⟨y,y.property.1⟩)

theorem pureLocalAction_surjective (w : componentOrbit V (T : Subgroup G)) :
    Function.Surjective (S.pureLocalAction w) := by
  intro a
  obtain ⟨m,hm⟩ := B.actionProjection_surjective a.val
  have hc : m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection :=
    by
      change B.actionProjection m ∈ S.setup.stabilizer (Additive.ofMul w)
      rw [hm]
      exact a.property
  rw [S.stabilizer_comap] at hc
  exact ⟨⟨m, m.property, hc⟩, Subtype.ext hm⟩

theorem purePointCore_le_localCore [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : B.PurePointSylows) (w : componentOrbit V (T : Subgroup G))
    (hw : w ≠ 1) (hp : (B.coordinates w).toAdd.2 = 0) :
    B.purePointCore w ≤
      (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)).pCoreIn 2 := by
  have hn := (B.purePointCore_le_normalizers hs w hw hp).trans inf_le_left
  rw [hNM] at hn
  have hq : B.purePointCore w ≤
      normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) :=
    le_inf hn (pCoreIn_le 2 _)
  exact (le_inf hq le_rfl).trans (inf_pCoreIn_le_of_le 2 inf_le_right)

theorem pureLocalAction_core (w : componentOrbit V (T : Subgroup G)) :
    (pCore 2 (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G)).map
      (S.pureLocalAction w) ≤ pCore 2 (S.setup.stabilizer (Additive.ofMul w)) :=
  le_sSup ⟨Subgroup.Normal.map inferInstance _ (S.pureLocalAction_surjective w),
    pCore_isPGroup.map _⟩

open scoped commutatorElement

private theorem span_point_mem_zpowers
    (w : componentOrbit V (T : Subgroup G))
    (v : Additive (componentOrbit V (T : Subgroup G)))
    (hv : v ∈ Submodule.span (ZMod 2) {Additive.ofMul w}) :
    (v.toMul : G) ∈ zpowers (w : G) := by
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  · simp

include S in
theorem pure_localCore_natural_commutator
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ⁅B.naturalSummand,
      (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)).pCoreIn 2⁆ ≤
        zpowers (w : G) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro q ⟨a,ha,rfl⟩ x hx
  let v : componentOrbit V (T : Subgroup G) := ⟨x, B.naturalSummand_le hx⟩
  let u : S.setup.natural := ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩
  have hv : Additive.ofMul v ∈ S.setup.natural :=
    (S.natural_marking v).mpr ((B.mem_naturalSummand v).mp hx)
  have hcore := S.pureLocalAction_core w (mem_map_of_mem _ ha)
  have hd := S.setup.pure_core_natural_displacement u hw
    (S.pureLocalAction w a) hcore (Additive.ofMul v) hv
  have hz := span_point_mem_zpowers w _ hd
  rw [S.representation_eq] at hz
  simp only [toMul_sub, div_eq_mul_inv] at hz
  change ((a : G) * x * (a : G)⁻¹) * x⁻¹ ∈ zpowers (w : G) at hz
  exact hz

/-- The literal dual polar hyperplane at the supplied natural point. -/
noncomputable def pureDualHyperplane (w : componentOrbit V (T : Subgroup G))
    (hp : (B.coordinates w).toAdd.2 = 0) : Subgroup G :=
  (S.setup.dualHyperplane
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩).toAddSubgroup.toSubgroup'.map
      (componentOrbit V (T : Subgroup G)).subtype

/-- The source hyperplane is the original dual summand intersected with the
polar hyperplane of the literal ambient point. -/
theorem mem_pureDualHyperplane
    (w : componentOrbit V (T : Subgroup G))
    (hp : (B.coordinates w).toAdd.2 = 0)
    (v : componentOrbit V (T : Subgroup G)) :
    (v : G) ∈ S.pureDualHyperplane w hp ↔
      (B.coordinates v).toAdd.1 = 0 ∧
        B.quadratic.polarBilin (Additive.ofMul w) (Additive.ofMul v) = 0 := by
  have he : (v : G) ∈ S.pureDualHyperplane w hp ↔
      Additive.ofMul v ∈ S.setup.dualHyperplane
        ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ := by
    constructor
    · rintro ⟨u,hu,he⟩
      have h : u = v := Subtype.ext he
      subst u
      exact hu
    · intro hv
      exact ⟨v,hv,rfl⟩
  rw [he, ChapterH.NaturalDual.SourceSetup.dualHyperplane, Submodule.mem_inf,
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  change (_ ∧ S.setup.quadratic.polarBilin (Additive.ofMul w) (Additive.ofMul v) = 0) ↔ _
  rw [S.dual_marking, S.quadratic_eq]

/-- The hyperplane retains its original dual summand embedding. -/
theorem pureDualHyperplane_le_dualSummand
    (w : componentOrbit V (T : Subgroup G))
    (hp : (B.coordinates w).toAdd.2 = 0) :
    S.pureDualHyperplane w hp ≤ B.dualSummand := by
  rintro x ⟨v,hv,rfl⟩
  exact (B.mem_dualSummand v).mpr
    ((S.mem_pureDualHyperplane w hp v).mp ⟨v,hv,rfl⟩).1

theorem pure_localCore_centralizes_dualHyperplane
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)).pCoreIn 2 ≤
      centralizer (S.pureDualHyperplane w hp : Set G) := by
  rintro q ⟨a,ha,rfl⟩ x ⟨v,hv,rfl⟩
  have hcore := S.pureLocalAction_core w (mem_map_of_mem _ ha)
  have he := S.setup.pure_core_dualHyperplane_fixed
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw
    (S.pureLocalAction w a) hcore (Additive.ofMul v) hv
  rw [S.representation_eq] at he
  have he' := congrArg (fun z => (z.toMul : G)) he
  change (a : G) * (v : G) * (a : G)⁻¹ = (v : G) at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- Every relative point stabilizer has its dual displacements in the
literal annihilator hyperplane. -/
theorem pure_local_dual_commutator
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ⁅B.dualSummand, normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)⁆ ≤
      S.pureDualHyperplane w hp := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro q hq x hx
  let a : (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) := ⟨q,hq⟩
  let v : componentOrbit V (T : Subgroup G) := ⟨x,B.dualSummand_le hx⟩
  have hv : Additive.ofMul v ∈ S.setup.dual :=
    (S.dual_marking v).mpr ((B.mem_dualSummand v).mp hx)
  have hd := S.setup.pure_dual_displacement
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw
    (S.pureLocalAction w a) (Additive.ofMul v) hv
  rw [S.representation_eq] at hd
  refine ⟨(B.quotientRepresentation (S.pureLocalAction w a).val (Additive.ofMul v) -
    Additive.ofMul v).toMul,hd,?_⟩
  simp only [toMul_sub, div_eq_mul_inv]
  rfl

/-- The ambient point core has the same dual displacement bound. -/
theorem purePointCore_dual_commutator [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : B.PurePointSylows) (w : componentOrbit V (T : Subgroup G))
    (hw : w ≠ 1) (hp : (B.coordinates w).toAdd.2 = 0) :
    ⁅B.dualSummand, B.purePointCore w⁆ ≤ S.pureDualHyperplane w hp :=
  (commutator_mono le_rfl ((purePointCore_le_localCore hNM hs w hw hp).trans
    (pCoreIn_le 2 _))).trans (S.pure_local_dual_commutator w hw hp)

include S in
theorem purePointCore_natural_commutator [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : B.PurePointSylows) (w : componentOrbit V (T : Subgroup G))
    (hw : w ≠ 1) (hp : (B.coordinates w).toAdd.2 = 0) :
    ⁅B.naturalSummand, B.purePointCore w⁆ ≤ zpowers (w : G) :=
  (commutator_mono le_rfl (purePointCore_le_localCore hNM hs w hw hp)).trans
    (S.pure_localCore_natural_commutator w hw hp)

theorem purePointCore_centralizes_dualHyperplane [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : B.PurePointSylows) (w : componentOrbit V (T : Subgroup G))
    (hw : w ≠ 1) (hp : (B.coordinates w).toAdd.2 = 0) :
    B.purePointCore w ≤ centralizer (S.pureDualHyperplane w hp : Set G) :=
  (purePointCore_le_localCore hNM hs w hw hp).trans
    (S.pure_localCore_centralizes_dualHyperplane w hw hp)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch


namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open BinaryNaturalDual.VectorStabilizers
variable {n : ℕ} {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup n M E)

private theorem pure_moving_has_nonsingular (u : S.natural) (hu : (u : E) ≠ 0) :
    ∃ v : E, v ∈ S.natural ⊔ S.dualHyperplane u ∧ S.quadratic v = 1 := by
  have hr := Pure.annihilator_finrank (S.naturalCoordinates_ne_zero u hu)
  have hd : 0 < Module.finrank (ZMod 2)
      (BinaryNaturalDual.VectorStabilizers.annihilator (S.naturalCoordinates u)) := by
    rw [hr]
    have := S.degree
    omega
  obtain ⟨f,hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hd
  have hf' : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  have hex : ∃ x, f.val x ≠ 0 := by
    by_contra! hn
    exact hf' (LinearMap.ext hn)
  obtain ⟨x,hx⟩ := hex
  have hx1 : f.val x = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hx
  refine ⟨S.naturalEmbedding x + S.dualEmbedding f.val, ?_, ?_⟩
  · apply Submodule.add_mem _
    · exact (le_sup_left : S.natural ≤ S.natural ⊔ S.dualHyperplane u)
        (S.naturalCoordinates.symm x).property
    · apply (le_sup_right : S.dualHyperplane u ≤ S.natural ⊔ S.dualHyperplane u)
      rw [S.dualHyperplane_eq_map]
      exact ⟨f.val,f.property,rfl⟩
  · rw [S.quadratic_apply, map_add, S.naturalEmbedding_coordinates, S.dualEmbedding_coordinates]
    simpa only [Prod.mk_add_mk, zero_add, add_zero, BinaryNaturalDual.quadratic_apply] using hx1

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
namespace SourceModel
variable (S : B.SourceModel)

/-- The moving subgroup of a pure point contains a nonsingular vector. -/
theorem pure_moving_has_nonsingular
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ∃ v : componentOrbit V (T : Subgroup G),
      (v : G) ∈ B.naturalSummand ⊔ S.pureDualHyperplane w hp ∧
        B.quadratic (Additive.ofMul v) = 1 := by
  obtain ⟨v,hv,hq⟩ := S.setup.pure_moving_has_nonsingular
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw
  refine ⟨v.toMul, ?_, S.quadratic_eq ▸ hq⟩
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
  change (a.toMul : G) * (b.toMul : G) ∈ _
  exact (B.naturalSummand ⊔ S.pureDualHyperplane w hp).mul_mem
    ((le_sup_left : B.naturalSummand ≤ B.naturalSummand ⊔ S.pureDualHyperplane w hp) ((B.mem_naturalSummand a.toMul).mpr ((S.natural_marking a.toMul).mp ha)))
    ((le_sup_right : S.pureDualHyperplane w hp ≤ B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⟨b.toMul,hb,rfl⟩)

/-- The centralizer comparison used in the last two paragraphs of 12.1.6.
It follows from the permitted nonsingular centralizers and the already
proved faithfulness of the original natural summand. -/
theorem pure_moving_centralizer
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hc : B.NonsingularCentralizers) (hd : B.SummandCentralizers)
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    centralizer (((B.naturalSummand ⊔ S.pureDualHyperplane w hp) : Subgroup G) : Set G) =
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  obtain ⟨v,hv,hq⟩ := S.pure_moving_has_nonsingular w hw hp
  have hM := (centralizer_le (Set.singleton_subset_iff.mpr hv)).trans
    (hc v (by rw [hq]; exact one_ne_zero))
  apply le_antisymm
  · apply le_trans _ hd.natural
    rw [hNM]
    exact le_inf hM (centralizer_le
      (show B.naturalSummand ≤ B.naturalSummand ⊔ S.pureDualHyperplane w hp from le_sup_left))
  · exact centralizer_le (sup_le B.naturalSummand_le
      ((S.pureDualHyperplane_le_dualSummand w hp).trans B.dualSummand_le))

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
