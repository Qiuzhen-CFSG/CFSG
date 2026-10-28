module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The root calculations extend the licensed split-octonion G₂ model, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: full-parabolic residuals, generation, maximality, root triple
commutators, and lifting through homomorphisms with two-group kernel.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Higher-field G₂ parabolic residuals and their lifted core obstruction

The solvable residual of each full root parabolic is its concrete rank-one
local group: that group is perfect for q > 2, normal in the parabolic, and
supplemented by the solvable Borel. The two residuals generate G₂, since their
rank-one tori generate the full split torus. The proper positive-root overgroup
theorem proves maximality of both full parabolics.

The root identities [[C(1),F(1)],E(1)] = A(1) and
[[F(1),E(1)],D(1)] = A(1) give nonzero triple commutators with both outside
entries in the corresponding actual two-core. A surjective model map with
two-group kernel preserves the intrinsic core on parabolic residuals, giving
both their PSL₂ quotients and the nonzero triple commutator upstairs. The
kernel condition is explicit and is not inferred from a model label.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.19,
printed p.931, and the G₂ local structure F.1.12, printed pp.262–264.
-/

@[expose] public section

open Subgroup
namespace Atlas.G2.HigherFieldResiduals
open LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

private theorem residual_eq_of_solvable_supplement {G : Type*} [Group G]
    (L B P : Subgroup G) (hL : L ≤ P) (hB : B ≤ P)
    [(L.subgroupOf P).Normal] [Group.IsPerfect L] [Group.IsSolvable B]
    (hgen : L ⊔ B = P) : (solvableResidual P).map P.subtype = L := by
  have hg : L.subgroupOf P ⊔ B.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup hL hB, hgen, subgroupOf_self]
  let q := QuotientGroup.mk' (L.subgroupOf P)
  let f : B.subgroupOf P →* P ⧸ L.subgroupOf P := q.comp (B.subgroupOf P).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf P) y
    obtain ⟨l, hl, b, hb, rfl⟩ := mem_sup_of_normal_left.mp (hg.symm ▸ mem_top x)
    refine ⟨⟨b, hb⟩, ?_⟩
    change q b = q (l*b)
    rw [map_mul, show q l = 1 from (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  let : Group.IsSolvable (B.subgroupOf P) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hB).toMonoidHom) (subgroupOfEquivOfLe hB).injective
  let : Group.IsSolvable (P ⧸ L.subgroupOf P) := Group.isSolvable_of_surjective hf
  apply le_antisymm _ (le_map_solvableResidual_of_isPerfect L P hL)
  exact (map_mono (solvableResidual_le_of_solvable_quotient (L.subgroupOf P))).trans_eq
    (map_subgroupOf_eq_of_le hL)

omit [CharP F 2] in
private theorem local₁_le_parabolic₁ : local₁ (F := F) ≤ parabolic₁ := by
  rw [← local₁_sup_borel]
  exact le_sup_left

theorem parabolic₁_residual [Finite F] (hq : 2 < Nat.card F) :
    (solvableResidual (parabolic₁ (F := F))).map parabolic₁.subtype = local₁ := by
  let := local₁_isPerfect hq
  let := DerivedNormalizerSolvable.isSolvable_borel (F := F)
  exact residual_eq_of_solvable_supplement local₁ borel parabolic₁
    local₁_le_parabolic₁ borel_le_parabolic₁ local₁_sup_borel

theorem parabolic₂_residual [Finite F] (hq : 2 < Nat.card F) :
    (solvableResidual (parabolic₂ (F := F))).map parabolic₂.subtype = local₂ := by
  let := local₂_isPerfect hq
  let := DerivedNormalizerSolvable.isSolvable_borel (F := F)
  exact residual_eq_of_solvable_supplement local₂ borel parabolic₂
    local₂_le_parabolic₂ borel_le_parabolic₂ local₂_sup_borel

theorem locals_generate : local₁ (F := F) ⊔ local₂ = ⊤ := by
  have ht : splitTorus (K := F) ≤ local₁ ⊔ local₂ := by
    rintro _ ⟨⟨l,m⟩, rfl⟩
    have hl : torus l l⁻¹ ∈ local₁ (F := F) := short_torus_mem_local₁ l
    have hm : torus 1 (l*m) ∈ local₂ (F := F) := by
      rw [local₂_eq_fixingFirstVector]
      change (torus 1 (l*m)).val (Atlas.SplitOctonion.basisVector 0) = _
      simpa using torus_first_basis (1 : Fˣ) (l*m)
    have he : torusHom (l,m) = torus l l⁻¹ * torus 1 (l*m) := by
      change torusHom (l,m) = torusHom (l,l⁻¹) * torusHom (1,l*m)
      rw [← map_mul]
      congr 1
      ext <;> simp
    rw [he]
    exact (local₁ ⊔ local₂).mul_mem (mem_sup_left hl) (mem_sup_right hm)
  have hb : borel (K := F) ≤ local₁ ⊔ local₂ :=
    sup_le (unipotent_le_local₁.trans le_sup_left) ht
  apply top_unique
  rw [← parabolics_generate, ← local₁_sup_borel, ← local₂_sup_borel]
  exact sup_le (sup_le le_sup_left hb) (sup_le le_sup_right hb)

theorem residuals_generate [Finite F] (hq : 2 < Nat.card F) :
    (solvableResidual (parabolic₁ (F := F))).map parabolic₁.subtype ⊔
      (solvableResidual (parabolic₂ (F := F))).map parabolic₂.subtype = ⊤ := by
  rw [parabolic₁_residual hq, parabolic₂_residual hq, locals_generate]

omit [CharP F 2] in
private theorem parabolic₁_ne_top : parabolic₁ (F := F) ≠ ⊤ := by
  intro ht
  have hw : (weylR : Model F) ∈ shortPlaneStabilizer :=
    parabolic₁_le_shortPlaneStabilizer (ht.symm ▸ mem_top _)
  have h := hw.1 _ (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  simp [weylR, weylREquiv, weylRLinear, weylRApply, Atlas.SplitOctonion.basisVector] at h

omit [CharP F 2] in
private theorem parabolic₂_ne_top : parabolic₂ (F := F) ≠ ⊤ := by
  intro ht
  have hw : (weylS : Model F) ∈ pointStabilizer := by
    rw [← parabolic_eq_pointStabilizer]
    exact ht.ge (mem_top _)
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp hw
  have h := congrFun ha 1
  simp [weylS, weylSEquiv, weylSLinear, weylSApply, Atlas.SplitOctonion.basisVector] at h

theorem parabolic₁_isCoatom : IsCoatom (parabolic₁ (F := F)) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨parabolic₁_ne_top, fun H hH hPH => ?_⟩
  rcases ProperSylowOvergroups.le_parabolic H
    ((show unipotent ≤ borel from le_sup_left).trans (borel_le_parabolic₁.trans hPH))
    (lt_top_iff_ne_top.mpr hH) with h | h
  · exact h
  · have he : (⊤ : Subgroup (Model F)) ≤ parabolic₂ := by
      rw [← parabolics_generate]
      exact sup_le (hPH.trans h) le_rfl
    exact (parabolic₂_ne_top (top_unique he)).elim

theorem parabolic₂_isCoatom : IsCoatom (parabolic₂ (F := F)) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨parabolic₂_ne_top, fun H hH hPH => ?_⟩
  rcases ProperSylowOvergroups.le_parabolic H
    ((show unipotent ≤ borel from le_sup_left).trans (borel_le_parabolic₂.trans hPH))
    (lt_top_iff_ne_top.mpr hH) with h | h
  · have he : (⊤ : Subgroup (Model F)) ≤ parabolic₁ := by
      rw [← parabolics_generate]
      exact sup_le le_rfl (hPH.trans h)
    exact (parabolic₁_ne_top (top_unique he)).elim
  · exact h


open scoped commutatorElement

private theorem rootCF : ⁅rootC (1 : F), rootF (1 : F)⁆ = rootB (1 : F) := by
  have hc : rootC (1 : F) = unipotentProduct ![0,0,1,0,0,0] := by simp [unipotentProduct]
  have hf : rootF (1 : F) = unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  have hb : rootB (1 : F) = unipotentProduct ![0,1,0,0,0,0] := by simp [unipotentProduct]
  rw [hc,hf,hb,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
    unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]

omit [CharP F 2] in
private theorem rootBE : ⁅rootB (1 : F), rootE (1 : F)⁆ = rootA (1 : F) := by
  simpa [unipotentProduct] using
    fiveRoot_commutator (F := F) ![0,1,0,0,0,0] ![0,0,0,0,1,0] rfl rfl

private theorem rootFE : ⁅rootF (1 : F), rootE (1 : F)⁆ = unipotentProduct ![1,1,1,1,0,0] := by
  have hf : rootF (1 : F) = unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  have he : rootE (1 : F) = unipotentProduct ![0,0,0,0,1,0] := by simp [unipotentProduct]
  rw [hf,he,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
    unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]

private theorem rootFED : ⁅unipotentProduct (K := F) ![1,1,1,1,0,0], rootD (1 : F)⁆ = rootA (1 : F) := by
  have hd : rootD (1 : F) = unipotentProduct ![0,0,0,1,0,0] := by simp [unipotentProduct]
  have ha : rootA (1 : F) = unipotentProduct ![1,0,0,0,0,0] := by simp [unipotentProduct]
  rw [hd,ha,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
    unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]

theorem short_root_triple : ⁅⁅rootC (1 : F), rootF (1 : F)⁆, rootE (1 : F)⁆ = rootA (1 : F) := by
  rw [rootCF,rootBE]

theorem long_root_triple : ⁅⁅rootF (1 : F), rootE (1 : F)⁆, rootD (1 : F)⁆ = rootA (1 : F) := by
  rw [rootFE,rootFED]

omit [CharP F 2] in
private theorem rootA_one_ne : rootA (1 : F) ≠ 1 := by
  intro h
  exact one_ne_zero (rootA_injective (h.trans rootA_zero.symm))

theorem short_core_triple : ⁅⁅radical₁ (F := F), local₁ (F := F)⁆, radical₁ (F := F)⁆ ≠ ⊥ := by
  have hC : rootC (1 : F) ∈ radical₁ :=
    ⟨![0,0,1,0,0,0], rfl, by simp [unipotentProduct]⟩
  have hF : rootF (1 : F) ∈ local₁ :=
    unipotent_le_local₁ (subset_closure (by simp))
  have hE : rootE (1 : F) ∈ radical₁ :=
    ⟨![0,0,0,0,1,0], rfl, by simp [unipotentProduct]⟩
  intro h
  have hm := commutator_mem_commutator (commutator_mem_commutator hC hF) hE
  rw [short_root_triple, h] at hm
  exact rootA_one_ne hm

theorem long_core_triple : ⁅⁅radical₂ (F := F), local₂ (F := F)⁆, radical₂ (F := F)⁆ ≠ ⊥ := by
  have hF : rootF (1 : F) ∈ radical₂ :=
    ⟨![0,0,0,0,0,1], rfl, by simp [unipotentProduct]⟩
  have hE : rootE (1 : F) ∈ local₂ :=
    unipotent_le_local₂ (subset_closure (by simp))
  have hD : rootD (1 : F) ∈ radical₂ :=
    ⟨![0,0,0,1,0,0], rfl, by simp [unipotentProduct]⟩
  intro h
  have hm := commutator_mem_commutator (commutator_mem_commutator hF hE) hD
  rw [long_root_triple, h] at hm
  exact rootA_one_ne hm



open scoped MatrixGroups

/-- The two actual full root parabolics, indexed with the special radical first. -/
def parabolicAt (i : Fin 2) : Subgroup (Model F) :=
  if i = 0 then parabolic₁ else parabolic₂

/-- Their rank-one residual groups, before any source-group lifting. -/
def localAt (i : Fin 2) : Subgroup (Model F) :=
  if i = 0 then local₁ else local₂

theorem parabolicAt_isCoatom (i : Fin 2) : IsCoatom (parabolicAt (F := F) i) := by
  fin_cases i
  · exact parabolic₁_isCoatom
  · exact parabolic₂_isCoatom

omit [CharP F 2] in
theorem unipotent_le_parabolicAt (i : Fin 2) : unipotent (K := F) ≤ parabolicAt i := by
  fin_cases i
  · exact (show unipotent ≤ borel from le_sup_left).trans borel_le_parabolic₁
  · exact unipotent_le_parabolic

theorem parabolicAt_residual [Finite F] (hq : 2 < Nat.card F) (i : Fin 2) :
    (solvableResidual (parabolicAt (F := F) i)).map (parabolicAt i).subtype = localAt i := by
  fin_cases i
  · exact parabolic₁_residual hq
  · exact parabolic₂_residual hq

noncomputable def localCoreQuotientEquivPSL [Finite F] (i : Fin 2) :
    localAt (F := F) i ⧸ pCore 2 (localAt (F := F) i) ≃* PSL(2,F) := by
  classical
  by_cases h : i = 0
  · subst i
    exact local₁CoreQuotientEquivPSL (F := F)
  · have hi : i = 1 := by omega
    subst i
    exact local₂CoreQuotientEquivPSL (F := F)

theorem local_core_triple [Finite F] (i : Fin 2) :
    ⁅⁅pCore 2 (localAt (F := F) i), (⊤ : Subgroup (localAt (F := F) i))⁆, pCore 2 (localAt (F := F) i)⁆ ≠ ⊥ := by
  intro h
  have hm := congrArg (Subgroup.map (localAt (F := F) i).subtype) h
  rw [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] at hm
  fin_cases i
  · change ⁅⁅(local₁ (F := F)).pCoreIn 2, local₁⁆, local₁.pCoreIn 2⁆ = ⊥ at hm
    rw [local₁_pCoreIn] at hm
    exact short_core_triple hm
  · change ⁅⁅(local₂ (F := F)).pCoreIn 2, local₂⁆, local₂.pCoreIn 2⁆ = ⊥ at hm
    rw [local₂_pCoreIn] at hm
    exact long_core_triple hm

variable {X : Type*} [Group X] [Finite X] [Finite F]

/-- The residual of a literal parabolic preimage maps onto the root local group. -/
theorem preimage_residual_image (f : X →* Model F) (hf : Function.Surjective f)
    (hq : 2 < Nat.card F) (i : Fin 2) :
    ((solvableResidual ((parabolicAt i).comap f)).map ((parabolicAt i).comap f).subtype).map f =
      localAt i := by
  rw [map_solvableResidual_comap f hf, parabolicAt_residual hq]

/-- The explicit restriction of the model map to the lifted solvable residual. -/
def preimageResidualMap (f : X →* Model F) (hf : Function.Surjective f)
    (hq : 2 < Nat.card F) (i : Fin 2) :
    solvableResidual ((parabolicAt i).comap f) →* localAt (F := F) i :=
  ((f.comp ((parabolicAt i).comap f).subtype).comp
    (solvableResidual ((parabolicAt i).comap f)).subtype).codRestrict _ (by
      intro x
      rw [← preimage_residual_image f hf hq i]
      exact mem_map_of_mem f (mem_map_of_mem _ x.property))

theorem preimageResidualMap_surjective (f : X →* Model F) (hf : Function.Surjective f)
    (hq : 2 < Nat.card F) (i : Fin 2) :
    Function.Surjective (preimageResidualMap f hf hq i) := by
  intro y
  have hy := (preimage_residual_image f hf hq i).ge y.property
  obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem preimageResidualMap_ker_isTwoGroup (f : X →* Model F) (hf : Function.Surjective f)
    (hq : 2 < Nat.card F) (i : Fin 2) (hk : IsPGroup 2 f.ker) :
    IsPGroup 2 (preimageResidualMap f hf hq i).ker := by
  unfold preimageResidualMap
  rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, ← MonoidHom.comap_ker]
  exact (hk.comap_of_injective _ ((parabolicAt i).comap f).subtype_injective).comap_of_injective
    _ (solvableResidual ((parabolicAt i).comap f)).subtype_injective

/-- The intrinsic core quotient of the lifted residual, with the action kernel
controlled as a two-group rather than inferred from the quotient's group name. -/
noncomputable def preimageResidualCoreQuotientEquivPSL
    (f : X →* Model F) (hf : Function.Surjective f) (hq : 2 < Nat.card F)
    (hk : IsPGroup 2 f.ker) (i : Fin 2) :
    (solvableResidual ((parabolicAt i).comap f) ⧸
      pCore 2 (solvableResidual ((parabolicAt i).comap f))) ≃* PSL(2,F) :=
  ((preimageResidualMap f hf hq i).pCoreQuotientEquiv
    (preimageResidualMap_surjective f hf hq i)
    (preimageResidualMap_ker_isTwoGroup f hf hq i hk)).trans (localCoreQuotientEquivPSL i)

/-- The root triple remains nonzero in the actual preimage residual's core. -/
theorem preimage_residual_core_triple
    (f : X →* Model F) (hf : Function.Surjective f) (hq : 2 < Nat.card F)
    (hk : IsPGroup 2 f.ker) (i : Fin 2) :
    let R := solvableResidual ((parabolicAt i).comap f)
    ⁅⁅pCore 2 R, (⊤ : Subgroup R)⁆, pCore 2 R⁆ ≠ ⊥ := by
  dsimp only
  let g := preimageResidualMap f hf hq i
  have hg := preimageResidualMap_surjective f hf hq i
  have hcore : (pCore 2 (solvableResidual ((parabolicAt i).comap f))).map g =
      pCore 2 (localAt i) := by
    rw [← g.comap_pCore_of_ker_isPGroup hg (preimageResidualMap_ker_isTwoGroup f hf hq i hk),
      map_comap_eq_self_of_surjective hg]
  intro h
  have hm := congrArg (Subgroup.map g) h
  rw [map_commutator, map_commutator, hcore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hg, Subgroup.map_bot] at hm
  exact local_core_triple i hm

end Atlas.G2.HigherFieldResiduals

end
