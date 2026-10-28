module
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.SpecificGroups.HigherLinear.SubspaceTransport
public import Theory.SpecificGroups.SL2.RadicalSubgroups
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
/-!
# Natural coordinates for radical normalizers in binary SL₃

The canonical radical filtration supplies a nonzero proper subspace. An
ambient linear change of basis marks its stabilizer as the point or plane
parabolic. A two-subgroup has trivial scalar character, so the radical lies
in the corresponding affine local. The SL₂ quotient then identifies it with
the parabolic core or a full Sylow subgroup. A nontrivial perfect subgroup
of the normalizer excludes the latter, since the full SL₃ Sylow normalizer
is solvable. The odd scalar centre is retained throughout.

The exported frame is an actual linear equivalence: `slConj_apply` preserves
the natural action for downstream block-module transport.
Source: Aschbacher–Smith C.2.7(3)(g), C.4.5–7, printed pp.145–153.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RadicalNormalizer
open Matrix.HigherLinear.SubspaceTransport
variable {F : Type*} [Field F]

private def pointSpace : Submodule F (Fin 3 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl,rfl⟩
  add_mem' := by rintro u v ⟨h1,h2⟩ ⟨k1,k2⟩; simp_all
  smul_mem' := by rintro a v ⟨h1,h2⟩; simp_all

private def lineSpace : Submodule F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; change u 2 + v 2 = 0; rw [hu,hv,add_zero]
  smul_mem' := by intro a v hv; change a * v 2 = 0; rw [hv,mul_zero]

private def pointEquiv : pointSpace (F := F) ≃ₗ[F] F where
  toFun v := v.val 0
  invFun a := ⟨![a,0,0],⟨rfl,rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · exact v.property.1.symm
    · exact v.property.2.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def lineEquiv : lineSpace (F := F) ≃ₗ[F] (Fin 2 → F) where
  toFun v i := v.val i.castSucc
  invFun a := ⟨![a 0,a 1,0],rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact v.property.symm
  right_inv a := by ext i; fin_cases i <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem point_parabolic : Matrix.HigherLinear.parabolicSL (pointSpace (F := F)) =
    pointParabolicSL F := by
  ext g
  rw [mem_parabolicSL_iff, pointParabolicSL, MulAction.mem_stabilizer_set]
  rfl

private theorem line_parabolic : Matrix.HigherLinear.parabolicSL (lineSpace (F := F)) =
    lineParabolicSL F := by
  ext g
  rw [mem_parabolicSL_iff, lineParabolicSL, MulAction.mem_stabilizer_set]
  rfl

private theorem exists_subspace_frame (W S : Submodule F (Fin 3 → F))
    (hd : Module.finrank F W = Module.finrank F S) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (Matrix.HigherLinear.parabolicSL W).map (slConj e).toMonoidHom =
        Matrix.HigherLinear.parabolicSL S := by
  let f := LinearEquiv.ofFinrankEq W S hd
  obtain ⟨e,he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hmem (x : Fin 3 → F) : e x ∈ S ↔ x ∈ W := by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := f.surjective ⟨e x,hx⟩
      have hey : e (y : Fin 3 → F) = e x := (he y).symm.trans (congrArg Subtype.val hy)
      exact e.injective hey ▸ y.property
    · intro hx
      rw [←he ⟨x,hx⟩]
      exact (f ⟨x,hx⟩).property
  refine ⟨e,?_⟩
  ext g
  obtain ⟨g,rfl⟩ := (slConj e).surjective g
  rw [Subgroup.mem_map_equiv,MulEquiv.symm_apply_apply,conj_mem W S e hmem]

/-- Change of basis identifies the literal subspace stabilizer with a standard
parabolic, while retaining the ambient linear equivalence. -/
theorem exists_parabolic_frame (W : Submodule F (Fin 3 → F))
    (hne : W ≠ ⊥) (hproper : W ≠ ⊤) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (Matrix.HigherLinear.parabolicSL W).map (slConj e).toMonoidHom = pointParabolicSL F ∨
      (Matrix.HigherLinear.parabolicSL W).map (slConj e).toMonoidHom = lineParabolicSL F := by
  have hp : 0 < Module.finrank F W :=
    Nat.pos_of_ne_zero (fun h => hne (Submodule.finrank_eq_zero.mp h))
  have ht := Submodule.finrank_lt hproper
  rw [Module.finrank_fin_fun] at ht
  have hc : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hc with hd | hd
  · have hs : Module.finrank F (pointSpace (F := F)) = 1 := by
      rw [(pointEquiv (F := F)).finrank_eq,Module.finrank_self]
    obtain ⟨e,he⟩ := exists_subspace_frame W pointSpace (hd.trans hs.symm)
    exact ⟨e,Or.inl (he.trans point_parabolic)⟩
  · have hs : Module.finrank F (lineSpace (F := F)) = 2 := by
      rw [(lineEquiv (F := F)).finrank_eq,Module.finrank_fin_fun]
    obtain ⟨e,he⟩ := exists_subspace_frame W lineSpace (hd.trans hs.symm)
    exact ⟨e,Or.inr (he.trans line_parabolic)⟩

variable [Finite F] [CharP F 2]

private def pointScalar : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def lineScalar : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

omit [Finite F] in
private theorem scalar_of_twoGroup {G : Type*} [Group G]
    (R P : Subgroup G) (hR : IsPGroup 2 R) (hRP : R ≤ P) (f : P →* F)
    (r : R) : f ⟨r,hRP r.property⟩ = 1 := by
  obtain ⟨k,hk⟩ := hR.exists_pow_pow_eq_one r
  have he : f ⟨r,hRP r.property⟩ ^ (2 ^ k) = 1 := by
    rw [←map_pow]
    have hh : (⟨r,hRP r.property⟩ : P) ^ (2 ^ k) = 1 :=
      Subtype.ext (congrArg (fun y : R => (y : G)) hk)
    rw [hh,map_one]
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def] using he)

private theorem point_twoGroup_le_local (R : Subgroup SL(3,F)) (hR : IsPGroup 2 R)
    (hRP : R ≤ pointParabolicSL F) : R ≤ pointLocalSL F := by
  intro r hr
  exact (mem_pointLocalSL_iff F r).mpr
    ⟨scalar_of_twoGroup R _ hR hRP pointScalar ⟨r,hr⟩,
      (mem_pointParabolicSL_iff F r).mp (hRP hr)⟩

private theorem line_twoGroup_le_local (R : Subgroup SL(3,F)) (hR : IsPGroup 2 R)
    (hRP : R ≤ lineParabolicSL F) : R ≤ lineLocalSL F := by
  intro r hr
  exact (mem_lineLocalSL_iff F r).mpr
    ⟨(mem_lineParabolicSL_iff F r).mp (hRP hr) |>.1,
      (mem_lineParabolicSL_iff F r).mp (hRP hr) |>.2,
      scalar_of_twoGroup R _ hR hRP lineScalar ⟨r,hr⟩⟩

private theorem normalizer_eq_parabolic_or_sylow
    (R P L : Subgroup SL(3,F)) (hR : R.IsPRadical 2)
    (hRL : R ≤ L) (hNP : normalizer (R : Set SL(3,F)) ≤ P)
    (hPL : P ≤ normalizer (L : Set SL(3,F)))
    (q : L →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (T : Sylow 2 SL(3,F)) (hTL : (T : Subgroup SL(3,F)) ≤ L) :
    normalizer (R : Set SL(3,F)) = P ∨
      ∃ S : Sylow 2 SL(3,F), (S : Subgroup SL(3,F)) = R := by
  rcases Matrix.SpecialLinearGroup.radical_local_eq_kernel_or_sylow
    R L hR hRL (hNP.trans hPL) q hq hk T hTL with he | hs
  · left
    have hc : q.ker = pCore 2 L := by
      have hh := q.comap_pCore_of_ker_isPGroup hq hk (p := 2)
      rwa [Matrix.SL2.twoCore_eq_bot F,MonoidHom.comap_bot] at hh
    apply le_antisymm hNP
    rw [he,hc]
    exact hPL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  · exact Or.inr hs

/-- A radical normalizer is a full maximal parabolic in a compatible natural
basis, unless the radical is itself Sylow. -/
theorem radical_normalizer_parabolic_or_sylow
    (R : Subgroup SL(3,F)) (hR : R.IsPRadical 2)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    (∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (normalizer (R : Set SL(3,F))).map (slConj e).toMonoidHom = pointParabolicSL F ∨
      (normalizer (R : Set SL(3,F))).map (slConj e).toMonoidHom = lineParabolicSL F) ∨
      ∃ S : Sylow 2 SL(3,F), (S : Subgroup SL(3,F)) = R := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  obtain ⟨k,W,hk,_,hproper,hN⟩ := Matrix.HigherLinear.radical_normalizer_eq_partialFlag_three R hR
  have hkpos : 0 < k := by omega
  let i : Fin k := ⟨0,hkpos⟩
  obtain ⟨e,he⟩ := exists_parabolic_frame (W i) (hproper i).1 (hproper i).2
  let a := slConj e
  let U := R.map a.toMonoidHom
  have hu : U.IsPRadical 2 := hR.map_equiv a
  have hmap : (normalizer (R : Set SL(3,F))).map a.toMonoidHom =
      normalizer (U : Set SL(3,F)) := map_equiv_normalizer_eq R a
  have hNW : normalizer (R : Set SL(3,F)) ≤ Matrix.HigherLinear.parabolicSL (W i) := by
    rw [hN]
    exact iInf_le _ i
  have hsyl (S : Sylow 2 SL(3,F)) (hS : (S : Subgroup SL(3,F)) = U) :
      ∃ S : Sylow 2 SL(3,F), (S : Subgroup SL(3,F)) = R := by
    refine ⟨S.mapSurjective (f := a.symm.toMonoidHom) a.symm.surjective,?_⟩
    change (S : Subgroup SL(3,F)).map a.symm.toMonoidHom = R
    rw [hS]
    simp [U,Subgroup.map_map]
  rcases he with he | he
  · have hp : normalizer (U : Set SL(3,F)) ≤ pointParabolicSL F := by
      rw [←hmap,←he]
      exact map_mono hNW
    have hPL : pointParabolicSL F ≤ normalizer (pointLocalSL F : Set SL(3,F)) := by
      rw [←pointParabolicSL_residual F hcard]
      simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
        (solvableResidual (pointParabolicSL F)).le_normalizer_map (pointParabolicSL F).subtype
    let q := (pointLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (pointLocalSL F)))
    have hq := (pointLocalSLCoreQuotientEquiv F).surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 (pointLocalSL F)))
    have hqker : q.ker = pCore 2 (pointLocalSL F) := by
      rw [MonoidHom.ker_comp_of_injective _ _ (pointLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
    rcases normalizer_eq_parabolic_or_sylow U _ _ hu
      (point_twoGroup_le_local U hu.isPGroup (U.le_normalizer.trans hp)) hp hPL q hq
      (hqker ▸ pCore_isPGroup) (CartanActions.BorelQuotient.unipotentSLSylow F (by omega) hF)
      inf_le_left with h | ⟨S,hS⟩
    · exact Or.inl ⟨e,Or.inl (hmap.trans h)⟩
    · exact Or.inr (hsyl S hS)
  · have hp : normalizer (U : Set SL(3,F)) ≤ lineParabolicSL F := by
      rw [←hmap,←he]
      exact map_mono hNW
    have hPL : lineParabolicSL F ≤ normalizer (lineLocalSL F : Set SL(3,F)) := by
      rw [←lineParabolicSL_residual F hcard]
      simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
        (solvableResidual (lineParabolicSL F)).le_normalizer_map (lineParabolicSL F).subtype
    let q := (lineLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (lineLocalSL F)))
    have hq := (lineLocalSLCoreQuotientEquiv F).surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 (lineLocalSL F)))
    have hqker : q.ker = pCore 2 (lineLocalSL F) := by
      rw [MonoidHom.ker_comp_of_injective _ _ (lineLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
    rcases normalizer_eq_parabolic_or_sylow U _ _ hu
      (line_twoGroup_le_local U hu.isPGroup (U.le_normalizer.trans hp)) hp hPL q hq
      (hqker ▸ pCore_isPGroup) (CartanActions.BorelQuotient.unipotentSLSylow F (by omega) hF)
      inf_le_right with h | ⟨S,hS⟩
    · exact Or.inl ⟨e,Or.inr (hmap.trans h)⟩
    · exact Or.inr (hsyl S hS)
omit [CharP F 2] in
/-- Full Sylow normalizers are solvable in the full special-linear group;
the odd scalar centre is retained. -/
theorem sylow_normalizer_solvable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 SL(3,F)) : Group.IsSolvable (normalizer (S : Set SL(3,F))) := by
  let N := normalizer (S : Set SL(3,F))
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  let e := CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv F hn hF S
  let : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  apply Group.isSolvable_of_ker_le_range (pCore 2 N).subtype (QuotientGroup.mk' (pCore 2 N))
  rw [QuotientGroup.ker_mk',range_subtype]

/-- A nontrivial perfect subgroup excludes the full-Sylow alternative, leaving
an actual natural-basis marking of the radical normalizer. -/
theorem radical_normalizer_frame_of_perfect
    (R B : Subgroup SL(3,F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥) (hBN : B ≤ normalizer (R : Set SL(3,F)))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (normalizer (R : Set SL(3,F))).map (slConj e).toMonoidHom = pointParabolicSL F ∨
      (normalizer (R : Set SL(3,F))).map (slConj e).toMonoidHom = lineParabolicSL F := by
  rcases radical_normalizer_parabolic_or_sylow R hR hn hF with he | ⟨S,hS⟩
  · exact he
  · let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hne
    let : Group.IsSolvable (normalizer (R : Set SL(3,F))) :=
      hS ▸ sylow_normalizer_solvable (by omega) hF S
    exact (Group.IsPerfect.not_isSolvable B
      (Group.isSolvable_of_isSolvable_injective
        (f := inclusion hBN) (inclusion_injective hBN))).elim

end Matrix.PSL3.LinearThree.RadicalNormalizer
