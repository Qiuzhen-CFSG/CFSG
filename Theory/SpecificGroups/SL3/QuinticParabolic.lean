module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation
public import Theory.SpecificGroups.PSL3.SplitPrimeActors.Reduction
public import Theory.GroupAction.SolvableLocalQuotient
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Mathlib.Algebra.CharP.Reduced
public import Theory.SpecificGroups.PSL2.BinaryOuter
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
/-!
# Quintic actors normalized by a full linear-three parabolic

A solvable actor subgroup normalized by a parabolic fixes the simple SL₂
quotient of its perfect local residual. The literal semilinear quotient
formula kills the coefficient automorphism. If the field units have order
prime to five, a determinant correction puts the quintic linear actor in
the local subgroup. Trivial quotient action then puts it in the two-core,
which excludes order five. Faithful descent and the actual local projections
retain the cubic SL₃ center when transporting the projective calculation.

Source application: Aschbacher--Smith 14.6.15, printed p.1035; the local
coordinates are those of F.1.12, printed p.264. Imported ATLAS models retain
attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.QuinticParabolic
open OuterExtensions OuterExtensions.CoreCalculation
variable (F : Type*) [Field F]
private def distinguished (point : Bool) (g : GL (Fin 3) F) : F :=
  if point then g.val 0 0 else g.val 2 2
private theorem shape_mul (point : Bool) (g h : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hh : ParabolicShape F point h) :
    ParabolicShape F point (g * h) := by
  cases point <;> obtain ⟨hg1,hg2⟩ := hg <;> obtain ⟨hh1,hh2⟩ := hh <;>
    simp [ParabolicShape, Matrix.mul_apply, Fin.sum_univ_three, hg1,hg2,hh1,hh2]
private theorem distinguished_mul (point : Bool) (g h : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hh : ParabolicShape F point h) :
    distinguished F point (g * h) = distinguished F point g * distinguished F point h := by
  cases point <;> obtain ⟨hg1,hg2⟩ := hg <;> obtain ⟨hh1,hh2⟩ := hh <;>
    simp [distinguished, Matrix.mul_apply, Fin.sum_univ_three, hg1,hg2,hh1,hh2]
private theorem shape_pow (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (k : ℕ) : ParabolicShape F point (g ^ k) := by
  induction k with
  | zero => cases point <;> simp [ParabolicShape]
  | succ k ih => rw [pow_succ]; exact shape_mul F point _ _ ih hg
private theorem distinguished_pow (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (k : ℕ) :
    distinguished F point (g ^ k) = distinguished F point g ^ k := by
  induction k with
  | zero => cases point <;> simp [distinguished]
  | succ k ih => rw [pow_succ, distinguished_mul F point _ _ (shape_pow F point g hg k) hg,
      ih, pow_succ]
private theorem distinguished_ne_zero (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) : distinguished F point g ≠ 0 := by
  cases point
  · obtain ⟨h20,h21⟩ := hg
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) g.val_inv
    have hx : g.val 2 2 * g.inv 2 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three,h20,h21] using he
    exact (mul_ne_zero_iff.mp (hx ▸ one_ne_zero)).1
  · obtain ⟨h10,h20⟩ := hg
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) g.inv_val
    have hx : g.inv 0 0 * g.val 0 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three,h10,h20] using he
    exact (mul_ne_zero_iff.mp (hx ▸ one_ne_zero)).2

variable [Finite F] [CharP F 2]
omit [Finite F] [CharP F 2] in
/-- A quintic linear actor is local when the scalar group has order prime to five. -/
private theorem linear_quintic_local (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hcop : Nat.Coprime 5 (Nat.card Fˣ))
    (hp : (linearConj F g) ^ 5 = 1) :
    ∃ x : localSL F point, linearConj F g = MulAut.conj (projection F x.val) := by
  have hc : g ^ 5 ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [← linearConj_ker]
    change linearConj F (g ^ 5) = 1
    rwa [map_pow]
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c,hc⟩ := hc
  have ht : distinguished F point g ^ 5 = (c : F) := by
    rw [← distinguished_pow F point g hg, ← hc]
    cases point <;> simp [distinguished, Matrix.scalar]
  let u : Fˣ := Units.mk0 (distinguished F point g) (distinguished_ne_zero F point g hg)
  have hu : u ^ 5 = c := Units.ext ht
  have hd : GeneralLinearGroup.det g ^ 5 = c ^ 3 := by
    simpa only [map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      (congrArg GeneralLinearGroup.det hc).symm
  have hd0 : GeneralLinearGroup.det g = u ^ 3 := by
    apply hcop.symm.pow_left_bijective.injective
    have he : GeneralLinearGroup.det g ^ 5 = (u ^ 3) ^ 5 := by
      rw [hd, ← pow_mul, Nat.mul_comm 3 5, pow_mul, hu]
    exact he
  let y : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g
  have hy : GeneralLinearGroup.det y = 1 := by
    dsimp only [y]
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hd0]
    group
  let x : SL(3,F) := ⟨y.val, congrArg Units.val hy⟩
  have hx : x ∈ localSL F point := by
    cases point
    · apply (mem_lineLocalSL_iff F x).mpr
      obtain ⟨h20,h21⟩ := hg
      have hn := distinguished_ne_zero F false g ⟨h20,h21⟩
      change g.val 2 2 ≠ 0 at hn
      simp [-Matrix.coe_units_inv, -map_inv, x, y, u, distinguished, GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.diagonal_mul,h20,h21,hn]
    · apply (mem_pointLocalSL_iff F x).mpr
      obtain ⟨h10,h20⟩ := hg
      have hn := distinguished_ne_zero F true g ⟨h10,h20⟩
      change g.val 0 0 ≠ 0 at hn
      simp [-Matrix.coe_units_inv, -map_inv, x, y, u, distinguished, GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.diagonal_mul,h10,h20,hn]
  refine ⟨⟨x,hx⟩, ?_⟩
  have hxy : SpecialLinearGroup.toGL x = y := Units.ext rfl
  rw [show MulAut.conj (projection F (⟨x,hx⟩ : localSL F point).val) =
    linearConj F (SpecialLinearGroup.toGL x) from (linearConj_toGL F x).symm, hxy]
  have hz : linearConj F (GeneralLinearGroup.scalar (Fin 3) u⁻¹) = 1 := by
    change GeneralLinearGroup.scalar (Fin 3) u⁻¹ ∈ (linearConj F).ker
    rw [linearConj_ker, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u⁻¹,rfl⟩
  change linearConj F g = linearConj F (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g)
  rw [map_mul,hz,one_mul]

open Theory.GroupTheory.AutomorphismExtensionBorel
/-- On either actual local SL₂ quotient a quintic kernel actor is trivial
when the scalar group has order prime to five. -/
theorem local_quintic_kernel (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (hlinear : E ≤ linearField F)
    (point : Bool) (hcop : Nat.Coprime 5 (Nat.card Fˣ))
    (a : normalizer (localIn F E hinner point : Set E))
    (hp : a.val.val^5=1) (htrivial : localBlockAction F E hinner point a = 1) :
    a.val.val = 1 := by
  obtain ⟨c,hc⟩ := localBlockAction_semilinear F E hinner hlinear point a
  have hσ := coefficient_eq_one_of_trivial_block F E hinner hlinear point a c hc htrivial
  obtain ⟨g,hg⟩ := coefficient_factorization F ⟨a.val.val,hlinear a.val.property⟩
  rw [hσ,map_one,mul_one] at hg
  have hpres : (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point :=
    hg ▸ normalizer_preserves F E hinner point a
  obtain ⟨x,hx⟩ := linear_quintic_local F point g
    (linear_preserves_shape F point g hpres) hcop (hg ▸ hp)
  let y := localProjectEquiv F point x
  have he : a.val.val = MulAut.conj (y : PSL(3,F)) := by
    rw [show (y : PSL(3,F)) = Matrix.PSL3.projection F x.val from localProjectEquiv_val F point x]
    exact hg.trans hx
  have hz : block F point y ∈ center SL(2,F) := by
    apply mem_center_iff.mpr
    intro z
    obtain ⟨v,rfl⟩ := block_surjective F point z
    have hh := (localBlockAction_eq_iff F E hinner point a 1).mp htrivial v
    have ha : actorLocal F E hinner point a v = y*v*y⁻¹ := by
      apply Subtype.ext
      change a.val.val v = (y : PSL(3,F)) * v * (y : PSL(3,F))⁻¹
      rw [he]
      rfl
    rw [ha,map_mul,map_mul,map_inv,MulAut.one_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hycore : y ∈ pCore 2 (localFactor F point) := by
    have hh : block F point y = 1 := by
      rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hz
      exact hz
    apply (QuotientGroup.eq_one_iff y).mp
    apply (localFactorQuotientEquiv F point).injective
    exact hh.trans (map_one _).symm
  have hy5 : y^5=1 := by
    apply Subtype.ext
    apply inner_injective F
    change MulAut.conj ((y : PSL(3,F))^5) = MulAut.conj 1
    rw [map_pow,←he,hp,map_one]
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := localFactor F point)).exists_pow_pow_eq_one
    (⟨y,hycore⟩ : pCore 2 (localFactor F point))
  have hy2 : y^(2^k)=1 := congrArg Subtype.val hk
  have hy1 : y = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 5 2).pow_right k)
    (orderOf_dvd_of_pow_eq_one hy5) (orderOf_dvd_of_pow_eq_one hy2))
  rw [he,hy1]
  exact map_one _


/-- A solvable actor subgroup normalized by either local has no quintic
that preserves that local, when the scalar group is five-free. -/
theorem no_solvable_local_quintic {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (point : Bool) (hcop : Nat.Coprime 5 (Nat.card Fˣ))
    (A : Subgroup (MulAut PSL(3,F))) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, (localFactor F point).map a.toMonoidHom = localFactor F point)
    (hN : (localFactor F point).map (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) ≤
      normalizer (A : Set _))
    (a : MulAut PSL(3,F)) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  have hq : 3 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    rw [←hF] at hh
    norm_num at hh
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hq
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  let L := localFactor F point
  let e := localFactorQuotientEquiv F point
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center SL(2,F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hh
    exact hh.trans (map_one _).symm
  let aL : MulAction.stabilizer (MulAut PSL(3,F)) L := ⟨a,hfix a ha⟩
  have htr := MulAut.solvable_subgroupStabilizerCoreAction_eq_one 2 L hz A hfix hN aL ha
  have hstd : a ∈ standard F := by
    rw [Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F
      (by omega) hF (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)]
    exact mem_top _
  have hp : a^5=1 := ha5 ▸ pow_orderOf_eq_one a
  have hlin : a ∈ linearField F := SplitPrimeActors.primePower_mem_linearField
    (by decide : Odd 5) a hstd (m := 1) (by simpa using hp)
  let E := linearField F
  have hinner : MulAut.innerSubgroup PSL(3,F) ≤ E := (inner_le_innerDiagonal F).trans le_sup_left
  let aE : E := ⟨a,hlin⟩
  have hnorm : aE ∈ normalizer (localIn F E hinner point : Set E) := by
    change aE ∈ normalizer (L.map (innerEmbedding E hinner) : Set E)
    rw [←rootIn_eq_map]
    exact (mem_normalizer_rootIn_iff L E hinner (inner_injective F) aE).mpr (hfix a ha)
  let b : normalizer (localIn F E hinner point : Set E) := ⟨aE,hnorm⟩
  have hb : localBlockAction F E hinner point b = 1 := by
    apply (localBlockAction_eq_iff F E hinner point b 1).mpr
    intro x
    have hh := congrArg (fun t : MulAut (L ⧸ pCore 2 L) =>
      t (QuotientGroup.mk' (pCore 2 L) x)) htr
    change quotientAut (pCore 2 L) (MulAut.subgroupStabilizerAction L aL)
      (QuotientGroup.mk' (pCore 2 L) x) = QuotientGroup.mk' (pCore 2 L) x at hh
    rw [quotientAut_apply_mk] at hh
    exact congrArg e hh
  have he := local_quintic_kernel F E hinner le_rfl point hcop b hp hb
  change a = 1 at he
  rw [he,orderOf_one] at ha5
  omega


/-- Retain the cubic center: the actor on SL₃ is detected by its faithful
central-quotient action, and both local subgroups use their literal projections. -/
theorem no_solvable_localSL_quintic {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (point : Bool) (hcop : Nat.Coprime 5 (Nat.card Fˣ))
    (A : Subgroup (MulAut SL(3,F))) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, (localSL F point).map a.toMonoidHom = localSL F point)
    (hN : (localSL F point).map (MulAut.conj : SL(3,F) →* MulAut SL(3,F)) ≤
      normalizer (A : Set _))
    (a : MulAut SL(3,F)) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  let f := centerAction F
  let D := A.map f
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  have hlocal : (localSL F point).map (Matrix.PSL3.projection F) = localFactor F point := by
    cases point <;> rfl
  have hDfix : ∀ b ∈ D, (localFactor F point).map b.toMonoidHom = localFactor F point := by
    rintro _ ⟨b,hb,rfl⟩
    rw [←hlocal,Subgroup.map_map]
    have he : (f b).toMonoidHom.comp (Matrix.PSL3.projection F) =
        (Matrix.PSL3.projection F).comp b.toMonoidHom := by
      ext x : 1
      exact centerAction_mk F b x
    rw [he,←Subgroup.map_map,hfix b hb]
  have hND : (localFactor F point).map (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) ≤
      normalizer (D : Set _) := by
    have he : f.comp (MulAut.conj : SL(3,F) →* MulAut SL(3,F)) =
        (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)).comp (Matrix.PSL3.projection F) := by
      ext x : 1
      apply MulEquiv.ext
      intro y
      obtain ⟨y,rfl⟩ := Matrix.PSL3.projection_surjective F y
      change centerAction F (MulAut.conj x) (QuotientGroup.mk y) = _
      rw [centerAction_mk]
      change Matrix.PSL3.projection F (x*y*x⁻¹) =
        Matrix.PSL3.projection F x * Matrix.PSL3.projection F y * (Matrix.PSL3.projection F x)⁻¹
      simp only [map_mul,map_inv]
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [Subgroup.map_map,he,←Subgroup.map_map,hlocal] at hh
  exact no_solvable_local_quintic F hn hF point hcop D hDfix hND (f a)
    (mem_map_of_mem f ha)
    ((orderOf_injective f (Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective F) a).trans ha5)

private theorem residual_preserved {X : Type*} [Group X] [Finite X]
    (P : Subgroup X) (a : MulAut X) (hP : P.map a.toMonoidHom = P) :
    ((solvableResidual P).map P.subtype).map a.toMonoidHom = (solvableResidual P).map P.subtype := by
  let b : MulAut P := (a.subgroupMap P).trans (MulEquiv.subgroupCongr hP)
  have he : a.toMonoidHom.comp P.subtype = P.subtype.comp b.toMonoidHom := rfl
  rw [Subgroup.map_map,he,←Subgroup.map_map,map_solvableResidual_eq b.toMonoidHom b.surjective]

/-- A full parabolic cannot normalize a solvable quintic actor subgroup
which preserves it, unless five divides the field unit-group order. -/
theorem no_solvable_parabolic_quintic {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hcop : Nat.Coprime 5 (Nat.card Fˣ))
    (P : Subgroup SL(3,F)) (hP : P = pointParabolicSL F ∨ P = lineParabolicSL F)
    (A : Subgroup (MulAut SL(3,F))) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, P.map a.toMonoidHom = P)
    (hN : P.map (MulAut.conj : SL(3,F) →* MulAut SL(3,F)) ≤ normalizer (A : Set _))
    (a : MulAut SL(3,F)) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  rcases hP with rfl | rfl
  · have hf : ∀ b ∈ A, (localSL F true).map b.toMonoidHom = localSL F true := by
      intro b hb
      change (pointLocalSL F).map b.toMonoidHom = pointLocalSL F
      rw [←pointParabolicSL_residual F hq]
      exact residual_preserved _ b (hfix b hb)
    exact no_solvable_localSL_quintic F hn hF true hcop A hf
      ((map_mono (pointLocalSL_le F)).trans hN) a ha ha5
  · have hf : ∀ b ∈ A, (localSL F false).map b.toMonoidHom = localSL F false := by
      intro b hb
      change (lineLocalSL F).map b.toMonoidHom = lineLocalSL F
      rw [←lineParabolicSL_residual F hq]
      exact residual_preserved _ b (hfix b hb)
    exact no_solvable_localSL_quintic F hn hF false hcop A hf
      ((map_mono (lineLocalSL_le F)).trans hN) a ha ha5



omit [Finite F] [CharP F 2] in
/-- The five-free scalar condition is exactly the needed field-degree restriction. -/
theorem five_coprime_units {n : ℕ} (hF : Nat.card F = 2^n) (hn : ¬4 ∣ n) :
    Nat.Coprime 5 (Nat.card Fˣ) := by
  apply (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
  rw [Nat.card_units,hF]
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff _ 5).mpr hd
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
    pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)] at hz
  have hn0 : n%4≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have hm : n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases hm with hm | hm | hm <;> rw [hm] at hz <;> revert hz <;> decide

/-- Transport through the specified component coordinates, retaining the
same marked parabolic and actor subgroup. -/
theorem no_solvable_parabolic_quintic_of_equiv
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) (hdeg : ¬4 ∣ n)
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (P : Subgroup C)
    (hP : P.map e.toMonoidHom = pointParabolicSL F ∨ P.map e.toMonoidHom = lineParabolicSL F)
    (A : Subgroup (MulAut C)) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, P.map a.toMonoidHom = P)
    (hN : P.map (MulAut.conj : C →* MulAut C) ≤ normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  apply no_solvable_parabolic_quintic F hn hF (five_coprime_units F hF hdeg)
    (P.map e.toMonoidHom) hP D ?_ ?_
    (MulAut.congr e a) (mem_map_of_mem f ha) ((MulAut.congr e).orderOf_eq a |>.trans ha5)
  · rintro _ ⟨b,hb,rfl⟩
    have he : (f b).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp b.toMonoidHom := by
      ext x : 1
      change e (b (e.symm (e x))) = e (b x)
      rw [e.symm_apply_apply]
    rw [Subgroup.map_map,he,←Subgroup.map_map,hfix b hb]
  · have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    have he : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : SL(3,F) →* MulAut SL(3,F)).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    rwa [Subgroup.map_map,he,←Subgroup.map_map] at hh

end Matrix.PSL3.LinearThree.QuinticParabolic
