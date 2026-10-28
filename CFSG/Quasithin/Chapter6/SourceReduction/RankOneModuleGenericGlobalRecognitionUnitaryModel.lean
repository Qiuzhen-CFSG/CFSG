module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointStructure

/-!
# Frattini geometry of the actual unitary-four point parabolic

The Heisenberg radical modulo its center has the literal horizontal
coordinates F × F. Opposite fixed-field Levi shears isolate either
coordinate. The diagonal matrix diag(a,a⁻¹,σ(a),σ(a)⁻¹) then scales the
second coordinate by σ(a)², which ranges through every nonzero field
element. Thus a parabolic-invariant horizontal subgroup is zero or full.
Since the radical center is its Frattini subgroup, nongeneration lifts
this dichotomy to the radical itself. That center centralizes the vector
stabilizer, which contains the parabolic solvable residual.

The result is transported through the actual faithful projective map.
It supplies the U₄ model comparison in 5.2.6; the adjacent source extension
applies it to the exact residual-core intersection of the selected diagram
factor. This is a local exclusion, not an amalgam classification.

Source: Aschbacher–Smith, 5.2.6, printed p.651, and F.1.12(I)(6),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFrattini
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

private def diagonalActor (a : Fˣ) : P := by
  let d : Fin 4 → F := ![(a:F), (a:F)⁻¹, σ a, (σ a)⁻¹]
  have hd : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp [d, Fin.prod_univ_succ]
  let g : SU F (form F σ hσ) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (form F σ hσ).conjTranspose (Matrix.diagonal d) * gram F *
          Matrix.diagonal d = gram F
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_succ, d, hσ (a:F)],
      Units.ext hd⟩
  exact ⟨g,(mem_pointParabolicSU F _ g).mpr ⟨rfl,rfl,rfl⟩⟩

omit [CharP F 2] in
private theorem torus_val (a : Fˣ) : (diagonalActor F σ hσ a).val.val.val =
    Matrix.diagonal ![(a:F), (a:F)⁻¹, σ a, (σ a)⁻¹] := rfl

omit [Finite F] in
private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact ⟨(radical_mul_coordinates F σ hσ c d).1,
    (radical_mul_coordinates F σ hσ c d).2.1⟩

private def horizontal : R →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd ((κ a).x, (κ a).y)
  map_one' := rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext (coord_mul F σ hσ a b).1 (coord_mul F σ hσ a b).2

omit [Finite F] in
private theorem horizontal_surjective : Function.Surjective (horizontal F σ hσ) := by
  rintro ⟨x,y⟩
  exact ⟨radicalOfCoordinates F σ hσ ⟨x,y,x*σ y,by simp only [map_mul,hσ y]; ring⟩,rfl⟩

omit [Finite F] in
private theorem horizontal_ker (hnt : ∃ u, σ u ≠ u) :
    (horizontal F σ hσ).ker = center R := by
  ext a
  rw [mem_center_radical_iff F σ hσ hnt]
  change (Multiplicative.ofAdd ((κ a).x, (κ a).y) : Multiplicative (F × F)) = 1 ↔ _
  exact Prod.ext_iff

private def torusCoordinates (a : Fˣ) (c : RadicalCoordinates F σ) : RadicalCoordinates F σ :=
  ⟨σ a / a * c.x, σ a ^ 2 * c.y, (a:F) * σ a * c.z, by
    have ha := a.ne_zero
    have hsa : σ (a:F) ≠ 0 := (map_ne_zero σ).mpr ha
    simp only [map_mul, map_div₀, map_pow, hσ (a:F)]
    field_simp
    exact c.trace_eq⟩

private theorem torus_conjugate (a : Fˣ) (c : RadicalCoordinates F σ) :
    (diagonalActor F σ hσ a).val * (radicalOfCoordinates F σ hσ c).val.val *
      (diagonalActor F σ hσ a).val⁻¹ =
        (radicalOfCoordinates F σ hσ (torusCoordinates F σ hσ a c)).val.val := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change (diagonalActor F σ hσ a).val.val.val * radicalMatrix F σ c =
    radicalMatrix F σ (torusCoordinates F σ hσ a c) * (diagonalActor F σ hσ a).val.val.val
  rw [torus_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, radicalMatrix, torusCoordinates,
      hσ (a:F)] <;> field_simp

omit [Finite F] in
private theorem center_radical_central (hnt : ∃ u, σ u ≠ u) :
    (center R).map (radical F σ hσ).subtype ≤ center L := by
  rintro x ⟨r,hr,rfl⟩
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hr
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmat : r.val.val.val.val = radicalMatrix F σ (κ r) := by
    exact congrArg (fun x : R => x.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
  have hg := (mem_localSU F _ g.val).mp g.property
  have hl := last_row F σ hσ g.val g.property
  change g.val.val.val * r.val.val.val.val = r.val.val.val.val * g.val.val.val
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, hx,hy, Matrix.mul_apply, Fin.sum_univ_succ,
      hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]

private theorem horizontal_invariant_dichotomy
    (W : AddSubgroup (F × F))
    (hu : ∀ x y, (x,y) ∈ W → (x+y,y) ∈ W)
    (hl : ∀ x y, (x,y) ∈ W → (x,x+y) ∈ W)
    (ht : ∀ (a : Fˣ) x y, (x,y) ∈ W → (σ a / a * x, σ a ^ 2 * y) ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hx (x y : F) (h : (x,y) ∈ W) : (y,0) ∈ W := by
    simpa only [Prod.sub_def, add_sub_cancel_left, sub_self] using W.sub_mem (hu x y h) h
  have hy (x y : F) (h : (x,y) ∈ W) : (0,x) ∈ W := by
    simpa only [Prod.sub_def, add_sub_cancel_right, sub_self] using W.sub_mem (hl x y h) h
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨x,y⟩,hxy,hne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hW)
  have hex : ∃ z : F, z ≠ 0 ∧ (0,z) ∈ W := by
    by_cases hxx : x = 0
    · refine ⟨y,?_,?_⟩
      · intro hyy
        exact hne (by simp [hxx,hyy])
      · simpa [hxx] using hxy
    · exact ⟨x,hxx,hy x y hxy⟩
  obtain ⟨z,hz,hw⟩ := hex
  have hall (t : F) : (0,t) ∈ W := by
    by_cases ht0 : t = 0
    · subst t
      exact W.zero_mem
    obtain ⟨b,hb⟩ := (frobeniusEquiv F 2).surjective (t / z)
    have hb' : b ^ 2 = t / z := hb
    have hb0 : b ≠ 0 := by
      intro he
      exact (div_ne_zero ht0 hz) (by simpa only [he,zero_pow (by decide : 2 ≠ 0)] using hb'.symm)
    let a : Fˣ := Units.mk0 (σ.symm b) ((map_ne_zero σ.symm).mpr hb0)
    have hsa : σ (a:F) = b := σ.apply_symm_apply b
    have h := ht a 0 z hw
    simpa only [hsa, mul_zero,hb',div_mul_cancel₀ _ hz] using h
  apply top_unique
  rintro ⟨u,v⟩ _
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    W.add_mem (hx 0 u (hall u)) (hall v)

private theorem normalized_radical_dichotomy
    (hnt : ∃ u, σ u ≠ u) (hR : IsPGroup 2 R)
    (N : Subgroup R)
    (hN : P ≤ normalizer (N.map ((localSU F (form F σ hσ)).subtype.comp
      (radical F σ hσ).subtype) : Set (SU F (form F σ hσ)))) :
    N ≤ center R ∨ N = ⊤ := by
  let j : R →* SU F (form F σ hσ) :=
    (localSU F (form F σ hσ)).subtype.comp (radical F σ hσ).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hconj (g : P) (r : R) (hr : r ∈ N) (s : R)
      (he : j s = g.val * j r * g.val⁻¹) : s ∈ N := by
    have hh := (mem_normalizer_iff.mp (hN g.property) (j r)).mp (mem_map_of_mem j hr)
    rw [←he] at hh
    obtain ⟨t,ht,heq⟩ := hh
    exact hj heq ▸ ht
  let W := (N.map (horizontal F σ hσ)).toAddSubgroup'
  have hW (x y : F) : (x,y) ∈ W ↔ ∃ r ∈ N, (κ r).x = x ∧ (κ r).y = y := by
    change (∃ r ∈ N, horizontal F σ hσ r = Multiplicative.ofAdd (x,y)) ↔ _
    constructor
    · rintro ⟨r,hr,he⟩
      exact ⟨r,hr,congrArg (fun t => t.toAdd.1) he,congrArg (fun t => t.toAdd.2) he⟩
    · rintro ⟨r,hr,hx,hy⟩
      exact ⟨r,hr,congrArg Multiplicative.ofAdd (Prod.ext hx hy)⟩
  have hlevi (M : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ))
      (r : R) (hr : r ∈ N) :
      leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm M) (κ r) ∈ N := by
    apply hconj ⟨(leviSL F σ hσ M).val,
      localSU_le_pointParabolicSU F _ (leviSL F σ hσ M).property⟩ r hr
    change _ * (radicalOfCoordinates F σ hσ (κ r)).val.val * _ = _
    rw [show radicalOfCoordinates F σ hσ (κ r) = r from
      (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r]
    rfl
  have hs (upper : Bool) (x y : F) (h : (x,y) ∈ W) :
      (if upper then (x+y,y) else (x,x+y)) ∈ W := by
    obtain ⟨r,hr,hx,hy⟩ := (hW x y).mp h
    let M : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
      ⟨if upper then !![1,1;0,1] else !![1,0;1,1],by
        cases upper <;> simp [Matrix.det_fin_two]⟩
    have hc := leviSL_conjugation_coordinates F σ hσ M (κ r)
    have hm := hlevi M r hr
    cases upper
    · apply (hW x (x+y)).mpr
      exact ⟨_,hm,by simpa [M,hx,hy] using hc.1,by simpa [M,hx,hy] using hc.2.1⟩
    · apply (hW (x+y) y).mpr
      exact ⟨_,hm,by simpa [M,hx,hy] using hc.1,by simpa [M,hx,hy] using hc.2.1⟩
  have ht (a : Fˣ) (x y : F) (h : (x,y) ∈ W) :
      (σ a / a * x, σ a ^ 2 * y) ∈ W := by
    obtain ⟨r,hr,hx,hy⟩ := (hW x y).mp h
    let c := torusCoordinates F σ hσ a (κ r)
    have hm : radicalOfCoordinates F σ hσ c ∈ N := by
      apply hconj (diagonalActor F σ hσ a) r hr
      change (radicalOfCoordinates F σ hσ (torusCoordinates F σ hσ a (κ r))).val.val = _
      rw [←torus_conjugate]
      rw [show radicalOfCoordinates F σ hσ (κ r) = r from
        (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r]
      rfl
    exact (hW _ _).mpr ⟨_,hm,by change σ a / a * (κ r).x = _; rw [hx],
      by change σ a ^ 2 * (κ r).y = _; rw [hy]⟩
  rcases horizontal_invariant_dichotomy F σ W (hs true) (hs false) ht with hb | ht
  · left
    rw [←horizontal_ker F σ hσ hnt]
    intro r hr
    have hm : ((κ r).x,(κ r).y) ∈ W := (hW _ _).mpr ⟨r,hr,rfl,rfl⟩
    rw [hb] at hm
    exact congrArg Multiplicative.ofAdd hm
  · right
    apply frattini_nongenerating
    rw [frattini_radical_eq_center F σ hσ hnt hR,←horizontal_ker F σ hσ hnt,
      ←comap_map_eq]
    have hm : N.map (horizontal F σ hσ) = ⊤ := by
      exact Subgroup.toAddSubgroup'.injective ht
    rw [hm,comap_top]

open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

/-- A normal subgroup of the point-parabolic two-core either centralizes
its solvable residual or is the entire core. This is the concrete Frattini
irreducibility argument, including the binary fixed field. -/
theorem matrix_point_core_dichotomy (n : ℕ) (hn : 1 ≤ n)
    (N : Subgroup (pointParabolicMatrix n hn)) [N.Normal]
    (hN : N ≤ pCore 2 (pointParabolicMatrix n hn)) :
    ⁅N,solvableResidual (pointParabolicMatrix n hn)⁆ = ⊥ ∨
      N = pCore 2 (pointParabolicMatrix n hn) := by
  let fld := MatrixField n
  let sig := fieldConj n
  let invol := fieldConj_involutive n hn
  let par := pointParabolicMatrix n hn
  let loc := PointLocal.MatrixLocal n hn
  let rad := PointLocal.Radical n hn
  let j : rad →* MatrixGroup n hn := loc.subtype.comp rad.subtype
  have hj : Function.Injective j := loc.subtype_injective.comp rad.subtype_injective
  let N0 := N.map par.subtype
  let N1 := N0.comap j
  have hrange : j.range = rad.map loc.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hNr : N0 ≤ j.range := by
    rw [hrange,←PointLocal.pointParabolicMatrix_twoCore n hn]
    exact map_mono hN
  have hm : N1.map j = N0 := by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hNr]
  have hn0 : par ≤ normalizer (N0 : Set (MatrixGroup n hn)) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map par.subtype
  have hnorm : par ≤ normalizer (N1.map j : Set (MatrixGroup n hn)) := by rwa [hm]
  have hh : N1 ≤ center rad ∨ N1 = ⊤ :=
    normalized_radical_dichotomy fld sig invol (PointLocal.fieldConj_nontrivial n hn)
      (PointLocal.radical_isTwoGroup n hn) N1 hnorm
  rcases hh with hc | he
  · left
    have hcent : N0 ≤ centralizer (loc : Set (MatrixGroup n hn)) := by
      rw [←hm]
      rintro x ⟨r,hr,rfl⟩
      have hz := center_radical_central fld sig invol (PointLocal.fieldConj_nontrivial n hn)
        (mem_map_of_mem rad.subtype (hc hr))
      rw [mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
    have hres : (solvableResidual par).map par.subtype ≤ loc :=
      UnitaryFourPointResidual.pointParabolic_solvableResidual_le fld (standardForm n hn)
    apply Subgroup.map_injective par.subtype_injective
    rw [map_commutator,Subgroup.map_bot]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hcent.trans (centralizer_le hres))
  · right
    have he0 : N0 = rad.map loc.subtype := by
      rw [←hm,he,←MonoidHom.range_eq_map,hrange]
    apply Subgroup.map_injective par.subtype_injective
    exact he0.trans (PointLocal.pointParabolicMatrix_twoCore n hn).symm

private theorem core_dichotomy_transport
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : ∀ N : Subgroup X, N.Normal → N ≤ pCore 2 X →
      ⁅N,solvableResidual X⁆ = ⊥ ∨ N = pCore 2 X)
    (N : Subgroup Y) [N.Normal] (hN : N ≤ pCore 2 Y) :
    ⁅N,solvableResidual Y⁆ = ⊥ ∨ N = pCore 2 Y := by
  let D := N.map e.symm.toMonoidHom
  let : D.Normal := Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  have heD : D.map e.toMonoidHom = N := by
    rw [Subgroup.map_map]
    simp
  have hD : D ≤ pCore 2 X := by
    rw [←pCore_map_iso 2 e.symm]
    exact map_mono hN
  rcases h D inferInstance hD with hc | ht
  · left
    rw [←heD,←map_solvableResidual_eq e.toMonoidHom e.surjective,←map_commutator,hc,Subgroup.map_bot]
  · right
    rw [←heD,ht,pCore_map_iso]

/-- The same Frattini dichotomy in the literal projective point parabolic.
The projective map is faithful in dimension four and characteristic two. -/
theorem projective_point_core_dichotomy (n : ℕ) (hn : 1 ≤ n)
    (N : Subgroup (pointParabolic n hn)) [N.Normal]
    (hN : N ≤ pCore 2 (pointParabolic n hn)) :
    ⁅N,solvableResidual (pointParabolic n hn)⁆ = ⊥ ∨
      N = pCore 2 (pointParabolic n hn) := by
  let e : pointParabolicMatrix n hn ≃* pointParabolic n hn :=
    (pointParabolicMatrix n hn).equivMapOfInjective (projection n hn)
      (projection_injective n hn)
  let : Finite (pointParabolic n hn) := Finite.of_equiv _ e.toEquiv
  apply core_dichotomy_transport e (fun D hD hle => ?_) N hN
  let := hD
  exact matrix_point_core_dichotomy n hn D hle

/-- Transport of the proved model dichotomy along an actual parabolic
isomorphism; no quotient or module action is supplied as an extra premise. -/
theorem point_core_dichotomy_of_equiv
    {X : Type*} [Group X] [Finite X] (n : ℕ) (hn : 1 ≤ n)
    (e : X ≃* pointParabolic n hn) (N : Subgroup X) [N.Normal]
    (hN : N ≤ pCore 2 X) :
    ⁅N,solvableResidual X⁆ = ⊥ ∨ N = pCore 2 X := by
  let : Finite (pointParabolic n hn) := Finite.of_equiv X e.toEquiv
  apply core_dichotomy_transport e.symm (fun D hD hle => ?_) N hN
  let := hD
  exact projective_point_core_dichotomy n hn D hle

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFrattini
