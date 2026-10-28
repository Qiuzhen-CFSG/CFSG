module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointStructure
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalExtensionRecognition

/-!
# The natural quotient of the unitary point factor

A proper noncentral invariant subgroup of the Hermitian Heisenberg radical,
containing its center, has horizontal coordinates D × D for a one-dimensional
subspace D of the quadratic matrix field. A linear coordinate on F/D identifies
the remaining radical with the natural plane over the fixed field. The explicit
Levi matrices give its actual conjugation action. Descending the middle-block
map along the original surjection constructs the natural extension, hence the
SL₂ block with its full two-core as commutator module.

The companion applies this construction to K → J/O₂(J) in the proper-core
branch of 5.2.8. No embedding alternative or ambient recognition is assumed.
Source: Aschbacher–Smith 5.2.8, printed p.652 (`refs/quasithin.pdf`), with the
unitary coordinates of F.1.12(I)(6), printed pp.263–264.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Matrix BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryNatural
section Model
variable (F : Type) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "k" => FixedBy.subfield F σ
local notation "κ" => coordinatesOfRadical F σ hσ

omit [Finite F] in
private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y ∧
    (κ (a*b)).z = (κ a).z + (κ b).z + σ (κ a).y * (κ b).x +
      σ (κ a).x * (κ b).y := by
  obtain ⟨c,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact radical_mul_coordinates F σ hσ c d

private def horizontal : R →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd ((κ a).x,(κ a).y)
  map_one' := rfl
  map_mul' a b := congrArg Multiplicative.ofAdd
    (Prod.ext (coord_mul F σ hσ a b).1 (coord_mul F σ hσ a b).2.1)

omit [Finite F] in
private theorem horizontal_ker (hnt : ∃ u, σ u ≠ u) :
    (horizontal F σ hσ).ker = center R := by
  ext a
  rw [mem_center_radical_iff F σ hσ hnt]
  exact Prod.ext_iff

omit [Finite F] in
private theorem invariant_coordinates
    (N : Subgroup R) (hn : (N.map (radical F σ hσ).subtype).Normal) :
    ∃ D : Submodule k F, ∀ x y : F,
      Multiplicative.ofAdd (x,y) ∈ N.map (horizontal F σ hσ) ↔ x ∈ D ∧ y ∈ D := by
  let W := (N.map (horizontal F σ hσ)).toAddSubgroup'
  have hW (x y : F) : (x,y) ∈ W ↔ ∃ r ∈ N, (κ r).x = x ∧ (κ r).y = y := by
    change (∃ r ∈ N, horizontal F σ hσ r = Multiplicative.ofAdd (x,y)) ↔ _
    constructor
    · rintro ⟨r,hr,he⟩
      exact ⟨r,hr,congrArg (fun t => t.toAdd.1) he,congrArg (fun t => t.toAdd.2) he⟩
    · rintro ⟨r,hr,hx,hy⟩
      exact ⟨r,hr,congrArg Multiplicative.ofAdd (Prod.ext hx hy)⟩
  have hlevi (M : SpecialLinearGroup (Fin 2) k) (r : R) (hr : r ∈ N) :
      leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm M) (κ r) ∈ N := by
    have hh := hn.conj_mem r.val (mem_map_of_mem (radical F σ hσ).subtype hr) (leviSL F σ hσ M)
    have he : (leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm M) (κ r)).val =
        leviSL F σ hσ M * r.val * (leviSL F σ hσ M)⁻¹ := by
      change _ * (radicalOfCoordinates F σ hσ (κ r)).val * _ = _
      rw [show radicalOfCoordinates F σ hσ (κ r) = r from
        (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r]
      rfl
    rw [←he] at hh
    exact (mem_map_iff_mem (radical F σ hσ).subtype_injective).mp hh
  have hs (upper : Bool) (c : k) (x y : F) (h : (x,y) ∈ W) :
      (if upper then (x+c*y,y) else (x,c*x+y)) ∈ W := by
    obtain ⟨r,hr,hx,hy⟩ := (hW x y).mp h
    let M : SpecialLinearGroup (Fin 2) k :=
      ⟨if upper then !![1,c;0,1] else !![1,0;c,1],by
        cases upper <;> simp [Matrix.det_fin_two]⟩
    have hc := leviSL_conjugation_coordinates F σ hσ M (κ r)
    have hm := hlevi M r hr
    cases upper
    · exact (hW _ _).mpr ⟨_,hm,by simpa [M,hx,hy] using hc.1,
        by simpa [M,hx,hy] using hc.2.1⟩
    · exact (hW _ _).mpr ⟨_,hm,by simpa [M,hx,hy] using hc.1,
        by simpa [M,hx,hy] using hc.2.1⟩
  have hx (x y : F) (h : (x,y) ∈ W) : (y,0) ∈ W := by
    simpa using W.sub_mem (hs true 1 x y h) h
  have hy (x y : F) (h : (x,y) ∈ W) : (0,x) ∈ W := by
    simpa using W.sub_mem (hs false 1 x y h) h
  let D : Submodule k F := {
    carrier := {x | (x,0) ∈ W}
    zero_mem' := W.zero_mem
    add_mem' := fun ha hb => by simpa using W.add_mem ha hb
    smul_mem' := by
      intro c x h
      have hh := W.sub_mem (hs true c 0 x (hy x 0 h)) (hy x 0 h)
      change ((c:F)*x,0) ∈ W
      simpa using hh }
  refine ⟨D,?_⟩
  intro x y
  change (x,y) ∈ W ↔ (x,0) ∈ W ∧ (y,0) ∈ W
  constructor
  · intro h
    exact ⟨hx 0 x (hy x y h),hx x y h⟩
  · rintro ⟨hx,hy'⟩
    simpa using W.add_mem hx (hy y 0 hy')


private theorem quotient_coordinates
    (hnt : ∃ u, σ u ≠ u) (hdim : Module.finrank k F = 2)
    (N : Subgroup R) (hn : (N.map (radical F σ hσ).subtype).Normal)
    (hz : center R ≤ N) (hnz : ¬ N ≤ center R) (hntop : N ≠ ⊤) :
    ∃ t : F →ₗ[k] k, Function.Surjective t ∧
      ∀ r : R, r ∈ N ↔ t (κ r).x = 0 ∧ t (κ r).y = 0 := by
  obtain ⟨D,hD⟩ := invariant_coordinates F σ hσ N hn
  have hmem (r : R) : r ∈ N ↔ (κ r).x ∈ D ∧ (κ r).y ∈ D := by
    have he : (N.map (horizontal F σ hσ)).comap (horizontal F σ hσ) = N := by
      rw [comap_map_eq,horizontal_ker F σ hσ hnt,sup_eq_left.mpr hz]
    rw [←he]
    exact hD _ _
  have hDbot : D ≠ ⊥ := by
    intro he
    apply hnz
    intro r hr
    obtain ⟨hx,hy⟩ := (hmem r).mp hr
    rw [he] at hx hy
    exact (mem_center_radical_iff F σ hσ hnt r).mpr ⟨hx,hy⟩
  have hDtop : D ≠ ⊤ := by
    intro he
    apply hntop
    apply top_unique
    intro r _
    exact (hmem r).mpr (by simp [he])
  have hDdim : Module.finrank k D = 1 := by
    have hpos : 0 < Module.finrank k D := Module.finrank_pos_iff.mpr ((Submodule.nontrivial_iff_ne_bot).mpr hDbot)
    have hlt := Submodule.finrank_lt hDtop
    omega
  have hdq : Module.finrank k (F ⧸ D) = Module.finrank k k := by
    have hh := D.finrank_quotient_add_finrank
    rw [hDdim,hdim] at hh
    simpa using (show Module.finrank k (F ⧸ D) = 1 by omega)
  let e := LinearEquiv.ofFinrankEq (F ⧸ D) k hdq
  let t := e.toLinearMap.comp D.mkQ
  have ht (x : F) : t x = 0 ↔ x ∈ D := by
    change e (D.mkQ x) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero D
  refine ⟨t,e.surjective.comp D.mkQ_surjective,?_⟩
  intro r
  rw [ht,ht]
  exact hmem r

omit [Finite F] in
private theorem middle_ker : (middleSL F σ hσ).ker = R := by
  ext x
  change middleSL F σ hσ x = 1 ↔ x ∈ R
  rw [←quotientEquivSL_mk F σ hσ]
  rw [map_eq_one_iff _ (quotientEquivSL F σ hσ).injective,QuotientGroup.eq_one_iff]

private theorem natural_image
    (hnt : ∃ u, σ u ≠ u) (hdim : Module.finrank k F = 2)
    {X : Type*} [Group X] [Finite X] (f : L →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ R) (hz : center R ≤ f.ker.subgroupOf R)
    (hnz : ¬ f.ker.subgroupOf R ≤ center R) (hne : f.ker ≠ R)
    (hel : IsElementaryAbelian 2 ((radical F σ hσ).map f)) (hlarge : 2 < Nat.card k) :
    letI : ((radical F σ hσ).map f).Normal := Normal.map (radical_normal F σ hσ) f hf
    Nonempty (Theory.SpecificGroups.SymplecticFour.NaturalExtension
      (F := k) ((radical F σ hσ).map f)) := by
  let N := f.ker.subgroupOf R
  have hn : (N.map (radical F σ hσ).subtype).Normal := by
    rw [map_subgroupOf_eq_of_le hker]
    infer_instance
  have hNt : N ≠ ⊤ := by
    intro ht
    apply hne
    apply le_antisymm hker
    exact subgroupOf_eq_top.mp ht
  obtain ⟨t,ht,htmem⟩ := quotient_coordinates F σ hσ hnt hdim N hn hz hnz hNt
  let u : R →* Multiplicative (Fin 2 → k) := {
    toFun r := Multiplicative.ofAdd ![t (κ r).x,t (κ r).y]
    map_one' := by change ![t 0,t 0] = 0; ext i; fin_cases i <;> simp
    map_mul' r s := by
      apply Multiplicative.toAdd.injective
      change ![t (κ (r*s)).x,t (κ (r*s)).y] = _
      rw [(coord_mul F σ hσ r s).1,(coord_mul F σ hσ r s).2.1]
      ext i; fin_cases i <;> simp }
  have hu : Function.Surjective u := by
    intro v
    obtain ⟨x,hx⟩ := ht (v.toAdd 0)
    obtain ⟨y,hy⟩ := ht (v.toAdd 1)
    let c := (radicalParametersEquiv F σ hσ).symm (x,y,0)
    refine ⟨radicalOfCoordinates F σ hσ c,?_⟩
    apply Multiplicative.toAdd.injective
    apply funext
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have huk : u.ker = N := by
    ext r
    change ![t (κ r).x,t (κ r).y] = 0 ↔ r ∈ N
    rw [htmem]
    exact ⟨fun h => ⟨congrFun h 0,congrFun h 1⟩,fun h => by
      ext i; fin_cases i <;> simp [h.1,h.2]⟩
  let Q := (radical F σ hσ).map f
  let g := f.subgroupMap R
  have hg : Function.Surjective g := f.subgroupMap_surjective R
  have hgk : g.ker = N := by
    ext x
    exact Subtype.ext_iff
  let e : Q ≃* Multiplicative (Fin 2 → k) :=
    (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hgk.trans huk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective u hu))
  have heg (r : R) : e (g r) = u r := by
    change (QuotientGroup.quotientKerEquivOfSurjective u hu)
      ((QuotientGroup.quotientMulEquivOfEq (hgk.trans huk.symm))
        ((QuotientGroup.quotientKerEquivOfSurjective g hg).symm (g r))) = u r
    rw [show (QuotientGroup.quotientKerEquivOfSurjective g hg).symm (g r) =
      QuotientGroup.mk' g.ker r from
      (QuotientGroup.quotientKerEquivOfSurjective g hg).symm_apply_apply (QuotientGroup.mk' g.ker r)]
    rfl
  have hka : f.ker ≤ (middleSL F σ hσ).ker := by rwa [middle_ker F σ hσ]
  let a := f.liftOfSurjective hf ⟨middleSL F σ hσ,hka⟩
  have haf (x : L) : a (f x) = middleSL F σ hσ x := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have ha : Function.Surjective a := by
    intro M
    exact ⟨f (leviSL F σ hσ M),(haf _).trans (middleSL_leviSL F σ hσ M)⟩
  have hak : a.ker = Q := by
    ext x
    obtain ⟨l,rfl⟩ := hf x
    change a (f l) = 1 ↔ f l ∈ (radical F σ hσ).map f
    rw [haf]
    constructor
    · intro hl
      exact mem_map_of_mem f (show l ∈ R from (middle_ker F σ hσ) ▸ hl)
    · rintro ⟨r,hr,he⟩
      have hr' : middleSL F σ hσ r = 1 := by
        exact show r ∈ (middleSL F σ hσ).ker from (middle_ker F σ hσ).symm ▸ hr
      rw [←haf r,he,haf l] at hr'
      exact hr'
  let : Q.Normal := Normal.map (radical_normal F σ hσ) f hf
  let := hel
  let : Algebra (ZMod 2) k := ZMod.algebra _ _
  refine ⟨Theory.SpecificGroups.SymplecticFour.naturalExtensionOfNatural
    hel a ha hak hlarge e ?_⟩
  intro x v
  obtain ⟨l,rfl⟩ := hf x
  obtain ⟨r,rfl⟩ := hg v
  let M := middleSL F σ hσ l
  let l₀ := leviSL F σ hσ M
  have hs : l*l₀⁻¹ ∈ R := by
    rw [←middle_ker F σ hσ]
    change middleSL F σ hσ (l*l₀⁻¹) = 1
    simp [l₀,M]
  let s : R := ⟨l*l₀⁻¹,hs⟩
  let r' := leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm M) (κ r)
  have hr' : r'.val = l₀*r.val*l₀⁻¹ := by
    change l₀*(radicalOfCoordinates F σ hσ (κ r)).val*l₀⁻¹ = _
    rw [show radicalOfCoordinates F σ hσ (κ r) = r from
      (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r]
  have hex : Theory.SpecificGroups.SymplecticFour.extensionConjugate Q (f l) (g r) = g r' := by
    have hc : g (s*r'*s⁻¹) = g r' := by
      apply e.injective
      rw [heg,heg,map_mul,map_mul,map_inv,mul_comm (u s) (u r'),mul_assoc,mul_inv_cancel,mul_one]
    apply Subtype.ext
    calc
      (f l * f r.val * (f l)⁻¹) = f (s.val*r'.val*s.val⁻¹) := by
        rw [hr']
        change _ = f ((l*l₀⁻¹)*(l₀*r.val*l₀⁻¹)*(l*l₀⁻¹)⁻¹)
        simp only [_root_.mul_inv_rev,inv_inv]
        simp only [mul_assoc,inv_mul_cancel_left,map_mul,map_inv]
      _ = f r'.val := congrArg Subtype.val hc
  rw [hex,heg,heg,haf]
  have hc := leviSL_conjugation_coordinates F σ hσ M (κ r)
  change ![t (κ r').x,t (κ r').y] = M.val.mulVec ![t (κ r).x,t (κ r).y]
  rw [hc.1,hc.2.1]
  have htlin (c : k) (z : F) : t ((c:F)*z) = c*t z := t.map_smul c z
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,htlin]


end Model

/-- A proper noncentral quotient of the unitary point radical gives the actual
natural block, retaining the specified surjection and its full kernel. -/
theorem point_image_block
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (e : X ≃* ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.ProjectiveLocal m hm)
    (f : X →* Y) (hf : Function.Surjective f)
    (hN : f.ker ≤ pCore 2 X)
    (hz : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ f.ker)
    (hnz : ¬ f.ker ≤ (center (pCore 2 X)).map (pCore 2 X).subtype)
    (hne : f.ker ≠ pCore 2 X)
    (hel : IsElementaryAbelian 2 (pCore 2 Y)) :
    ChapterC.IsL2EvenBlock Y m ∧ pCore 2 Y = ChapterC.blockU Y := by
  let F := ChapterF.GreenBook.LieModels.UnitaryFour.MatrixField m
  let σ := ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj m
  let hσ := ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm
  let k := FixedBy.subfield F σ
  let P := pCore 2 X
  let R : Subgroup (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.MatrixLocal m hm) :=
    ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.Radical m hm
  let a := e.trans (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.localEquiv m hm).symm
  have hPR : P.map a.toMonoidHom = R := (pCore_map_iso 2 a).trans
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.radical_eq_twoCore m hm).symm
  let c : P ≃* R := (a.subgroupMap P).trans (MulEquiv.subgroupCongr hPR)
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  have hgR : g.ker ≤ R := by
    intro x hx
    have hh := hN (show a.symm x ∈ f.ker from hx)
    rw [←hPR]
    exact ⟨a.symm x,hh,a.apply_symm_apply x⟩
  have hgZ : center R ≤ g.ker.subgroupOf R := by
    intro r hr
    have hc := (centerCongr c.symm ⟨r,hr⟩).property
    have hh := hz (mem_map_of_mem P.subtype hc)
    exact hh
  have hgnZ : ¬ g.ker.subgroupOf R ≤ center R := by
    intro hh
    apply hnz
    intro x hx
    let p : P := ⟨x,hN hx⟩
    have hcp : c p ∈ g.ker.subgroupOf R := by
      change f (a.symm (a x)) = 1
      simpa only [a.symm_apply_apply,MonoidHom.mem_ker] using hx
    have hc := (centerCongr c.symm ⟨c p,hh hcp⟩).property
    change c.symm (c p) ∈ center P at hc
    rw [c.symm_apply_apply] at hc
    exact ⟨p,hc,rfl⟩
  have hgne : g.ker ≠ R := by
    intro hh
    apply hne
    apply le_antisymm hN
    intro x hx
    have hp := mem_map_of_mem a.toMonoidHom hx
    rw [hPR,←hh] at hp
    change f (a.symm (a x)) = 1 at hp
    simpa only [a.symm_apply_apply,MonoidHom.mem_ker] using hp
  have hpmap : P.map f = pCore 2 Y := by
    have hp := f.comap_pCore_of_ker_isPGroup hf (pCore_isPGroup.to_le hN)
    change (pCore 2 X).map f = _
    rw [←hp,map_comap_eq_self_of_surjective hf]
  have hgmap : R.map g = pCore 2 Y := by
    rw [←hpmap,←hPR,Subgroup.map_map]
    congr 1
    ext x
    exact congrArg f (a.symm_apply_apply x)
  have hdim : Module.finrank k F = 2 := by
    have hpow := Module.natCard_eq_pow_finrank (K := k) (V := F)
    have hF : Nat.card F = (2^m)^2 :=
      ChapterF.GreenBook.LieModels.UnitaryFour.matrixField_card m hm
    have hk : Nat.card k = 2^m :=
      ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fixedField_card m hm
    rw [hF,hk] at hpow
    exact Nat.pow_right_injective (by have := Nat.one_lt_two_pow (by omega : m ≠ 0); omega)
      hpow.symm
  have hk : Nat.card k = 2^m :=
    ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fixedField_card m hm
  have hlarge : 2 < Nat.card k := by
    rw [hk]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hm')
  let : (R.map g).Normal := Normal.map (radical_normal F σ hσ) g hg
  obtain ⟨d⟩ := natural_image F σ hσ
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fieldConj_nontrivial m hm)
    hdim g hg hgR hgZ hgnZ hgne (hgmap.symm ▸ hel) hlarge
  have hd : Theory.SpecificGroups.SymplecticFour.NaturalExtension (F := k) (pCore 2 Y) := by
    change Theory.SpecificGroups.SymplecticFour.NaturalExtension (F := k) (R.map g) at d
    simpa only [hgmap] using d
  exact ⟨ChapterC.isL2EvenBlock_of_naturalExtension hd hm' hk,by
    rw [ChapterC.blockU,hd.commutator_eq]⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryNatural
