module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryIntersection
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order

/-!
# Proper unitary core intersections and the Mathieu exclusion

For K = O²(H), Q = O₂(K), R = O₂(J), the previous intersection calculation
places Z(Q) inside N = K ∩ R. When Q is not contained in R, N is a proper
noncentral K-invariant subgroup of Q. In the actual Hermitian Heisenberg
coordinates, the opposite fixed-field Levi shears force its horizontal image
to be D × D for a fixed-field subspace D of the quadratic matrix field.
Noncentrality and properness force dim(D) = 1. The Heisenberg law then makes
N elementary of order q³. The literal quotient map K → J/O₂(J) has kernel N,
so its image has two-core of order q² and |R| ≤ 2q³.

For q = 4, characteristic two gives a faithful action of J/O₂(J) on
R/Φ(R), of dimension at most seven. The orders of these binary general
linear groups are prime to eleven, excluding the actual M₂₂, triple-cover
M₂₂ and M₂₃ quotient models in the source shortlist. The companion applies
all these conclusions to the literal Chapter12 pair, retaining both unitary
orientations and the degree-two extension.

The case Q ≤ R with Q nonnormal, the complete embedding selection and the
second-parabolic contradiction remain open. The argument does not assert
unitary maximality, exhaustive amalgam comparison or ambient recognition.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryConstituent
section Model
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
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

private theorem normalized_proper_radical
    (hnt : ∃ u, σ u ≠ u) (hdim : Module.finrank k F = 2)
    (N : Subgroup R) (hn : (N.map (radical F σ hσ).subtype).Normal)
    (hz : center R ≤ N) (hnz : ¬ N ≤ center R) (hntop : N ≠ ⊤) :
    IsElementaryAbelian 2 N ∧ Nat.card N = Nat.card k ^ 3 := by
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
  obtain ⟨a,ha,ha0⟩ := D.ne_bot_iff.mp hDbot
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hDdim ha ha0
  have scalar (x : F) (hx : x ∈ D) : ∃ c : k, (c:F)*a = x := by
    rw [hspan] at hx
    exact Submodule.mem_span_singleton.mp hx
  have hsq (r : N) : r^2 = 1 := by
    obtain ⟨hx,hy⟩ := (hmem r.val).mp r.property
    obtain ⟨c,hc⟩ := scalar _ hx
    obtain ⟨d,hd⟩ := scalar _ hy
    apply Subtype.ext
    apply (radicalCoordinatesEquiv F σ hσ).symm.injective
    change κ (r.val^2) = κ 1
    have hp := coord_mul F σ hσ r.val r.val
    rw [pow_two]
    have hxx : (κ (r.val*r.val)).x = 0 := by rw [hp.1,CharTwo.add_self_eq_zero]
    have hyy : (κ (r.val*r.val)).y = 0 := by rw [hp.2.1,CharTwo.add_self_eq_zero]
    have hzz : (κ (r.val*r.val)).z = 0 := by
      rw [hp.2.2,CharTwo.add_self_eq_zero,zero_add,←hc,←hd,map_mul,map_mul]
      rw [show σ (c:F) = c from c.property,show σ (d:F) = d from d.property]
      ring_nf
      simp [CharTwo.two_eq_zero]
    cases hec : κ (r.val*r.val) with
    | mk x y z ht =>
      simp only [hec] at hxx hyy hzz
      subst x; subst y; subst z
      rfl
  have hinv (r : N) : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq r)
  have helem : IsElementaryAbelian 2 N := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun r s => by
      have hh := mul_inv_rev r s
      simpa only [hinv] using hh)
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }
  let e₀ := (radicalCoordinatesEquiv F σ hσ).symm.trans (radicalParametersEquiv F σ hσ)
  let e : N ≃ D × D × k := {
    toFun r := (⟨(e₀ r.val).1,((hmem r.val).mp r.property).1⟩,
      ⟨(e₀ r.val).2.1,((hmem r.val).mp r.property).2⟩,(e₀ r.val).2.2)
    invFun p := ⟨e₀.symm (p.1.val,p.2.1.val,p.2.2),(hmem _).mpr ⟨p.1.property,p.2.1.property⟩⟩
    left_inv r := by
      apply Subtype.ext
      exact e₀.symm_apply_apply r.val
    right_inv p := by
      have he := e₀.apply_symm_apply (p.1.val,p.2.1.val,p.2.2)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) he))
          (congrArg (fun z => z.2.2) he) }
  refine ⟨helem,?_⟩
  rw [Nat.card_congr e,Nat.card_prod,Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := k) (V := D),hDdim,pow_one]
  ring

end Model

private theorem point_core_constituent
    {X : Type*} [Group X] [Finite X] (m : ℕ) (hm : 1 ≤ m)
    (e : X ≃* ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.ProjectiveLocal m hm)
    (N : Subgroup X) [N.Normal] (hN : N ≤ pCore 2 X)
    (hz : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ N)
    (hnz : ¬ N ≤ (center (pCore 2 X)).map (pCore 2 X).subtype)
    (hne : N ≠ pCore 2 X) : IsElementaryAbelian 2 N ∧ Nat.card N = (2^m)^3 := by
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
  let U := N.subgroupOf P
  let D := U.map c.toMonoidHom
  have hmap : D.map R.subtype = N.map a.toMonoidHom := by
    rw [Subgroup.map_map]
    change U.map (a.toMonoidHom.comp P.subtype) = _
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hN]
  have hnorm : (D.map R.subtype).Normal := by
    rw [hmap]
    exact Normal.map inferInstance a.toMonoidHom a.surjective
  have hZU : center P ≤ U := fun x hx => hz ⟨x,hx,rfl⟩
  have hZD : center R ≤ D := by
    rw [←center_map_equiv c]
    exact map_mono hZU
  have hnzc : ¬ D ≤ center R := by
    intro hh
    have hUZ : U ≤ center P := (map_le_map_iff_of_injective c.injective).mp
      (hh.trans_eq (center_map_equiv c).symm)
    apply hnz
    rw [←map_subgroupOf_eq_of_le hN]
    exact map_mono hUZ
  have hDt : D ≠ ⊤ := by
    intro hh
    have hUt : U = ⊤ := (Subgroup.map_injective c.injective)
      (hh.trans (Subgroup.map_equiv_top c).symm)
    apply hne
    rw [←map_subgroupOf_eq_of_le hN]
    change U.map P.subtype = P
    rw [hUt,←MonoidHom.range_eq_map,range_subtype]
  have hdim : Module.finrank k F = 2 := by
    have hpow := Module.natCard_eq_pow_finrank (K := k) (V := F)
    have hF : Nat.card F = (2^m)^2 :=
      ChapterF.GreenBook.LieModels.UnitaryFour.matrixField_card m hm
    have hk : Nat.card k = 2^m :=
      ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fixedField_card m hm
    rw [hF,hk] at hpow
    exact Nat.pow_right_injective (by have := Nat.one_lt_two_pow (by omega : m ≠ 0); omega)
      hpow.symm
  obtain ⟨hDe,hDc⟩ := normalized_proper_radical F σ hσ
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fieldConj_nontrivial m hm)
    hdim D hnorm hZD hnzc hDt
  let b : N ≃* D := (subgroupOfEquivOfLe hN).symm.trans
    (U.equivMapOfInjective c.toMonoidHom c.injective)
  let : IsElementaryAbelian 2 D := hDe
  refine ⟨IsElementaryAbelian.of_injective b.toMonoidHom b.injective,?_⟩
  exact (Nat.card_congr b.toEquiv).trans (hDc.trans (congrArg (fun t : ℕ => t^3)
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fixedField_card m hm)))


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryConstituent

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- If the original unitary core is not contained in the overcomponent core,
their intersection is elementary of order q³. This is the natural-constituent
calculation for the actual source subgroups, in both unitary orientations. -/
theorem Preparation.unitary_overcomponent_proper_intersection
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    IsElementaryAbelian 2 (residual H ⊓ J.pCoreIn 2 : Subgroup G) ∧
      Nat.card (residual H ⊓ J.pCoreIn 2 : Subgroup G) = (2^m)^3 := by
  let K := residual H
  let P := pCore 2 K
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let N := R.subgroupOf K
  obtain ⟨_,hNQ,hnot,_,hZN,_⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ
  obtain ⟨_,_,_,_,_,_,_,_,_,hZK⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  have hN : N ≤ P := fun x hx => (mem_map_iff_mem K.subtype_injective).mp
    (hNQ ⟨x.property,hx⟩)
  have hn : N.Normal := normal_subgroupOf_of_le_normalizer
    (hKJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  let := hn
  have hZ : ((center P).map P.subtype).map K.subtype = (center Q).map Q.subtype :=
    map_embeddedCenter P K.subtype K.subtype_injective
  have hz : (center P).map P.subtype ≤ N := by
    intro x hx
    exact (hZN (hZ ▸ mem_map_of_mem K.subtype hx)).2
  have hnz : ¬ N ≤ (center P).map P.subtype := by
    intro hh
    apply hnot
    intro x hx
    have hxc := hZK (hh (show (⟨x,hx.1⟩ : K) ∈ N from hx.2))
    exact mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hy⟩))
  have hne : N ≠ P := by
    intro hh
    apply hQR
    rintro x ⟨u,hu,rfl⟩
    change u ∈ N
    rwa [hh]
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨e⟩ := hf.2.2.2.1
  obtain ⟨hNe,hNc⟩ := UnitaryConstituent.point_core_constituent m hm e N hN hz hnz hne
  let b : N ≃* (K ⊓ R : Subgroup G) :=
    (N.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr ((subgroupOf_map_subtype R K).trans (inf_comm R K)))
  let := hNe
  exact ⟨IsElementaryAbelian.of_injective b.symm.toMonoidHom b.symm.injective,
    (Nat.card_congr b.symm.toEquiv).trans hNc⟩

/-- The literal image in J/O₂(J) has two-core of order q² when the
original unitary core is not contained in O₂(J). The overcomponent core
has order at most 2q³, including the degree-two extension. -/
theorem Preparation.unitary_overcomponent_proper_quotient_core
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
    Nat.card (pCore 2 f.range) = (2^m)^2 ∧ Nat.card (J.pCoreIn 2) ≤ 2*(2^m)^3 := by
  let K := residual H
  let P := pCore 2 K
  let R := J.pCoreIn 2
  let N := R.subgroupOf K
  let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
  obtain ⟨_,hNcard⟩ := d.unitary_overcomponent_proper_intersection h hH hp m hm he hJ hKJ hQR
  obtain ⟨_,hNQ,_,_,_,hidx⟩ := d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ
  obtain ⟨hk,hmap,_,_,_⟩ := d.unitary_overcomponent_quotient_image h hH hp m hm he hJ hKJ
  have hNP : N ≤ P := fun x hx => (mem_map_iff_mem K.subtype_injective).mp
    (hNQ ⟨x.property,hx⟩)
  let b : N ≃* (K ⊓ R : Subgroup G) :=
    (N.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr ((subgroupOf_map_subtype R K).trans (inf_comm R K)))
  have hcN : Nat.card N = (2^m)^3 := (Nat.card_congr b.toEquiv).trans hNcard
  let g := f.subgroupMap P
  have hkg : g.ker = N.subgroupOf P := by
    ext x
    change g x = 1 ↔ x.val ∈ N
    have hh : g x = 1 ↔ f x.val = 1 := Subtype.ext_iff
    rw [hh]
    exact show x.val ∈ f.ker ↔ x.val ∈ N from by rw [hk]
  have hcKer : Nat.card g.ker = (2^m)^3 := by
    rw [hkg,Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv,hcN]
  have hcP : Nat.card P = (2^m)^5 := (d.unitary_core_structure h hH.1.1.2 hp m hm he).2.2.2.2.1
  have hcMap : Nat.card (P.map f) = Nat.card (pCore 2 f.range) := by
    rw [hmap]
    exact Nat.card_congr ((pCore 2 f.range).equivMapOfInjective
      f.range.subtype f.range.subtype_injective).symm.toEquiv
  have hprod : (2^m)^3 * Nat.card (pCore 2 f.range) = (2^m)^5 := by
    have hh := g.ker.card_mul_index
    rw [hcKer,index_ker,MonoidHom.range_eq_top.mpr (f.subgroupMap_surjective P),
      Nat.card_congr (topEquiv (G := P.map f)).toEquiv,hcMap,hcP] at hh
    exact hh
  refine ⟨?_,?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2^m)^3)
    exact hprod.trans (by rw [←pow_add])
  · have hh := (K ⊓ R).subgroupOf R |>.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show K ⊓ R ≤ R from inf_le_right)).toEquiv,
      hNcard] at hh
    change (2^m)^3 * (K ⊓ R).relIndex R = Nat.card R at hh
    rw [←hh]
    simpa [mul_comm] using Nat.mul_le_mul_left ((2^m)^3) hidx

omit d h hH hp m hm he in
private theorem quotient_eleven_free_of_small_core
    {X : Type*} [Group X] [Finite X] (h : HasCharacteristicTwo X)
    (hc : Nat.card (pCore 2 X) ≤ 2^7) : ¬ 11 ∣ Nat.card (X ⧸ pCore 2 X) := by
  let P := pCore 2 X
  let E := P ⧸ frattini P
  let a := (quotientAut (frattini P)).comp (MulAut.conjNormal : X →* MulAut P)
  have hk : a.ker = P := pCore_frattini_action_kernel 2 h
  let f := QuotientGroup.lift P a hk.ge
  have hf : Function.Injective f := (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  let : Fact (IsPGroup 2 P) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hb : r ≤ 7 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
    rw [←hr]
    exact (Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini P))
      (QuotientGroup.mk'_surjective _)).trans hc)
  have hd := card_dvd_of_injective f hf
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E r hr] at hd
  intro h11
  have hh := h11.trans hd
  interval_cases r <;> norm_num [Fin.prod_univ_succ] at hh

/-- In the field-four noncontainment branch, no factor of eleven occurs in
the actual overcomponent quotient. The faithful action is on its own core's
Frattini quotient, of dimension at most seven. This excludes the three
Mathieu embedding alternatives in the source's unitary argument. -/
theorem Preparation.unitary_four_proper_quotient_eleven_free
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) (hm2 : m = 2) :
    ¬ 11 ∣ Nat.card (J ⧸ pCore 2 J) := by
  have hc := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ hQR).2
  have hci : Nat.card (pCore 2 J) = Nat.card (J.pCoreIn 2) :=
    Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo
    T (h.qtke.evenCharacteristic T) hJ
  apply quotient_eleven_free_of_small_core hchar
  rw [hci]
  simpa only [hm2,Nat.reducePow,Nat.reduceMul] using hc


/-- None of the three Mathieu overcomponent quotients in the field-four
embedding shortlist occurs for the actual proper unitary intersection. -/
theorem Preparation.unitary_four_proper_quotient_not_mathieu
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) (hm2 : m = 2) :
    ¬ (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) ∨
      Chapter1.Section02.LocalModels.IsM22Cover (J ⧸ pCore 2 J) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)) := by
  have h11 := d.unitary_four_proper_quotient_eleven_free h hH hp m hm he hJ hKJ hQR hm2
  intro hmodel
  rcases hmodel with he22 | hcover | he23
  · obtain ⟨e⟩ := he22
    apply h11
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num
  · obtain ⟨e⟩ := hcover.2.2
    have hd := (center (J ⧸ pCore 2 J)).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order] at hd
    exact h11 ((by norm_num : 11 ∣ 443520).trans hd)
  · obtain ⟨e⟩ := he23
    apply h11
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num


end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
