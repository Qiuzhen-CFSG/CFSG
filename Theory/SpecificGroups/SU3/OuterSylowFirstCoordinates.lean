module

public import Theory.SpecificGroups.SU3.SylowFixedInvolutions

/-!
# Outer involutions and first Hermitian coordinates on the supplied Sylow subgroup

The graph-fixed Sylow-center calculation and uniqueness of a Sylow containing an
involution align an arbitrary supplied Sylow subgroup with the literal upper
Hermitian root group.  The alignment is chosen inside the graph-fixed subgroup,
so it commutes with entrywise conjugation.  Outer involutions are first
conjugated to this graph action.  The special-unitary statement descends and
then lifts this projective calculation through the actual scalar projection.
-/

open Subgroup BenderSuzuki.External
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.OuterSylowFirstCoordinates
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def graphCoord (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  ⟨(J.conj z.val.1, J.conj z.val.2), by
    have h := congrArg J.conj z.property
    simpa only [map_add, map_mul, map_zero] using h⟩

private theorem graphCoord_val (z : hermitianUnipotentCoord J) :
    (graphCoord J z).val = (J.conj z.val.1, J.conj z.val.2) := rfl

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private theorem projective_graph_root (z : hermitianUnipotentCoord J) :
    J.projectiveGraphAut hJ (hermitianUnipotentPSU J hJ z) =
      hermitianUnipotentPSU J hJ (graphCoord J z) := by
  have hp (w : hermitianUnipotentCoord J) : hermitianUnipotentPSU J hJ w =
      J.specialToProjective (hermitianUnipotentSU J hJ w) := by
    apply Subtype.ext
    rw [hermitianUnipotentPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, J.projectiveGraphAut_specialToProjective hJ, hp]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  change (hermitianUnipotentMatrix J z).map J.conj =
    hermitianUnipotentMatrix J (graphCoord J z)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix, graphCoord]

variable [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed in
private theorem fixed_sylow_containing [CharP E 2]
    (R : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ R)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) (hfix : J.projectiveGraphAut hJ z = z) :
    ∃ S : Sylow 2 (J.projectiveGraphAut hJ).fixedSubgroup,
      (S : Subgroup _).map (J.projectiveGraphAut hJ).fixedSubgroup.subtype ≤ R ∧
      (⟨z, (MulAut.mem_fixedSubgroup _ _).mpr hfix⟩ :
        (J.projectiveGraphAut hJ).fixedSubgroup) ∈ S := by
  let zW : (J.projectiveGraphAut hJ).fixedSubgroup :=
    ⟨z, (MulAut.mem_fixedSubgroup _ _).mpr hfix⟩
  have hp : IsPGroup 2 (zpowers zW) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using
      orderOf_dvd_of_pow_eq_one (show zW ^ 2 = 1 from Subtype.ext hz2))
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := GraphFixedSylowCenters.exists_sylow_center_eq J hJ hn hcard hfixed S
  have hzQ : z ∈ Q := by
    have hm : z ∈ (center Q).map (Q : Subgroup _).subtype := by
      rw [hQ]
      exact ⟨zW, hS (mem_zpowers _), rfl⟩
    obtain ⟨x, _, rfl⟩ := hm
    exact x.property
  have he := SylowFixedInvolutions.projective_sylow_eq_of_common_involution
    J hn hJ hcard hfixed R Q z hz hzQ hne hz2
  refine ⟨S, ?_, hS (mem_zpowers _)⟩
  rw [he, ← hQ]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact y.property

include hn hcard hfixed in
private theorem graph_align [CharP E 2]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) (hfix : J.projectiveGraphAut hJ z = z) :
    ∃ w : (J.projectiveGraphAut hJ).fixedSubgroup,
      (P : Subgroup _).map (MulAut.conj w.val).toMonoidHom = rootGroup J hJ := by
  let R := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  let t : hermitianUnipotentCoord J := ⟨(0,1), by simp [CharTwo.add_self_eq_zero]⟩
  let r := hermitianUnipotentPSU J hJ t
  have hr : r ∈ R := ⟨t, rfl⟩
  have hrne : r ≠ 1 := by
    intro he
    have ht : t = 1 := EvenInner.root_injective J hJ (he.trans (map_one _).symm)
    have hh := congrArg (fun x : hermitianUnipotentCoord J => x.val.2) ht
    exact one_ne_zero hh
  have hr2 : r ^ 2 = 1 := by
    rw [← map_pow, (EvenSemilinear.square_eq_one_iff_first_zero J t).mpr rfl, map_one]
  have hrfix : J.projectiveGraphAut hJ r = r := by
    rw [projective_graph_root]
    congr 1
    exact Subtype.ext (by simp [graphCoord, t])
  obtain ⟨S₀, hS₀, _⟩ := fixed_sylow_containing J hJ hn hcard hfixed R r hr hrne hr2 hrfix
  obtain ⟨S, _, hzS⟩ := fixed_sylow_containing J hJ hn hcard hfixed P z hz hne hz2 hfix
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq (J.projectiveGraphAut hJ).fixedSubgroup S S₀
  let e := MulAut.conj w.val
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hzR : e z ∈ R := by
    apply hS₀
    let zW : (J.projectiveGraphAut hJ).fixedSubgroup :=
      ⟨z, (MulAut.mem_fixedSubgroup _ _).mpr hfix⟩
    refine ⟨MulAut.conj w zW, ?_, rfl⟩
    rw [← hw]
    exact mem_map_of_mem (MulAut.conj w).toMonoidHom hzS
  have heq := SylowFixedInvolutions.projective_sylow_eq_of_common_involution
    J hn hJ hcard hfixed Q R (e z) (mem_map_of_mem e.toMonoidHom hz) hzR
    (fun h => hne (e.injective (h.trans (map_one e).symm)))
    (by rw [← map_pow, hz2, map_one])
  exact ⟨w, congrArg Sylow.toSubgroup heq⟩

include hJ hn hcard hfixed in
/-- Coordinates on the supplied projective Sylow intertwine the outer action
with Hermitian conjugation on the first coordinate. -/
public theorem projective_first_coordinates
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, a = MulAut.conj g)
    (hstable : ∀ x, x ∈ P → a x ∈ P)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) (hfix : a z = z) :
    ∃ c : P ≃* hermitianUnipotentCoord J, ∀ x : P,
      (c ⟨a x, hstable x x.property⟩).val.1 = J.conj (c x).val.1 := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨b, hb⟩ := J.outer_involution_conjugate n hn hJ hcard hfixed
    (J.projectiveGraphAut_isEntrywiseConjugation hJ) a ha houter
  let Q := P.mapSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hbact (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      b.symm (a x) = J.projectiveGraphAut hJ (b.symm x) := by
    apply b.injective
    rw [b.apply_symm_apply]
    change a x = MulAut.congr b (J.projectiveGraphAut hJ) x
    rw [hb]
  have hbz : J.projectiveGraphAut hJ (b.symm z) = b.symm z := by
    rw [← hbact, hfix]
  obtain ⟨w, hw⟩ := graph_align J hJ hn hcard hfixed Q (b.symm z)
    (mem_map_of_mem b.symm.toMonoidHom hz)
    (fun he => hne (b.symm.injective (he.trans (map_one _).symm)))
    (by rw [← map_pow, hz2, map_one]) hbz
  let e := b.symm.trans (MulAut.conj w.val)
  have hemap : (P : Subgroup _).map e.toMonoidHom = rootGroup J hJ := by
    change (P : Subgroup _).map ((MulAut.conj w.val).toMonoidHom.comp
      b.symm.toMonoidHom) = _
    rw [← map_map]
    exact hw
  have heact (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      e (a x) = J.projectiveGraphAut hJ (e x) := by
    change w.val * b.symm (a x) * w.val⁻¹ =
      J.projectiveGraphAut hJ (w.val * b.symm x * w.val⁻¹)
    rw [map_mul, map_mul, map_inv, (MulAut.mem_fixedSubgroup _ _).mp w.property, hbact]
  let f : P ≃* rootGroup J hJ :=
    ((P : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hemap)
  let d : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
    MonoidHom.ofInjective (EvenInner.root_injective J hJ)
  let c := f.trans d.symm
  have hcoord (x : P) : hermitianUnipotentPSU J hJ (c x) = e x := by
    exact congrArg Subtype.val (d.apply_symm_apply (f x))
  refine ⟨c, fun x => ?_⟩
  have heq : c ⟨a x, hstable x x.property⟩ = graphCoord J (c x) := by
    apply EvenInner.root_injective J hJ
    rw [hcoord, ← projective_graph_root, hcoord, heact]
  exact congrArg (fun t : hermitianUnipotentCoord J => t.val.1) heq

include hn hcard hfixed in
private theorem descended_noninner
    (a : MulAut J.specialSubgroup) (houter : ¬ ∃ g, a = MulAut.conj g)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : ∀ x, b (J.specialToProjective x) = J.specialToProjective (a x)) :
    ¬ ∃ g, b = MulAut.conj g := by
  rintro ⟨g, hg⟩
  obtain ⟨y, rfl⟩ := J.specialToProjective_surjective g
  have hq : 2 < 2 ^ n := by
    change 2 ^ 1 < 2 ^ n
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  let := J.special_isPerfect_of_fixed_card hq hcard hfixed
  have he : a.toMonoidHom = (MulAut.conj y).toMonoidHom := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      J.specialToProjective J.specialToProjective_ker_le_center
    apply MonoidHom.ext
    intro x
    change J.specialToProjective (a x) = J.specialToProjective (y * x * y⁻¹)
    rw [← hb, hg, MulAut.conj_apply, map_mul, map_mul, map_inv]
  apply houter
  exact ⟨y, MulEquiv.ext (fun x => DFunLike.congr_fun he x)⟩

include hJ hn hcard hfixed in
/-- The literal scalar projection gives the same action coordinates on the
supplied special-unitary Sylow, including when the scalar kernel is nontrivial. -/
public theorem special_first_coordinates
    (P : Sylow 2 J.specialSubgroup)
    (a : MulAut J.specialSubgroup) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, a = MulAut.conj g)
    (hstable : ∀ x, x ∈ P → a x ∈ P)
    (z : J.specialSubgroup) (hz : z ∈ P)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) (hfix : a z = z) :
    ∃ c : P ≃* hermitianUnipotentCoord J, ∀ x : P,
      (c ⟨a x, hstable x x.property⟩).val.1 = J.conj (c x).val.1 := by
  obtain ⟨b, hb2, hb⟩ := SylowFixedInvolutions.special_descended_involution
    J hn hcard hfixed a ha
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hbouter := descended_noninner J hn hcard hfixed a houter b hb
  have hbstable (x) (hx : x ∈ Q) : b x ∈ Q := by
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hb]
    exact mem_map_of_mem J.specialToProjective (hstable y hy)
  have hzne : J.specialToProjective z ≠ 1 := by
    intro he
    apply hne
    apply congrArg Subtype.val (SylowOmega.specialProjection_injective_on_sylow
      J P (a₁ := ⟨z, hz⟩) (a₂ := 1) ?_)
    exact he.trans (map_one _).symm
  obtain ⟨c, hc⟩ := projective_first_coordinates J hJ hn hcard hfixed Q b hb2 hbouter
    hbstable (J.specialToProjective z) (mem_map_of_mem J.specialToProjective hz) hzne
    (by rw [← map_pow, hz2, map_one]) (by rw [hb, hfix])
  let e := SylowOmega.specialSylowEquivProjective J P
  refine ⟨e.trans c, fun x => ?_⟩
  have he : e ⟨a x, hstable x x.property⟩ =
      ⟨b (e x), hbstable (e x) (e x).property⟩ := by
    apply Subtype.ext
    rw [SylowOmega.specialSylowEquivProjective_apply]
    have he_apply : (e x : ProjectiveSpecialUnitaryMatrixGroup J) =
        J.specialToProjective x := by
      simpa [e] using (SylowOmega.specialSylowEquivProjective_apply J P x)
    calc
      J.specialToProjective (a x) = b (J.specialToProjective x) := (hb x).symm
      _ = b (e x) := congrArg b he_apply.symm
  change (c (e ⟨a x, hstable x x.property⟩)).val.1 = J.conj (c (e x)).val.1
  rw [he]
  exact hc (e x)

end BenderSuzuki.MatrixGroups.HermitianForm.OuterSylowFirstCoordinates
