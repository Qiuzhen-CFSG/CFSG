module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.QuotientRank
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.SelectionGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Intersection
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Borel
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.BinaryG2Exclusion

/-!
# Direct geometry for the ordinary even-model exclusions

The original residual and literal Sylow marking put a rank-two solvable
subgroup inside every component identified with the cubic residual of I.
The marked involution fixes that subgroup. The minimal escape gives the
maximal intersection needed to force pointwise fixation of a component Borel.
All claims use ResidualInput, without a partner residual identity.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
variable (hcard : Nat.card (centralInvolutions T) = 2)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include r hcard

/-- The original central involution fixes a Sylow of the actual component. -/
theorem marked_component_twoCentral
    (_hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : TwoCentralInner a := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal c.component c.isComponent.1
  refine ⟨hi,marked_component_action_order_two c (r.marked_centralizer_of_seed_card hcard hz hzne).1 hz hzne a ha,Q,?_⟩
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rw [ha]
  have hxP : (x.val : I) ∈ P := by
    have hh : x.val ∈ (Q : Subgroup c.component) := x.property
    rw [hQ] at hh
    exact hh
  have hxT : ((x.val : I) : G) ∈ (T : Subgroup G) :=
    (show planeSylow T ⁅V,B⁆ ≤ (T : Subgroup G) from inf_le_left)
      (hP ▸ mem_map_of_mem I.subtype hxP)
  have hc := centralInvolutions_le_centralizer_sylow T hz _ hxT
  rw [←hc,mul_inv_cancel_right]

/-- The original rank-two K embeds in the marked fixed subgroup upstairs. -/
theorem fixed_three_rank_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (hres : c.component = primeToResidual 3 I)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := residual H
  have hKL : K ≤ c.component.map I.subtype := by
    rw [hres]
    exact r.residual_le_escape_cubic hI
  let eL := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := eL.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (eL.apply_symm_apply ⟨k,hKL k.property⟩)
  have hfix (k : K) : f k ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Subtype.ext
    rw [ha,hf]
    have hkMc : (k : G) ∈ Mc :=
      r.geometry.in_partner (map_subtype_le _ k.property)
    have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp
      ((r.marked_centralizer_of_seed_card hcard hz hzne).2.ge hkMc)
    rw [← hkz,mul_inv_cancel_right]
  let g := f.codRestrict a.fixedSubgroup hfix
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : a.fixedSubgroup => ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  rw [r.residual_rank_two] at hbound
  exact hbound

variable {D : Type*} [Group D] [Finite D]

/-- The literal quotient involution centralizer has three-rank at least two. -/
theorem quotient_centralizer_three_rank_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hres : c.component = primeToResidual 3 I)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a) :
    ∃ t : D, orderOf t = 2 ∧ DoubleCoverCentralizer.TwoCentral t ∧
      2 ≤ primeRank 3 (centralizer ({t} : Set D)) := by
  obtain ⟨t,ht,htc,hact⟩ := quotient_twoCentral_of_inner c e a hai
  let q : c.component →* D := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hk : q.ker = pCore 2 c.component := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [e.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  have hle : a.fixedSubgroup.map q ≤ centralizer ({t} : Set D) := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hact y
    rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  refine ⟨t,ht,htc,?_⟩
  have hlow := fixed_three_rank_of_residual r hcard c hI hz hzne hres a ha
  have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel
    (by decide : Odd 3) q (by rw [hk]; exact pCore_isPGroup) a.fixedSubgroup
  rw [←he] at hlow
  exact hlow.trans (primeRank_mono 3 hle)
omit hcard in
/-- The original wreath quotient makes H solvable. -/
theorem source_H_solvable : Group.IsSolvable H := by
  obtain ⟨e⟩ := r.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

omit hcard in
/-- The same intersection is solvable, without a model assumption. -/
theorem component_intersection_solvable : Group.IsSolvable (componentIntersection (H := H) c) := by
  let : Group.IsSolvable H := source_H_solvable r
  let f : componentIntersection (H := H) c →* H := {
    toFun x := ⟨((x.val : I) : G),x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : H => (w : G)) h
  exact Group.isSolvable_of_isSolvable_injective hf

omit hcard in
/-- Restriction of the actual S to its subnormal component supplies the full Sylow. -/
theorem component_intersection_sylow
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆) :
    ∃ Q : Sylow 2 c.component, (Q : Subgroup c.component) ≤ componentIntersection (H := H) c := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal c.component c.isComponent.1
  refine ⟨Q,?_⟩
  intro x hx
  have hxP : (x : I) ∈ P := by rw [hQ] at hx; exact hx
  have hxT : ((x : I) : G) ∈ (T : Subgroup G) :=
    (show planeSylow T ⁅V,B⁆ ≤ (T : Subgroup G) from inf_le_left)
      (hP ▸ mem_map_of_mem I.subtype hxP)
  exact r.outside.1.1.2 hxT

omit hcard in
/-- Once the original cubic residual is identified, K forces rank two in H∩L. -/
theorem component_intersection_three_rank (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hres : c.component = primeToResidual 3 I) :
    2 ≤ primeRank 3 (componentIntersection (H := H) c) := by
  let K := residual H
  have hKL : K ≤ c.component.map I.subtype := by
    rw [hres]
    exact r.residual_le_escape_cubic hI
  let eL := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := eL.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (eL.apply_symm_apply ⟨k,hKL k.property⟩)
  let g : K →* componentIntersection (H := H) c := f.codRestrict _ (fun k => by
    change ((f k : I) : G) ∈ H
    rw [hf]
    exact map_subtype_le _ k.property)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : componentIntersection (H := H) c =>
      ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  rw [r.residual_rank_two] at hbound
  exact hbound

/-- H lies in Mc=C_G(z), so the original marked action fixes the whole intersection. -/
theorem component_intersection_fixed (_hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    componentIntersection (H := H) c ≤ a.fixedSubgroup := by
  intro x hx
  rw [MulAut.mem_fixedSubgroup]
  apply Subtype.ext
  apply Subtype.ext
  rw [ha]
  have hc := (r.marked_centralizer_of_seed_card hcard hz hzne).2.ge (r.geometry.in_partner hx)
  have hh : (x : G) * z = z * (x : G) := mem_centralizer_singleton_iff.mp hc
  rw [←hh,mul_inv_cancel_right]

omit hcard in
/-- The actual intersection Mc ∩ I is maximal inside the minimal escape. -/
theorem minimal_intrinsic_intersection (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (_hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆) :
    IsCoatom (Mc.comap I.subtype) := by
  apply isCoatom_iff_ge_of_le.mpr
  constructor
  · intro he
    apply hI.1.2.2
    intro x hx
    have hh : (⟨x,hx⟩ : I) ∈ Mc.comap I.subtype := he ▸ mem_top _
    exact hh
  · intro J hJ hCJ
    have hCM : (Mc.comap I.subtype).map I.subtype = Mc ⊓ I := by
      rw [map_comap_eq,range_subtype,inf_comm]
    have hle : Mc ⊓ I ≤ J.map I.subtype := hCM ▸ map_mono hCJ
    rcases r.minimal_intermediate_direct hI hle (map_subtype_le J) with he | he
    · have hh : J = Mc.comap I.subtype := map_injective I.subtype_injective (he.trans hCM.symm)
      exact hh.le
    · exfalso
      apply hJ
      apply map_injective I.subtype_injective
      simpa only [← MonoidHom.range_eq_map,range_subtype] using he

/-- The marked action fixes the full Borel when its fixed subgroup normalizes the Sylow. -/
theorem marked_component_borel_fixed
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a)
    (Q : Sylow 2 c.component)
    (hQ : (Q : Subgroup c.component) ≤ a.fixedSubgroup)
    (hn : a.fixedSubgroup ≤ normalizer (Q : Set c.component)) :
    ∀ x ∈ normalizer (Q : Set c.component), a x = x := by
  let C := Mc.comap I.subtype
  let L := c.component
  have hD : a.fixedSubgroup.map L.subtype = L ⊓ C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      change (y : G) ∈ Mc
      rw [← (r.marked_centralizer_of_seed_card hcard hz hzne).2]
      apply mem_centralizer_singleton_iff.mpr
      have hh := ha y
      rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · rintro ⟨hxL,hxC⟩
      refine ⟨⟨x,hxL⟩,?_,rfl⟩
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      apply Subtype.ext
      rw [ha]
      have hc : (x : G) * z = z * x := mem_centralizer_singleton_iff.mp
        ((r.marked_centralizer_of_seed_card hcard hz hzne).2.ge hxC)
      rw [←hc,mul_inv_cancel_right]
  have hcore : (L ⊓ C).pCoreIn 2 = (Q : Subgroup L).map L.subtype := by
    rw [← hD,← map_pCoreIn_of_injective 2 _ _ L.subtype_injective]
    congr 1
    apply le_antisymm
    · have hh := pCoreIn_le_sylow a.fixedSubgroup (Q.subtype hQ)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hQ] using hh
    · exact le_pCoreIn_of_normalizes Q.isPGroup' hQ hn
  have hnon : ¬ (L ⊓ C).pCoreIn 2 ≤ centralizer (L : Set I) := by
    intro hc
    have ht := hai.1
    obtain ⟨t,_,he⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution Q a
      (hai.2.1 ▸ pow_orderOf_eq_one a) ht
      (fun x hx => (MulAut.mem_fixedSubgroup _ _).mp (hQ hx)) c.center_two
    have hacent : MulAut.conj (t : L) = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (t : I) * (x : I) * (t : I)⁻¹ = x
      have htc := hc (hcore ▸ mem_map_of_mem L.subtype t.property) (x : I) x.property
      exact mul_inv_eq_iff_eq_mul.mpr htc.symm
    have hh : orderOf a = 1 := by rw [←he,hacent,orderOf_one]
    have ho := hai.2.1
    omega
  have hle := c.isComponent.normalizer_intersection_core_le
    (minimal_intrinsic_intersection r hI hP) hnon
  intro x hx
  have hxI : (x : I) ∈ normalizer ((L ⊓ C).pCoreIn 2 : Set I) := by
    rw [hcore]
    exact (Q : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem L.subtype hx)
  have hc := hle ⟨x.property,hxI⟩
  have hxD : (x : I) ∈ a.fixedSubgroup.map L.subtype := hD ▸ ⟨x.property,hc⟩
  exact (MulAut.mem_fixedSubgroup _ _).mp ((mem_map_iff_mem L.subtype_injective).mp hxD)
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
