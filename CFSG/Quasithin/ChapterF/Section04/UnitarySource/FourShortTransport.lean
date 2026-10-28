module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortTransport
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourPlacement
/-!
# Short-root transport in the marked projective unitary amalgam

Projectivization is faithful in dimension four in characteristic two. Thus
any element carrying the marked short root into the Hermitian plane core
preserves the plane. The whole-overlap comparison transports this fact to
an arbitrary subgroup amalgam, preserving both endpoint maps.

If the opposite full group is a product of its local endpoint with actors
normalizing the plane core, its short-root centralizer lies in the plane
normalizer. This is the local common-centralizer step of F.4.42; it does
not assert containment of the entire ambient short-root centralizer.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
-/

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourShortTransport
open GreenBook.LieModels.UnitaryFour FourPlacement
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm

def shortRoot : ProjectiveGroup m hm := projection m hm (shortLocal F σ hσ).val

theorem shortRoot_order : orderOf (shortRoot m hm) = 2 := by
  change orderOf (project F (form F σ hσ) (shortLocal F σ hσ).val) = 2
  rw [orderOf_injective (project F (form F σ hσ)) (project_injective F (form F σ hσ))]
  exact (orderOf_coe (shortLocal F σ hσ)).trans
    ((orderOf_coe (SourceNormalizer.FourShortRoot.shortMark F σ hσ)).trans
      (SourceNormalizer.FourShortRoot.shortMark_order F σ hσ))

theorem shortRoot_mem_core : shortRoot m hm ∈ planeCore m hm := by
  rw [←matrix_plane_core_map]
  apply mem_map_of_mem
  refine ⟨shortLocal F σ hσ,?_,rfl⟩
  rw [←L2MatrixRadical_eq_twoCore]
  exact (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))).property

theorem planeCore_le_point : planeCore m hm ≤ pointParabolic m hm := by
  rw [←matrix_plane_core_map]
  rintro x ⟨a,⟨b,hb,rfl⟩,rfl⟩
  rw [←L2MatrixRadical_eq_twoCore] at hb
  obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨b,hb⟩
  refine ⟨b.val,?_,rfl⟩
  rw [←congrArg (fun u : radical F σ hσ => u.val.val) hX]
  change unipotentSU F σ hσ X.toAdd ∈ pointParabolicSU F (form F σ hσ)
  rw [mem_pointParabolicSU]
  exact ⟨rfl,rfl,rfl⟩

def shortOverlap : overlap m hm := ⟨shortRoot m hm, by
  rw [←exact_overlap]
  exact ⟨planeCore_le_point m hm (shortRoot_mem_core m hm),
    (pCoreIn_le 2 _).trans (L2_le_planeParabolic m hm) (shortRoot_mem_core m hm)⟩⟩

theorem conjugator_short_to_core (g : ProjectiveGroup m hm)
    (hg : g * shortRoot m hm * g⁻¹ ∈ planeCore m hm) : g ∈ planeParabolic m hm := by
  obtain ⟨a,rfl⟩ := project_surjective F (form F σ hσ) g
  rw [←matrix_plane_core_map] at hg
  obtain ⟨v,⟨b,hb,rfl⟩,he⟩ := hg
  rw [←L2MatrixRadical_eq_twoCore] at hb
  obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨b,hb⟩
  have heq : a * unipotentSU F σ hσ (shortParameter F σ) * a⁻¹ = unipotentSU F σ hσ X.toAdd := by
    have hh : a * unipotentSU F σ hσ (shortParameter F σ) * a⁻¹ = b.val :=
      (project_injective F (form F σ hσ)) (by
        rw [map_mul,map_mul,map_inv]
        exact he.symm)
    exact hh.trans (congrArg (fun u : radical F σ hσ => u.val.val) hX).symm
  exact ⟨a,SourceNormalizer.FourShortTransport.conjugator_short_to_radical F σ hσ a X.toAdd heq,rfl⟩


variable {G : Type*} [Group G] {P R : Subgroup G}
variable (e : RankTwoAmalgam.Iso
  (RankTwoAmalgam.ofSubgroups P (P ⊓ R) R inf_le_left inf_le_right) (amalgam m hm).reverse)

def sourceShort : (P ⊓ R : Subgroup G) := e.middle.symm (shortOverlap m hm)

theorem sourceShort_order : orderOf (sourceShort m hm e).val = 2 := by
  exact (orderOf_coe (sourceShort m hm e)).trans
    ((e.middle.symm.orderOf_eq (shortOverlap m hm)).trans
      ((orderOf_coe (shortOverlap m hm)).symm.trans (shortRoot_order m hm)))

private theorem comparison_agrees (x : (P ⊓ R : Subgroup G)) :
    (e.left ⟨x.val,x.property.1⟩).val = (e.right ⟨x.val,x.property.2⟩).val :=
  (congrArg Subtype.val (e.left_commutes x)).trans
    (congrArg Subtype.val (e.right_commutes x)).symm

private theorem sourceShort_left :
    (e.left ⟨(sourceShort m hm e).val,(sourceShort m hm e).property.1⟩).val = shortRoot m hm := by
  have hh := congrArg Subtype.val (e.left_commutes (sourceShort m hm e))
  change (e.left ⟨(sourceShort m hm e).val,(sourceShort m hm e).property.1⟩).val =
    (e.middle (sourceShort m hm e)).val at hh
  rw [show e.middle (sourceShort m hm e) = shortOverlap m hm from e.middle.apply_symm_apply _] at hh
  exact hh

private theorem sourceShort_right :
    (e.right ⟨(sourceShort m hm e).val,(sourceShort m hm e).property.2⟩).val = shortRoot m hm :=
  (comparison_agrees m hm e _).symm.trans (sourceShort_left m hm e)

private theorem core_mem_iff (x : P) :
    x.val ∈ P.pCoreIn 2 ↔ (e.left x).val ∈ planeCore m hm := by
  rw [planeCore_eq_twoCore]
  change P.subtype x ∈ (pCore 2 P).map P.subtype ↔
    (planeParabolic m hm).subtype (e.left x) ∈ (pCore 2 (planeParabolic m hm)).map (planeParabolic m hm).subtype
  rw [mem_map_iff_mem P.subtype_injective,mem_map_iff_mem (planeParabolic m hm).subtype_injective,
    ←pCore_map_iso 2 e.left]
  exact (mem_map_iff_mem (f := e.left.toMonoidHom) e.left.injective).symm

include e in
private theorem core_le_other : P.pCoreIn 2 ≤ R := by
  intro x hx
  let p : P := ⟨x,pCoreIn_le 2 P hx⟩
  have hp := (core_mem_iff m hm e p).mp hx
  let b : overlap m hm := ⟨(e.left p).val,by
    exact (exact_overlap m hm).le ⟨planeCore_le_point m hm hp,(e.left p).property⟩⟩
  let a := e.middle.symm b
  have he : (⟨a.val,a.property.1⟩ : P) = p := by
    apply e.left.injective
    apply Subtype.ext
    have hh := congrArg Subtype.val (e.left_commutes a)
    change (e.left ⟨a.val,a.property.1⟩).val = (e.middle a).val at hh
    rw [show e.middle a = b from e.middle.apply_symm_apply _] at hh
    exact hh
  have hv : a.val = x := congrArg Subtype.val he
  exact hv ▸ a.property.2

theorem sourceShort_mem_core : (sourceShort m hm e).val ∈ P.pCoreIn 2 := by
  apply (core_mem_iff m hm e ⟨(sourceShort m hm e).val,(sourceShort m hm e).property.1⟩).mpr
  rw [sourceShort_left]
  exact shortRoot_mem_core m hm

/-- A product decomposition with an actor normalizing the plane core extends
its native short-root transporter bound to the complete opposite group. -/
theorem sourceShort_opposite_centralizer (N M : Subgroup G)
    (hPN : P ≤ N) (hNQ : N ≤ normalizer (P.pCoreIn 2 : Set G))
    (hfactor : ∀ g ∈ M, ∃ k ∈ R, ∃ b ∈ N, g = k*b) :
    M ⊓ centralizer ({(sourceShort m hm e).val} : Set G) ≤ N := by
  rintro g ⟨hgM,hgt⟩
  obtain ⟨k,hk,b,hb,rfl⟩ := hfactor g hgM
  let t := (sourceShort m hm e).val
  let y := b*t*b⁻¹
  have hyQ : y ∈ P.pCoreIn 2 := (mem_normalizer_iff.mp (hNQ hb) t).mp
    (sourceShort_mem_core m hm e)
  have hyP : y ∈ P := pCoreIn_le 2 P hyQ
  have hyR : y ∈ R := core_le_other m hm e hyQ
  have hkt : k⁻¹*t*k = y := by
    have hh : (k*b)*t*(k*b)⁻¹ = t :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgt)
    calc
      _ = k⁻¹*((k*b)*t*(k*b)⁻¹)*k := by rw [hh]
      _ = y := by dsimp [y]; group
  let kr : R := ⟨k,hk⟩
  let tr : R := ⟨t,(sourceShort m hm e).property.2⟩
  have heq : kr⁻¹*tr*kr = (⟨y,hyR⟩ : R) := Subtype.ext hkt
  have hmodel : (e.right kr).val⁻¹ * shortRoot m hm * (e.right kr).val ∈ planeCore m hm := by
    have he := congrArg (fun x : R => (e.right x).val) heq
    simp only [map_mul,map_inv] at he
    change (e.right kr).val⁻¹ * (e.right tr).val * (e.right kr).val = _ at he
    have htmod : (e.right tr).val = shortRoot m hm := sourceShort_right m hm e
    rw [htmod] at he
    rw [he,←comparison_agrees m hm e (⟨y,hyP,hyR⟩ : (P ⊓ R : Subgroup G))]
    exact (core_mem_iff m hm e ⟨y,hyP⟩).mp hyQ
  have hkplane : (e.right kr).val ∈ planeParabolic m hm := by
    apply (planeParabolic m hm).inv_mem_iff.mp
    exact conjugator_short_to_core m hm _ (by simpa only [inv_inv] using hmodel)
  let c : overlap m hm := ⟨(e.right kr).val,by
    exact (exact_overlap m hm).le ⟨(e.right kr).property,hkplane⟩⟩
  let a := e.middle.symm c
  have he : (⟨a.val,a.property.2⟩ : R) = kr := by
    apply e.right.injective
    apply Subtype.ext
    have hh := congrArg Subtype.val (e.right_commutes a)
    change (e.right ⟨a.val,a.property.2⟩).val = (e.middle a).val at hh
    rw [show e.middle a = c from e.middle.apply_symm_apply _] at hh
    exact hh
  have hv : a.val = k := congrArg Subtype.val he
  have hkP : k ∈ P := hv ▸ a.property.1
  exact N.mul_mem (hPN hkP) hb

end CFSG.Quasithin.ChapterF.UnitarySource.FourShortTransport
