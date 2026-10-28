module
public import Theory.Mathieu.M11.Properties.InvolutionCentralizer
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.PerfectCentralCoverSemidihedral
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The ordinary M₁₁ local geometry and central two-covers

The semidihedral Sylow presentation identifies its full center with a single
involution. Conjugacy of involutions and the checked maximality of the native
involution centralizer prove that its centralizer is maximal for every Sylow
subgroup, under any specified M₁₁ equivalence. The same Sylow presentation
excludes a nontrivial two-group kernel in a finite perfect central cover.

These supply the literal center and covering-group clauses in the ordinary
M₁₁ branch of Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097, and
15.1.22(6), printed p.1100. No sporadic catalogue is assumed.
-/

open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.OrdinaryLocal

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

public theorem involution_centralizer_isCoatom (z : M11) (hz : orderOf z = 2) :
    IsCoatom (centralizer ({z} : Set M11)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA z hz)
  let e := MulAut.conj g
  have he : e z = m11GeneratorAInM11 := hg
  apply (e.mapSubgroup.isCoatom_iff _).mp
  have hc : (centralizer ({z} : Set M11)).map e.toMonoidHom = m11InvolutionCentralizer := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, m11_mem_involutionCentralizer_iff]
    rw [← he]
    constructor
    · intro h
      have hh := congrArg e h
      simpa only [map_mul,e.apply_symm_apply] using hh
    · intro h
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using h
  change IsCoatom ((centralizer ({z} : Set M11)).map e.toMonoidHom)
  rw [hc]
  exact m11_involutionCentralizer_isCoatom

public theorem centralizer_isCoatom {K : Type*} [Group K]
    (e : K ≃* M11) (S : Sylow 2 K) :
    IsCoatom (centralizer ((center S).map (S : Subgroup K).subtype : Set K)) := by
  let : Finite K := Finite.of_injective e e.injective
  obtain ⟨P,a,b,ha,hb,hc,hgen⟩ := m11_exists_semidihedral_sylow
  have hZ : center P = zpowers (a ^ 4) :=
    Semidihedral.center_eq (n := 4) (by decide) a b ha hb hc hgen
  let z : M11 := (a ^ 4 : P)
  have hz : orderOf z = 2 := by
    rw [show orderOf z = orderOf (a ^ 4) from orderOf_coe _]
    rw [orderOf_pow,ha]
    decide
  have hCP : centralizer ((center P).map (P : Subgroup M11).subtype : Set M11) =
      centralizer ({z} : Set M11) := by
    rw [hZ, MonoidHom.map_zpowers]
    ext x
    constructor
    · intro hx
      exact mem_centralizer_singleton_iff.mpr (hx z (mem_zpowers z)).symm
    · intro hx y hy
      have hzC : z ∈ centralizer ({x} : Set M11) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx).symm
      exact mem_centralizer_singleton_iff.mp ((zpowers_le.mpr hzC) hy)
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M11 R P
  let f : K ≃* M11 := e.trans (MulAut.conj g)
  have hf : (S : Subgroup K).map f.toMonoidHom = (P : Subgroup M11) := by
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl, ← map_map]
    exact congrArg (fun Q : Sylow 2 M11 => (Q : Subgroup M11)) hg
  have hZS : ((center S).map (S : Subgroup K).subtype).map f.toMonoidHom =
      (center P).map (P : Subgroup M11).subtype := by
    rw [map_map, ← map_center_image_of_injective (S : Subgroup K) f.toMonoidHom f.injective,hf]
  apply (f.mapSubgroup.isCoatom_iff _).mp
  change IsCoatom ((centralizer ((center S).map (S : Subgroup K).subtype : Set K)).map f.toMonoidHom)
  rw [centralizer_map_equiv,hZS,hCP]
  exact involution_centralizer_isCoatom z hz

public theorem central_two_cover_injective {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hZ : IsPGroup 2 (center L)) (e : L ⧸ center L ≃* M11) :
    Function.Injective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hk : f.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,a,b,ha,hb,hc,hgen⟩ := m11_exists_semidihedral_sylow
  have htwo := PerfectCentralCovering.not_two_dvd_card_kernel_of_semidihedral_sylow
    f (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le P a b ha
    (by simpa only [hb] using pow_orderOf_eq_one b) hc hgen
  apply f.ker_eq_bot_iff.mp
  apply card_eq_one.mp
  exact ((hk.symm ▸ hZ).card_eq_or_dvd).resolve_right htwo

end Sporadic.Mathieu.OrdinaryLocal
