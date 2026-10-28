module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InvariantMarking
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# A Sylow exchanger preserving the same original Cartan

Hall conjugacy factors T through T intersect L₀ and the normalizer of the
specified Cartan C. Since L₀ normalizes the original component L, the latter
normalizer contains a factor exchanger. If the actual odd Hall subgroup B
of H intersect M lies in the abelian C, Hall uniqueness makes every element
of N_T(C) normalize B as well. No replacement of C or B is made.

NaturalTensorExchange applies both statements to the actual tensor branch
and chooses this exchanger in its original component quotient markings.
Source: Aschbacher--Smith 9.2.7, printed pp.731--732, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- A factor exchanger in the original Sylow group preserves the specified
Hall Cartan, with no new conjugation of that Cartan. -/
theorem original_cartan_exchanger
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L)
    (hHall : IsHallSubgroup OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L))) :
    ∃ s : G, s ∈ (T : Subgroup G) ∧ s ∉ normalizer (L : Set G) ∧
      s ∈ normalizer (C : Set G) := by
  let R := localOrbit T L
  let U := (T : Subgroup G) ⊓ R
  let N := sourceOrbitSylowNormalizer T L
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := le_normalizer_componentOrbit L T
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTR).trans inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf hTR (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hCN : C ≤ N := hC.trans (map_subtype_le _)
  have hHallN := OddHall.hall_of_twoResidual N C hC hHall
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  have hSN : (S : Subgroup R) ≤ N.subgroupOf R := by
    rw [source_orbit_sylow_normalizer_eq S hS]
    exact (S : Subgroup R).le_normalizer
  let a := subgroupOfEquivOfLe (show N ≤ R from inf_le_left)
  let P := (S.subtype hSN).mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : (P : Subgroup N).map N.subtype = U := by
    change (((S : Subgroup R).subgroupOf (N.subgroupOf R)).map a.toMonoidHom).map N.subtype = U
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      have hzT : (z.val : G) ∈ (T : Subgroup G) := by
        change z.val ∈ (T : Subgroup G).subgroupOf R
        rwa [←hS]
      exact ⟨hzT,z.val.property⟩
    · intro hx
      have hxN : x ∈ N := ⟨hx.2,hTU hx.1⟩
      refine ⟨⟨x,hxN⟩,⟨⟨⟨x,hx.2⟩,hxN⟩,?_,rfl⟩,rfl⟩
      exact hS.symm ▸ hx.1
  have hfrat := OddHall.normal_sylow_frattini N U T C
    (source_sl2_sylow_normalizer_solvable D e hn) inf_le_left hTN P hP hCN hHallN
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hn
  have hx' : x ∈ (U : Set G) * ((T ⊓ normalizer (C : Set G) : Subgroup G) : Set G) := hfrat ▸ hx
  obtain ⟨r,hr,s,hs,he⟩ := hx'
  refine ⟨s,hs.1,?_,hs.2⟩
  intro hsn
  exact hxn (he ▸ (normalizer (L : Set G)).mul_mem
    (source_nonnormal_orbit_le_normalizer D hn hr.2) hsn)

variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
include c

/-- Inside the prescribed Sylow group, normalizing an abelian Cartan containing
the original Hall subgroup also normalizes that Hall subgroup itself. -/
theorem original_hall_normalized_by_cartan_normalizer
    (C : Subgroup G) [IsMulCommutative C] (hBC : B.map H.subtype ≤ C) :
    (T : Subgroup G) ⊓ normalizer (C : Set G) ≤ normalizer (B.map H.subtype : Set G) := by
  intro t ht
  let J := D.maximalLocal.subgroupOf H
  let tJ : J := ⟨⟨t,c.hstar.1.1.2 ht.1⟩,le_normalizer_componentOrbit L T ht.1⟩
  let B0 := B.subgroupOf J
  have hc : B0.map (MulAut.conj tJ).toMonoidHom ≤ centralizer (B0 : Set J) := by
    rintro x ⟨b,hb,rfl⟩ y hy
    have hbC : (b:G) ∈ C := hBC (mem_map_of_mem H.subtype hb)
    have hyC : (y:G) ∈ C := hBC (mem_map_of_mem H.subtype hy)
    have hb'C : t*(b:G)*t⁻¹ ∈ C := (mem_normalizer_iff.mp ht.2 _).mp hbC
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C => (z : G))
      (mul_comm (⟨y,hyC⟩ : C) ⟨t*(b:G)*t⁻¹,hb'C⟩)
  have he : B0.map (MulAut.conj tJ).toMonoidHom = B0 :=
    (c.hall.map_conj tJ).eq_of_le c.hall
      (c.hall.le_of_le_normalizer (c.hall.map_conj tJ)
        (hc.trans (Subgroup.centralizer_le_normalizer _)))
  have heH := congrArg (map J.subtype) he
  rw [map_subgroupOf_map_conj_eq c.hall_le,map_subgroupOf_eq_of_le c.hall_le] at heH
  apply mem_normalizer_iff_map_conj_eq.mpr
  have heG := congrArg (map H.subtype) heH
  rw [map_map] at heG
  change B.map ((MulAut.conj t).toMonoidHom.comp H.subtype) = B.map H.subtype at heG
  rwa [←map_map] at heG

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
