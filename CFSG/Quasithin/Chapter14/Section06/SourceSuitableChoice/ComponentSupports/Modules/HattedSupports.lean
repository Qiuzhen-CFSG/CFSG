module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.CentralOverlap

/-!
# Hatted directness supplies the covering-support geometry

The hatted projection is the literal map U → U/C_U(K). Disjoint images of
two actual supports imply that their intersection centralizes K. This
constructs the weaker geometry consumed by the covering-section vector
argument, retaining N_T(W), inverse conjugation, and N_Mc(N_T(W))=T.

This implication neither identifies the two natural sections nor asserts
their intersection is contained in Z. Source: Aschbacher--Smith F.9.18(4iii)
and 14.6.22--24, printed pp.325,1038--1039.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
variable {G : Type*} [Group G]

/-- The exact hatted quotient gives valid support geometry even when the
covering supports have a nontrivial common fixed part modulo Z. -/
theorem centralOverlapGeometry_of_pair_fixed_quotient
    (T : Sylow 2 G) (Mc U K W W' : Subgroup G) [IsMulCommutative U]
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ U) (hZW : Chapter15.Section03.centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (hdis : let q := QuotientGroup.mk' ((centralizer (K : Set G)).subgroupOf U)
      Disjoint ((W.subgroupOf U).map q) ((W'.subgroupOf U).map q))
    (hpair : ∀ t ∈ (T : Subgroup G), W.map (MulAut.conj t).toMonoidHom = W ∨
      W.map (MulAut.conj t).toMonoidHom = W')
    (x : G) (hx : x ∈ (T : Subgroup G))
    (hmove : W.map (MulAut.conj x).toMonoidHom ≠ W)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G)) :
    CentralOverlapGeometry T Mc U K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  apply centralOverlapGeometry_of_pair T Mc U K W W' hK hWU hZW hKW hKW' _ hpair x hx hmove hlocal
  exact central_intersection_of_disjoint_images K U W W' hWU
    (QuotientGroup.mk' ((centralizer (K : Set G)).subgroupOf U))
    (by rw [QuotientGroup.ker_mk']) hdis

/-- F.9.18 uses the whole component orbit K0 in its hatted kernel.
Its fixed subgroup is contained in C_U(K), so the same movement proof
applies to its actual quotient, without replacing that quotient by U/C_U(K). -/
theorem centralOverlapGeometry_of_pair_orbit_quotient
    (T : Sylow 2 G) (Mc U K K0 W W' : Subgroup G) [IsMulCommutative U]
    (hKK0 : K ≤ K0)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ U) (hZW : Chapter15.Section03.centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (hdis : let q := QuotientGroup.mk' ((centralizer (K0 : Set G)).subgroupOf U)
      Disjoint ((W.subgroupOf U).map q) ((W'.subgroupOf U).map q))
    (hpair : ∀ t ∈ (T : Subgroup G), W.map (MulAut.conj t).toMonoidHom = W ∨
      W.map (MulAut.conj t).toMonoidHom = W')
    (x : G) (hx : x ∈ (T : Subgroup G))
    (hmove : W.map (MulAut.conj x).toMonoidHom ≠ W)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G)) :
    CentralOverlapGeometry T Mc U K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  apply centralOverlapGeometry_of_pair T Mc U K W W' hK hWU hZW hKW hKW' _ hpair x hx hmove hlocal
  exact central_intersection_of_disjoint_images K U W W' hWU
    (QuotientGroup.mk' ((centralizer (K0 : Set G)).subgroupOf U))
    (by
      rw [QuotientGroup.ker_mk']
      intro u hu
      exact Subgroup.centralizer_le hKK0 hu) hdis

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
