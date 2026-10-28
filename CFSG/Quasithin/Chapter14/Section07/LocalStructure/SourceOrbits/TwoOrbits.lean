module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.CriticalOrbit
/-!
# The two subgroup orbits in the original natural binary action

The literal flag point labels the conjugates of U: equal transported points
give equal transported U because the point stabilizer is H. The full natural
L-action transports any two distinct nonzero vectors, so the stabilizer of
the original point is transitive on the remaining U-conjugates. This proves
the exact two-orbit cover used in the commutator argument.

Source: Aschbacher–Smith 14.7.12, printed p.1046.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
 {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
 {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
 (d : Data T L V F W)
include d in
 theorem mem_H_of_fixes_point {a : G} (h : (MulAut.conj a) d.z = d.z) : a ∈ F.H := by
  change a ∈ normalizer (F.Vi 1 : Set G)
  rw [mem_normalizer_iff_map_conj_eq,d.point,MonoidHom.map_zpowers]
  exact congrArg zpowers h
include d in
 theorem map_U_eq_of_point_eq {a b : G}
    (h : (MulAut.conj a) d.z = (MulAut.conj b) d.z) :
    F.U.conjBy a = F.U.conjBy b := by
  have hf : (MulAut.conj (b⁻¹*a)) d.z = d.z := by
    have hh := congrArg (MulAut.conj b⁻¹) h
    simpa [MulAut.conj_apply,mul_assoc] using hh
  have hn := mem_normalizer_iff_map_conj_eq.mp
    (d.conjugationSection.normalized (mem_H_of_fixes_point d hf))
  change F.U.conjBy (b⁻¹*a) = F.U at hn
  have hh := congrArg (fun A : Subgroup G => A.conjBy b) hn
  simpa only [conjBy_conjBy,mul_inv_cancel_left] using hh
include d in
 theorem two_orbit {A : Subgroup G}
    (ha : ∃ a ∈ L, A = F.U.conjBy a) (hne : A ≠ F.U) (l : L) :
    F.U.conjBy (l : G) = F.U ∨
      ∃ p : (L ⊓ F.H : Subgroup G), F.U.conjBy (l : G) = A.conjBy (p : G) := by
  classical
  by_cases he : F.U.conjBy (l : G) = F.U
  · exact Or.inl he
  right
  obtain ⟨a,ha,rfl⟩ := ha
  have hzV : d.z ∈ V := F.le_seed 1 (d.point.symm ▸ mem_zpowers d.z)
  have haz : (MulAut.conj a) d.z ∈ V :=
    (mem_normalizer_iff.mp (d.natural.chosen.normalizes ha) d.z).mp hzV
  have hlz : (MulAut.conj (l : G)) d.z ∈ V :=
    (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) d.z).mp hzV
  have hazne : (MulAut.conj a) d.z ≠ 1 := (map_ne_one_iff _ (MulAut.conj a).injective).mpr d.z_ne_one
  have hlzne : (MulAut.conj (l : G)) d.z ≠ 1 := (map_ne_one_iff _ (MulAut.conj (l : G)).injective).mpr d.z_ne_one
  have hza : d.z ≠ (MulAut.conj a) d.z := by
    intro hz
    exact hne (by simpa only [conjBy_one] using
      map_U_eq_of_point_eq d (a := a) (b := 1) (by simpa using hz.symm))
  have hzl : d.z ≠ (MulAut.conj (l : G)) d.z := by
    intro hz
    exact he (by simpa only [conjBy_one] using
      map_U_eq_of_point_eq d (a := l) (b := 1) (by simpa using hz.symm))
  obtain ⟨p,hp,hpz,hpaz⟩ := pair_transporter d hzV haz hzV hlz d.z_ne_one hazne
    d.z_ne_one hlzne hza hzl
  have hpH : p ∈ F.H := mem_H_of_fixes_point d hpz
  refine ⟨⟨p,hp,hpH⟩,?_⟩
  rw [conjBy_conjBy]
  apply map_U_eq_of_point_eq d
  simpa only [MulAut.conj_apply,mul_inv_rev,mul_assoc] using hpaz.symm
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
