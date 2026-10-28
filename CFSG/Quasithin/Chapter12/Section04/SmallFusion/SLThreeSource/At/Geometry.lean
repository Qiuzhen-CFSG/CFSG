module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.LocalConstruction

/-!
# The fixed line in the local L₃ geometry

A nonfixed central vector would conjugate the whole Sylow group into the
local vector centralizer, contradicting the index-two Sylow witness there.
Thus the original central omega subgroup meets V in exactly C_V(L). Combining
this with the constructed supplement proves both original 12.4.5 identities.

Adapted from SLThreeSource/Geometry.lean and Source.lean, preserving the literal
plane and Sylow subgroup. Source: Aschbacher–Smith, 12.4.5, pp.813–814.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

include d in
/-- The fixed-line calculation follows from the local Sylow witness and
the already proved transitivity outside C_V(L). A nonfixed central vector
would conjugate the whole T into M∩C_G(v), contradicting its Sylow order. -/
theorem LocalGeometry.fixed_line_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) :
    omegaCenterIn (T : Subgroup G) ⊓ V = fixedSubgroup L V := by
  obtain ⟨z, _, hgen, _, _, hzZ, _⟩ := At.exists_fixed_involution_setup_of_card_two
    h D structural uniquenessEarlier_knownSimple (ext.fixed_card_eq_two hne)
  have hFZ : fixedSubgroup L V ≤ omegaCenterIn (T : Subgroup G) := by
    rw [hgen, omegaCenterIn_eq_omegaOneAmbient]
    exact zpowers_le_of_mem hzZ
  apply le_antisymm ?_ (le_inf hFZ inf_le_left)
  intro x hx
  by_contra hxf
  obtain ⟨l, hl, hlx⟩ := ext.transitive_nonfixed hne x d.v
    hx.2 (d.le_module d.mem_plane) hxf d.nonfixed
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer ({d.v} : Set G)
  have hlM : l ∈ M := L.le_normalizer hl
  let f : T →* C :=
    ((MulAut.conj l).toMonoidHom.comp (T : Subgroup G).subtype).codRestrict C (by
      intro t
      refine ⟨?_, ?_⟩
      · exact M.mul_mem (M.mul_mem hlM ((structural L h).1 t.property))
          (M.inv_mem hlM)
      · apply mem_centralizer_singleton_iff.mpr
        rw [← hlx]
        exact (MulAut.conj l).map_mul (t : G) x |>.symm.trans
          ((congrArg (MulAut.conj l)
            (((mem_omegaCenterIn_iff _ _).mp hx.1).2.1 t t.property)).trans
              ((MulAut.conj l).map_mul x (t : G))))
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext ((MulAut.conj l).injective (congrArg Subtype.val he))
  obtain ⟨P, hP⟩ := d.local_sylow
  change (P : Subgroup C).map C.subtype = d.R at hP
  obtain ⟨Q, hQ⟩ :=
    (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card T ≤ Nat.card d.R := by
    calc
      Nat.card T = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
      _ = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
      _ = Nat.card d.R := by
        rw [← hP]
        exact Nat.card_congr
          ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv
  have he : d.R = (T : Subgroup G) := eq_of_le_of_card_ge inf_le_left hc
  have hi := d.index
  change d.R.relIndex (T : Subgroup G) = 2 at hi
  simp [he] at hi

namespace At

/-- The omega-center conclusions of source 12.4.5 at the original G,T. -/
theorem omega_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) ∧
      omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
        omegaCenterIn (T : Subgroup G) ⊔ V := by
  obtain ⟨ext⟩ := extension_of_modules h D modules hmodel hne
  obtain ⟨d⟩ := local_geometry h D hmany structural modules hmodel hne
  have hfixed : omegaCenterIn (T : Subgroup G) ⊓ V ≤ centralizer (L : Set G) := by
    rw [d.fixed_line_at h structural ext hne]
    exact inf_le_right
  have hc := omega_center_of_fixed_supplement D d.E d.le_module
    d.fixed_supplement hfixed d.fixed_plane
  exact ⟨hc.1, hc.2.1⟩

end At
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
