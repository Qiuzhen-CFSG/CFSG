module
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.CyclicSylowAction

/-!
# TI conjugates centralized by fixed commutators

A nontrivial centralizing intersection forces equal-order elementary TI
conjugates to commute. When a conjugate contains an element a, TI puts C(a)
in its normalizer. A cyclic Sylow action then places the derived subgroup
of any two-subgroup of C(a) in the full conjugate centralizer.

This is the TI-pair step of Aschbacher–Smith, I.6.2, applied in 2.4.21, p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

theorem IsTISubgroup.conjugate_le_centralizer_of_inf_ne_bot
    (Z : Subgroup G) [IsElementaryAbelian 2 Z] (hZ : IsTISubgroup Z)
    (g : G) (hc : Z ⊓ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) ≠ ⊥) :
    Z.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) := by
  let E := Z.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  rcases hZ.eq_or_disjoint_conjugate g with he | hd
  · rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ti_pair_commute_of_full_normalizer E Z hd (hZ.map_equiv (MulAut.conj g)) hZ
    (card_map_of_injective (MulAut.conj g).injective)
    (ti_pair_full_normalizer_of_centralizer_ne_bot E Z hd hZ hc)

theorem IsTISubgroup.commutator_le_conjugate_centralizer_of_sylow_action
    (Z I : Subgroup G) (hZ : IsTISubgroup Z) (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ normalizer (Z : Set G))
    (hc : IsCyclic ((Z.normalizerMonoidHom.comp (inclusion hP)).range))
    (hI : IsPGroup 2 I) (g a : G)
    (ha : a ∈ Z.map (MulAut.conj g).toMonoidHom) (ha1 : a ≠ 1)
    (hIc : I ≤ centralizer ({a} : Set G)) :
    ⁅I,I⁆ ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
  let e := MulAut.conj g
  have hz : e.symm a ∈ Z := by
    obtain ⟨z,hz,rfl⟩ := ha
    change e.symm (e z) ∈ Z
    rw [MulEquiv.symm_apply_apply]
    exact hz
  have hz1 : e.symm a ≠ 1 := by
    intro he
    apply ha1
    exact e.injective (by simpa using congrArg e he)
  have hi : I.map e.symm.toMonoidHom ≤ centralizer ({e.symm a} : Set G) := by
    have hh := (map_mono (f := e.symm.toMonoidHom) hIc).trans
      (map_centralizer_le_centralizer_image ({a} : Set G) e.symm.toMonoidHom)
    simpa only [Set.image_singleton,MulEquiv.coe_toMonoidHom] using hh
  have hcomm := Theory.GroupTheory.normalizer_commutator_le_centralizer_of_sylow_action
    Z P hP hc (I.map e.symm.toMonoidHom) (hI.map e.symm.toMonoidHom)
    (hi.trans (hZ.centralizer_le_normalizer hz hz1))
  have hback : (I.map e.symm.toMonoidHom).map e.toMonoidHom = I := by
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; exact e.apply_symm_apply x
    rw [he,map_id]
  have hh := (map_mono (f := e.toMonoidHom) hcomm).trans
    (map_centralizer_le_centralizer_image (Z : Set G) e.toMonoidHom)
  rwa [map_commutator,hback] at hh

/-- A nontrivial part of the original TI subgroup inside a centralizing
commutator forces the entire conjugate to centralize it. -/
theorem IsTISubgroup.mem_centralizer_of_derived_fixed
    (Z I : Subgroup G) [IsElementaryAbelian 2 Z] (hZ : IsTISubgroup Z)
    (g a : G) (ha : a ∈ Z.map (MulAut.conj g).toMonoidHom)
    (hfixed : Z ⊓ centralizer ({a} : Set G) ≠ ⊥)
    (hd : Z ⊓ centralizer ({a} : Set G) ≤ ⁅I,I⁆)
    (hc : ⁅I,I⁆ ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G)) :
    a ∈ centralizer (Z : Set G) := by
  have hn : Z ⊓ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) ≠ ⊥ :=
    ne_bot_of_le_ne_bot hfixed (le_inf inf_le_left (hd.trans hc))
  exact hZ.conjugate_le_centralizer_of_inf_ne_bot Z g hn ha
end CFSG.Quasithin.ChapterI.Section06To08

