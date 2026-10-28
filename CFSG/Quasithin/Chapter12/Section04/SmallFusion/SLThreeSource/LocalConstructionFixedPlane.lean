module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The exact fixed plane of the local centralizer

For the invariant four-plane E, the subgroup R=C_T(E) has index two in T.
Intersecting R with L gives an even-order image in the marked SL₃(2): the
image of T∩L is Sylow of order eight, and the index can decrease by at most
two. Choose an involution in that image. Its fixed space on V has dimension
two by B.4.8, so the fixed space of R is exactly E.

Only the image is required to have order two; its lift in L need not be an
involution. All centralizers are taken in the original ambient group.
Source: Aschbacher–Smith, B.4.8(2), p.91, used in 12.4.6, p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- A subgroup of index two in T fixes exactly the invariant four-plane. -/
theorem invariant_plane_fixed_space (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (E : Subgroup G) (hEV : E ≤ V) (hEc : Nat.card E = 4)
    (hi : ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2) :
    V ⊓ centralizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) = E := by
  let _ := D.elementary
  let R := (T : Subgroup G) ⊓ centralizer (E : Set G)
  let q : L →* BinaryLinearThree.Group :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    ext.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  obtain ⟨P, hP⟩ := Chapter1.Terminal.sylow_inf_of_normalizes T L hTL
  let S := P.mapSurjective hq
  have hSc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  let f : P →* T := {
    toFun := fun p => ⟨p.val, (show (p.val : G) ∈ (T : Subgroup G) ⊓ L from
      hP ▸ mem_map_of_mem L.subtype p.property).1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let C := (R.subgroupOf (T : Subgroup G)).comap f
  let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hCi : C.index ≤ 2 := by
    have hd : C.index ∣ 2 := by
      rw [show C.index = (R.subgroupOf (T : Subgroup G)).relIndex f.range from index_comap _ _]
      exact (relIndex_dvd_index_of_normal _ _).trans hi.dvd
    exact Nat.le_of_dvd (by decide) hd
  let fA : P →* BinaryLinearThree.Group := q.comp (P : Subgroup L).subtype
  have hrange : fA.range = (S : Subgroup BinaryLinearThree.Group) := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  let B := C.map fA
  have hBS : B ≤ S := hrange ▸ map_le_range fA C
  have hBi : B.relIndex S ≤ 2 := by
    have he : B.relIndex S = (C ⊔ fA.ker).index := by
      rw [← hrange, ← index_comap, comap_map_eq]
    rw [he]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)
      (index_dvd_of_le (le_sup_left : C ≤ C ⊔ fA.ker))).trans hCi
  have hBc : Nat.card B * B.relIndex S = 8 := by
    have hh := (B.subgroupOf (S : Subgroup BinaryLinearThree.Group)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv] at hh
    exact hh.trans hSc
  have hpB : IsPGroup 2 B := (P.isPGroup'.to_subgroup C).map fA
  have hBne : Nat.card B ≠ 1 := by intro he; rw [he, one_mul] at hBc; omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    (hpB.card_eq_or_dvd.resolve_left hBne)
  obtain ⟨p, hp, hpa⟩ := a.property
  have hpR : ((p : L) : G) ∈ R := hp
  have hao : orderOf (a : BinaryLinearThree.Group) = 2 := (orderOf_coe a).trans ha
  let W := V ⊓ centralizer (R : Set G)
  let F := Representation.BinaryOffender.fixedSpace ext.action (zpowers (a : BinaryLinearThree.Group))
  have hwF (w : W) : Additive.ofMul (⟨w, w.property.1⟩ : V) ∈ F := by
    rw [Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [← hpa]
    change ((ext.action (q (p : L)) (Additive.ofMul ⟨w, w.property.1⟩)).toMul : G) = w
    exact (ext.conjugation (p : L) (Additive.ofMul ⟨w, w.property.1⟩)).trans
      (mul_inv_eq_iff_eq_mul.mpr (w.property.2 p.val hpR))
  let i : W → F := fun w => ⟨Additive.ofMul ⟨w, w.property.1⟩, hwF w⟩
  have hinj : Function.Injective i := by
    intro w x he
    exact Subtype.ext (congrArg (fun y : F => (y.val.toMul : G)) he)
  have hWc : Nat.card W ≤ 4 := by
    have hh := Nat.card_le_card_of_injective i hinj
    have hdim := (SLThreeCommutatorSource.involution_linear_plane ext hne a hao).2
    have hFc : Nat.card F = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
      rfl
    exact hh.trans_eq hFc
  symm
  apply eq_of_le_of_card_ge (le_inf hEV (le_centralizer_iff.mp
    (show R ≤ centralizer (E : Set G) from inf_le_right)))
  rwa [hEc]

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
