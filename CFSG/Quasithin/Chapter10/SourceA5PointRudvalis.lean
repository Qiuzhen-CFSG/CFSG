module
public import CFSG.Quasithin.Chapter10.SourceA5PointCoreCenter
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.LocalA5

/-!
# Excluding the actual Rudvalis local A₅ row

Let B be the image of the original local component L in I/Z(I). Its two-core
center has at least sixteen elements, while an actual full-Sylow local A₅
subgroup of Rudvalis with two-core order 2¹¹ has two-core center at most two.
The model placement theorem supplies the marked embedding in the actual max6
carrier. Local C-component membership is transported through the literal
central quotient, including the original Sylow image.

This discharges the Ru alternative of Aschbacher–Smith A.3.12(20)/A.3.14 in
source 10.2.9, printed pp.750–751, once the earlier embedding theorem supplies
its genuine local-component premise and two-core order. The conclusion does
not infer that premise from a Rudvalis carrier label.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G} {T : Sylow 2 G}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The actual local image in a Rudvalis central quotient cannot be the Ru row. -/
theorem source_a5_not_rudvalis_local_image
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model) (P : Sylow 2 Rudvalis.Model)
    (hlocal : ((((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map eI.toMonoidHom).subgroupOf
      ((((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map eI.toMonoidHom) ⊔
        (P : Subgroup Rudvalis.Model))).IsSubnormal)
    (hcore : Nat.card (pCore 2
      (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map eI.toMonoidHom)) = 2048) :
    False := by
  let A := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  let B := A.map eI.toMonoidHom
  let f : A ≃* B := A.equivMapOfInjective eI.toMonoidHom eI.injective
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (pCore 2 A) (pCore 2 B) f (pCore_map_iso 2 f)).symm.trans
      (source_a5_containing_center_image_quotient e hLI)
  have hlow := source_a5_marked_core_center_card D e hLI f
  have hsmall := MainConverse.SporadicLocal.RuEven.local_a5_core_center_card_le_two
    P B hlocal eB hcore
  omega

include D in
/-- The Ru row is excluded for the literal image of a full-Sylow local component
in the containing component, without supplying a marked local embedding. -/
theorem source_a5_not_rudvalis_containing_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ ChapterA.Section03.localCComponents S)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model)
    (hcore : Nat.card (pCore 2
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 2048) : False := by
  let q := QuotientGroup.mk' (center I)
  let f := eI.toMonoidHom.comp q
  have hf : Function.Surjective f := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable f.ker := by
    have hk : f.ker = center I := by
      ext x
      change eI (q x) = 1 ↔ x ∈ center I
      rw [←eI.map_one,eI.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  let P := S.mapSurjective hf
  have he : (L.subgroupOf I).map f =
      ((L.subgroupOf I).map q).map eI.toMonoidHom := by rw [map_map]
  have hp : ((S : Subgroup I).map f) = (P : Subgroup Rudvalis.Model) := rfl
  rw [he,hp] at hl
  let g := ((L.subgroupOf I).map q).equivMapOfInjective eI.toMonoidHom eI.injective
  let cg := (g.subgroupMap (pCore 2 ((L.subgroupOf I).map q))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 g))
  have hc : Nat.card (pCore 2 (((L.subgroupOf I).map q).map eI.toMonoidHom)) = 2048 :=
    (Nat.card_congr cg.toEquiv).symm.trans hcore
  exact source_a5_not_rudvalis_local_image D e hLI eI P hl.subnormal hc

end CFSG.Quasithin.Chapter10
