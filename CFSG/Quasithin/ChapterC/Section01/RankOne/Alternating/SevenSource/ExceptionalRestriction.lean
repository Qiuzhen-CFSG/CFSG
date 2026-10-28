module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalNaturalSource
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Restricting the exceptional source to its selected A₅ preimage

The four-dimensional action of the original group is restricted along the
literal subgroup inclusion. Both the centralizer kernel and the natural
coordinates retain the original quotient map. Characteristic two descends
from the ambient group because the selected preimage contains its two-core.

Source: Aschbacher–Smith C.1.24, printed p.131, the subgroup X∞O₂(G).
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB.QuasisimpleSource
local notation "A7" => alternatingGroup (Fin 7)
variable {G : Type*} [Group G] [Finite G]

/-- Keeping the original Baumann image also keeps Thompson movement on
any subgroup which contains the original moved module. -/
theorem selected_thompson_movement_of_baumann
    (T : Sylow 2 G) (U H : Subgroup G) (hUH : U ≤ H)
    (P : Sylow 2 H)
    (hB : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U.subgroupOf H : Set H) := by
  let R := (P : Subgroup H).map H.subtype
  have hBR : ChapterB.baumann (T : Subgroup G) ≤ R := by
    rw [←hB]
    exact map_mono (show ChapterB.baumann (P : Subgroup H) ≤ P from inf_le_left)
  have hJR : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (T : Subgroup G) :=
    (twoSubgroup_thompson_baumann_eq T R (P.isPGroup'.map H.subtype) hBR).1
  have hJP : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    exact hJR
  intro hfix
  apply hJ
  intro j hj u hu
  obtain ⟨x,hx,hxj⟩ := (hJP.symm ▸ hj : j ∈ (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype)
  have he := congrArg Subtype.val (hfix hx ⟨u,hUH hu⟩ hu)
  change u * (x : G) = (x : G) * u at he
  change (x : G) = j at hxj
  rwa [hxj] at he

theorem exceptional_selected_natural_localClass
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (B : Subgroup A7) (H : Subgroup G) (hH : H.map q = B) (hUH : U ≤ H)
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (a : B ≃* SL(2,F.Carrier))
    (p : Additive U ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (b : B) v,
      p (NormalElementaryQuotient.representation U q hq hk b v) =
        specialLinearNatural 2 (a b) (p v))
    (hk2 : IsPGroup 2 (q.ker.subgroupOf H))
    (hf : generalizedFitting G = pCore 2 G) (hQH : pCore 2 G ≤ H)
    (P : Sylow 2 H)
    (hJ : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U.subgroupOf H : Set H)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show ChapterB.baumann (P : Subgroup H) ≤
        pResidual 2 H ⊔ ChapterB.baumann (P : Subgroup H) from le_sup_right)) := by
  let W := U.subgroupOf H
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUH
  let r : H →* B := (q.comp H.subtype).codRestrict B
    (fun h => hH ▸ mem_map_of_mem q h.property)
  let f := a.toMonoidHom.comp r
  have hfs : Function.Surjective f := by
    intro x
    have hb : (a.symm x : A7) ∈ H.map q := by rw [hH]; exact (a.symm x).property
    obtain ⟨h,hh,hhe⟩ := hb
    refine ⟨⟨h,hh⟩,?_⟩
    change a (r ⟨h,hh⟩) = x
    rw [show r ⟨h,hh⟩ = a.symm x from Subtype.ext hhe,a.apply_symm_apply]
  have hfk : f.ker = q.ker.subgroupOf H := by
    ext h
    change a (r h) = 1 ↔ q (h : G) = 1
    constructor
    · intro hh
      exact congrArg Subtype.val (a.injective (hh.trans a.map_one.symm))
    · intro hh
      exact (congrArg a (show r h = 1 from Subtype.ext hh)).trans a.map_one
  have hcentral : f.ker = centralizer (W : Set H) := by
    rw [hfk,hk]
    ext h
    constructor
    · intro hh w hw
      apply Subtype.ext
      exact hh w hw
    · intro hh u hu
      exact congrArg Subtype.val (hh ⟨u,hUH hu⟩ hu)
  let e := subgroupOfEquivOfLe hUH
  let el : Additive W ≃ₗ[ZMod 2] Additive U :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let pH := el.trans p
  have hact (h : H) (v : Additive W) :
      pH (Additive.ofMul (MulAut.conjNormal h v.toMul)) =
        specialLinearNatural 2 (f h) (pH v) := by
    change p (el (Additive.ofMul (MulAut.conjNormal h v.toMul))) =
      specialLinearNatural 2 (a (r h)) (p (el v))
    rw [←he (r h) (el v)]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U q hq hk (h : G) (el v)).symm
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le H
        (by rw [←hf]; exact centralizer_generalizedFitting_le G) hQH)
  exact CFSG.Quasithin.ChapterC.RankOne.SevenSource.exceptional_natural_inLocalClass
    F hF P W f hfs hcentral (hfk.symm ▸ hk2) hfit hJ pH hact

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
