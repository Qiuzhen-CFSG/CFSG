module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.CommutatorRows
public import Theory.GroupTheory.TwoPlaneCover
public import Theory.GroupAction.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient

/-!
# Sylow centers of central double covers of PSL₃(4)

The elementary root planes of the unipotent Sylow subgroup lift to elementary
subgroups. They generate the full Sylow preimage, so its center is the preimage
of the unipotent center. It is elementary of order eight, whereas the full
Sylow subgroup has order 128. The construction retains the original cover map.

Source: Aschbacher--Smith I.2.2(3b) and 14.3.22, printed pp.409--410 and 999.
This supplies the central-cover exclusion in OppositeCentralizer.RecognitionCover.
-/

public section
open Subgroup
namespace Matrix.PSL3Four
open PSL3.LinearThree PSL3Even.UnipotentGeometry
variable {E : Type*} [Group E] [Finite E]

private theorem card_comap_surjective {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (q : A →* B) (hq : Function.Surjective q) (H : Subgroup B) :
    Nat.card (H.comap q) = Nat.card H * Nat.card q.ker := by
  rw [card_eq_card_quotient_mul_card_subgroup (q.ker.subgroupOf (H.comap q)),
    card_quotient_subgroupOf_comap_eq q hq H,
    Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap q H)).toEquiv]

/-- In a central double cover of PSL₃(4), the elementary root planes lift
and their intersection gives an elementary Sylow center of order eight. -/
theorem double_cover_sylow_center
    (q : E →* PSL) (hq : Function.Surjective q)
    (hc : q.ker ≤ center E) (hk : Nat.card q.ker = 2) (P : Sylow 2 E) :
    Nat.card P = 128 ∧ IsElementaryAbelian 2 (center P) ∧ Nat.card (center P) = 8 := by
  have hker : IsPGroup 2 q.ker := IsPGroup.of_card (n := 1) hk
  have hs (x : E) (hx : x ∈ q.ker) : x^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : q.ker))
    rw [hk] at hh
    exact congrArg q.ker.subtype hh
  let S := (unipotentSylow F (by decide : 0<2) (by simpa using card_F)).comapOfKerIsPGroup
    q hker (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  let eU := unipotentEquiv F
  let f : S →* U F := eU.symm.toMonoidHom.comp
    (q.restrict (fun _ hx => hx))
  have he (x : S) : projective F (f x) = q x := by
    exact congrArg (unipotent F).subtype (eU.apply_symm_apply ⟨q x,x.property⟩)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨x,hx⟩ := hq (projective F u)
    have hxS : x ∈ S := by
      change q x ∈ unipotent F
      rw [hx,←projective_range]
      exact ⟨u,rfl⟩
    refine ⟨⟨x,hxS⟩,?_⟩
    apply projective_injective F
    exact (he ⟨x,hxS⟩).trans hx
  have hfk : f.ker = q.ker.subgroupOf (S : Subgroup E) := by
    ext x
    change f x=1 ↔ q x=1
    rw [←he,←map_one (projective F),(projective_injective F).eq_iff]
  have hkc : Nat.card f.ker = 2 := by
    rw [hfk]
    change Nat.card (q.ker.subgroupOf ((unipotent F).comap q)) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap q (unipotent F))).toEquiv,hk]
  have hplanes (V : Subgroup (U F)) [IsElementaryAbelian 2 V] :
      IsElementaryAbelian 2 (V.comap f) := by
    let A := V.map (projective F)
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    let := ElementaryParabolic.elementary_comap q hq hc hs A
    let j : V.comap f →* A.comap q :=
      ((S : Subgroup E).subtype.comp (V.comap f).subtype).codRestrict _ (by
        intro x
        exact ⟨f x,x.property,he x⟩)
    exact IsElementaryAbelian.of_injective j (fun x y hh =>
      Subtype.ext (Subtype.ext (show ((x : S) : E) = ((y : S) : E) from congrArg (fun t : A.comap q => (t : E)) hh)))
  let := hplanes (V₁ F)
  let := hplanes (V₂ F)
  have hZ : center S = (center (U F)).comap f :=
    TwoPlaneCover.center_eq_comap f hf (V₁ F) (V₂ F) planes_generate center_le_planes
  have hZe : IsElementaryAbelian 2 (center S) := by
    rw [hZ]
    exact IsElementaryAbelian.of_injective (inclusion
      (comap_mono (center_le_planes.trans inf_le_left))) (inclusion_injective _)
  have hZc : Nat.card (center S) = 8 := by
    rw [hZ,card_comap_surjective f hf,←Z_eq_center,card_Z,card_F,hkc]
  have hSc : Nat.card S = 128 := by
    change Nat.card ((unipotent F).comap q) = 128
    rw [card_comap_surjective q hq,card_unipotent,card_F,hk]
    norm_num
  let eSP := Sylow.equiv S P
  let eZ := centerCongr eSP
  let := hZe
  exact ⟨(Nat.card_congr eSP.toEquiv).symm.trans hSc,
    IsElementaryAbelian.of_surjective eZ.toMonoidHom eZ.surjective,
    (Nat.card_congr eZ.toEquiv).symm.trans hZc⟩
end Matrix.PSL3Four
