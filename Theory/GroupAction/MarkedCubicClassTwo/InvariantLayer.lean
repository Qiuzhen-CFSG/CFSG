module

public import Theory.GroupAction.MarkedCubicClassTwo.LowerCentral
public import Theory.GroupAction.MarkedCubicClassTwo.Defs
public import Theory.GroupAction.MarkedCubicClassTwo.InvariantLayer.Characters

/-!
# An invariant cubic quotient of the third lower-central layer

Write `V = γ₃(P)` and `W = γ₄(P)`. If `V` is nontrivial in a finite three-group,
then its image in `P/W` is nontrivial and central. Two commuting involutions
therefore preserve a subgroup of index three in this image: use a common sign
character of the abelian image. Centrality makes the kernel normal in `P/W`,
and its pullback is the required normal invariant subgroup `N` of `P`.

The order of the image of `V` in the literal quotient `P/N` is checked using
relative index and the surjection `V → V.map (QuotientGroup.mk' W)`.

Source: Aschbacher–Smith F.6.16, printed p.308 (PDF p.319), combined manuscript
of 1 March 2004. This is the invariant-subgroup step in its class-three
contradiction; cubic markings and fixed-subgroup bounds are not needed here.
-/

public section

open Subgroup

namespace MarkedCubicClassTwo
variable {P : Type*} [Group P]

private def layerRestrict {Q : Type*} [Group Q] (H : Subgroup Q)
    (c : MulAut Q) (hc : H.map c.toMonoidHom = H) : MulAut H :=
  (c.subgroupMap H).trans (MulEquiv.subgroupCongr hc)

/-- The invariant index-three third-layer quotient used in F.6.16. -/
theorem exists_invariant_third_layer_quotient [Finite P] (hP : IsPGroup 3 P)
    (a b : MulAut P) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hV : (⊤ : Subgroup P).lowerCentralSeries 2 ≠ ⊥) :
    ∃ (N : Subgroup P) (hN : N.Normal),
      let := hN
      (⊤ : Subgroup P).lowerCentralSeries 3 ≤ N ∧
      N ≤ (⊤ : Subgroup P).lowerCentralSeries 2 ∧
      Nat.card (((⊤ : Subgroup P).lowerCentralSeries 2).map (QuotientGroup.mk' N)) = 3 ∧
      N.map a.toMonoidHom = N ∧ N.map b.toMonoidHom = N := by
  let V := (⊤ : Subgroup P).lowerCentralSeries 2
  let W := (⊤ : Subgroup P).lowerCentralSeries 3
  let q := QuotientGroup.mk' W
  let H := V.map q
  have hWV : W ≤ V := Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
  have hH : H ≠ ⊥ := third_layer_mod_fourth_nontrivial hP hV
  have hHZ : H ≤ center (P ⧸ W) := third_layer_mod_fourth_le_center
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  let : CommGroup H :=
    { __ := (inferInstance : Group H)
      mul_comm := fun x y => Subtype.ext ((mem_center_iff.mp (hHZ y.property)) x) }
  have hHP : IsPGroup 3 H := (hP.to_quotient W).to_subgroup H
  have hWc (c : MulAut P) : W.map c.toMonoidHom = W :=
    characteristic_iff_map_eq.mp inferInstance c
  let lift (c : MulAut P) : MulAut (P ⧸ W) := QuotientGroup.congr W W c (hWc c)
  have hlift (c : MulAut P) (x : P) : lift c (q x) = q (c x) :=
    QuotientGroup.congr_mk' W W c (hWc c) x
  have hHc (c : MulAut P) : H.map (lift c).toMonoidHom = H := by
    change (V.map q).map (lift c).toMonoidHom = V.map q
    rw [map_map, show (lift c).toMonoidHom.comp q = q.comp c.toMonoidHom from
      MonoidHom.ext (hlift c), ← map_map]
    rw [characteristic_iff_map_eq.mp (inferInstance : V.Characteristic) c]
  let rest (c : MulAut P) : MulAut H := layerRestrict H (lift c) (hHc c)
  have hrest (c : MulAut P) (x : H) : (rest c x : P ⧸ W) = lift c x := rfl
  have hsquare (c : MulAut P) (hc : c ^ 2 = 1) : rest c ^ 2 = 1 := by
    have hcc (x : P) : c (c x) = x := DFunLike.congr_fun hc x
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (rest c (rest c x) : P ⧸ W) = x
    rw [hrest, hrest]
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective W (x : P ⧸ W)
    rw [← hy, hlift, hlift, hcc]
  have hcomm : Commute (rest a) (rest b) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (rest a (rest b x) : P ⧸ W) = rest b (rest a x)
    rw [hrest, hrest, hrest, hrest]
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective W (x : P ⧸ W)
    rw [← hy, hlift, hlift, hlift, hlift, show a (b y) = b (a y) from
      DFunLike.congr_fun hab.eq y]
  obtain ⟨U, hUcard, haU, hbU⟩ := InvariantLayer.exists_invariant_index_three hHP
    (rest a) (rest b) (hsquare a ha) (hsquare b hb) hcomm
  let Ubar : Subgroup (P ⧸ W) := U.map H.subtype
  have hUH : Ubar ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let : Ubar.Normal := by
    constructor
    intro x hx g
    have hc := mem_center_iff.mp (hHZ (hUH hx)) g
    simpa only [hc, mul_inv_cancel_right] using hx
  let N : Subgroup P := Ubar.comap q
  let : N.Normal := inferInstanceAs (Ubar.comap q).Normal
  have hWN : W ≤ N := by
    intro x hx
    change q x ∈ Ubar
    rw [show q x = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
    exact Ubar.one_mem
  have hNV : N ≤ V := by
    intro x hx
    have hxH : q x ∈ H := hUH hx
    obtain ⟨y, hy, hyx⟩ := hxH
    have hyxW : y⁻¹ * x ∈ W := QuotientGroup.eq.mp hyx
    simpa only [mul_inv_cancel_left] using V.mul_mem hy (hWV hyxW)
  have hNchar (c : MulAut P) (hc : ∀ x : H, rest c x ∈ U ↔ x ∈ U) :
      N.map c.toMonoidHom = N := by
    have hforward (x : P) (hx : x ∈ N) : c x ∈ N := by
      obtain ⟨y, hy, hyx⟩ := hx
      change q (c x) ∈ Ubar
      refine ⟨rest c y, (hc y).mpr hy, ?_⟩
      exact (hrest c y).trans ((congrArg (lift c) hyx).trans (hlift c x))
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hforward x hx
    · exact (card_map_of_injective c.injective).ge
  refine ⟨N, inferInstance, hWN, hNV, ?_, hNchar a haU, hNchar b hbU⟩
  have hker : N.subgroupOf V = U.comap (q.subgroupMap V) := by
    ext x
    change q (x : P) ∈ U.map H.subtype ↔ q.subgroupMap V x ∈ U
    constructor
    · rintro ⟨y, hy, he⟩
      have hyx : y = q.subgroupMap V x := Subtype.ext he
      exact hyx ▸ hy
    · intro hx
      exact ⟨q.subgroupMap V x, hx, rfl⟩
  calc
    Nat.card (V.map (QuotientGroup.mk' N)) = N.relIndex V := by
      simpa only [QuotientGroup.ker_mk'] using (relIndex_ker V (QuotientGroup.mk' N)).symm
    _ = (U.comap (q.subgroupMap V)).index := by rw [relIndex, hker]
    _ = U.index := U.index_comap_of_surjective (q.subgroupMap_surjective V)
    _ = 3 := hUcard
end MarkedCubicClassTwo
