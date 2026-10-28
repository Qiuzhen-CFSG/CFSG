module
public import Theory.SpecificGroups.PSL3Two.WreathCubicRadical

/-!
# Independent coordinates of cubic-normalized binary wreath subgroups

Let U be a two-subgroup in the base of SL₃(2) wr C₂, normalized by a
cubic plane P. Each coordinate of every element of U belongs to U separately.
Conjugate P to the two standard independent cubics. Elementarity of U and
the fixed-point-free cubic action on each coordinate express a coordinate
projection as the product of two cubic conjugates. Wreath conjugation then
transports the statement back to the original marking.

The finite identity checks only the 168-element SL₃(2) factor. The actual
Chapter 10 consumer splits the containing core into centralizers of the two
original natural-module factors, before passing to its Frattini section.
Source: Aschbacher--Smith, 10.2.4--5, printed pp.747--748; binary parabolic
geometry I.5.4, printed p.420. Matrix-model attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Matrix.PSL3Two.WreathPair.CubicSplitting
open Matrix.PSL3Two.WreathPair
private def cubic : SL := ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩
private theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
private theorem cubic_order : orderOf cubic = 3 := by
  exact orderOf_eq_prime (by decide +kernel) cubic_ne_one
private theorem cubic_centralizer_cube : ∀ a : SL, a * cubic = cubic * a → a ^ 3 = 1 := by
  decide +kernel

private def planeHom : (Bit → zpowers cubic) →* Actor where
  toFun a := ⟨fun i => (a i : SL),1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

private theorem planeHom_injective : Function.Injective planeHom := by
  intro a b he
  funext i
  exact Subtype.ext (congrArg (fun w : Actor => w.left i) he)

private theorem plane_card : Nat.card planeHom.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective planeHom_injective).toEquiv.symm,
    Nat.card_fun,Nat.card_zpowers,cubic_order]
  change 3 ^ Nat.card (ZMod 2) = 9
  rw [Nat.card_zmod]
  norm_num

private def planeSylow : Sylow 3 Actor := Sylow.ofCard planeHom.range (by
  rw [plane_card,RegularWreathProduct.card,card_SL]
  change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
  rw [Nat.card_zmod]
  decide +kernel)


@[expose] def coordinatePart (u : Actor) (i : Bit) : Actor :=
  ⟨Pi.mulSingle i (u.left i),1⟩

private theorem cubic_norm : ∀ u : SL, u ^ 2 = 1 →
    u * (cubic * u * cubic⁻¹) = (cubic * u * cubic⁻¹) * u →
    (cubic * u * cubic⁻¹) * (cubic ^ 2 * u * (cubic ^ 2)⁻¹) = u := by
  decide +kernel

private theorem plane_coordinatePart_mem (U : Subgroup Actor)
    [IsElementaryAbelian 2 U]
    (hr : ∀ u ∈ U, u.right = 1)
    (hn : planeHom.range ≤ normalizer (U : Set Actor))
    (u : Actor) (hu : u ∈ U) (i : Bit) : coordinatePart u i ∈ U := by
  classical
  let a : Actor := planeHom (Pi.mulSingle i ⟨cubic,mem_zpowers cubic⟩)
  have ha : a ∈ normalizer (U : Set Actor) := hn ⟨_,rfl⟩
  have hu1 : a * u * a⁻¹ ∈ U := (mem_normalizer_iff.mp ha u).mp hu
  have hu2 : a ^ 2 * u * (a ^ 2)⁻¹ ∈ U :=
    (mem_normalizer_iff.mp ((normalizer (U : Set Actor)).pow_mem ha 2) u).mp hu
  have he : (a * u * a⁻¹) * (a ^ 2 * u * (a ^ 2)⁻¹) = coordinatePart u i := by
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
    have hc : u * (a*u*a⁻¹) = (a*u*a⁻¹) * u :=
      congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) ⟨_,hu1⟩)
    apply RegularWreathProduct.ext
    · funext j
      by_cases hj : j=i
      · subst j
        have hs' : (u.left i) ^ 2 = 1 := by
          simpa [pow_two,hr u hu] using congrArg (fun w : Actor => w.left i) hs
        have hc' : u.left i * (cubic * u.left i * cubic⁻¹) =
            (cubic * u.left i * cubic⁻¹) * u.left i := by
          simpa [a,planeHom,hr u hu] using congrArg (fun w : Actor => w.left i) hc
        simpa [a,planeHom,coordinatePart,pow_two,hr u hu,mul_assoc] using
          cubic_norm (u.left i) hs' hc'
      · have hs' : u.left j * u.left j = 1 := by
          simpa [pow_two,hr u hu] using congrArg (fun w : Actor => w.left j) hs
        simp [a,planeHom,coordinatePart,Pi.mulSingle_apply,hj,pow_two,hr u hu,hs']
    · simp [a,planeHom,coordinatePart,pow_two,hr u hu]
  exact he ▸ U.mul_mem hu1 hu2

private theorem coordinatePart_conj (g u : Actor) (hr : u.right = 1) (i : Bit) :
    coordinatePart (g*u*g⁻¹) (g.right*i) = g * coordinatePart u i * g⁻¹ := by
  classical
  apply RegularWreathProduct.ext
  · funext j
    by_cases hj : j = g.right*i
    · subst j
      simp [coordinatePart,hr]
    · have hj' : g.right⁻¹ * j ≠ i := by
        intro he
        apply hj
        calc j = g.right*(g.right⁻¹*j) := by group
             _ = g.right*i := by rw [he]
      simp [coordinatePart,Pi.mulSingle_apply,hr,hj,hj']
  · simp [coordinatePart,hr]

/-- Each coordinate of the original two-subgroup occurs independently. -/
theorem coordinatePart_mem (P U : Subgroup Actor) (hP : Nat.card P = 9)
    (hU : IsPGroup 2 U) (hr : ∀ u ∈ U, u.right = 1)
    (hn : P ≤ normalizer (U : Set Actor)) (u : Actor) (hu : u ∈ U) (i : Bit) :
    coordinatePart u i ∈ U := by
  let S : Sylow 3 Actor := Sylow.ofCard P (by
    rw [hP,RegularWreathProduct.card,card_SL]
    change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
    rw [Nat.card_zmod]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor S planeSylow
  let e := MulAut.conj g
  have he : P.map e.toMonoidHom = planeHom.range := congrArg Sylow.toSubgroup hg
  let U' := U.map e.toMonoidHom
  have hr' : ∀ x ∈ U', x.right = 1 := by
    rintro _ ⟨x,hx,rfl⟩
    simp [e,MulAut.conj_apply,hr x hx]
  have hn' : planeHom.range ≤ normalizer (U' : Set Actor) :=
    he ▸ (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  let : IsElementaryAbelian 2 U' :=
    two_base_normalized_cubic_plane_elementary _ U' plane_card (hU.map _) hr' hn'
  have hh := plane_coordinatePart_mem U' hr' hn'
    (e u) (mem_map_of_mem e.toMonoidHom hu) (g.right*i)
  change coordinatePart (g*u*g⁻¹) (g.right*i) ∈ U' at hh
  rw [coordinatePart_conj g u (hr u hu) i] at hh
  obtain ⟨v,hv,hve⟩ := hh
  exact (e.injective hve) ▸ hv

end Matrix.PSL3Two.WreathPair.CubicSplitting
