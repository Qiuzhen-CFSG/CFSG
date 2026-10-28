module

public import Theory.Quasithin.EvenCharacteristic
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# An incompatible construction in the printed final paragraph of 15.3.38

On printed p.1137 (Aschbacher--Smith, manuscript of 1 March 2004), the earlier
paragraph identifies `C_G(V₁) = L⟨τf⟩`, where `Z(L)` is a four-group,
`L/Z(L)` is L₃(4), and `τf` is an outer involution. Thus the relative index
of `L` is two. The actual PSL₃(4) cardinality gives `|L| = 80640` and
`|C_G(V₁)| = 161280`, not divisible by 27.

The last paragraph claims a conjugate `U₁` of `V₁` for which
`O(C_G(f)(U₁))` is extraspecial of order 27. That subgroup would lie in
`C_G(U₁)`, whose order equals `|C_G(V₁)|`, contradicting Lagrange's theorem.
The proof below checks this incompatibility with an actual PSL₃(4)
isomorphism and actual conjugation, without any model labels or new axioms.

This identifies a gap in the printed proof, not a counterexample to the
statement of 15.3.38. The order-27 assertion must not be requested as an
intrinsic fact of the cover. `JointCentralizer` gives the corrected E₉
construction from the earlier local data. The remaining field-component
argument still requires proof.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup
variable {G : Type*} [Group G]

/-- The earlier centralizer description excludes the order-27 subgroup
claimed in the printed final paragraph, for every conjugate of `V`. -/
theorem no_order_27_in_conjugate_plane_centralizer [Finite G] (V L : Subgroup G)
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2)
    (hZ : Nat.card (center L) = 4)
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) (g : G)
    (B : Subgroup G) (hB : Nat.card B = 27) :
    ¬ B ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hquot : Nat.card (L ⧸ center L) = 20160 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hL : Nat.card L = 80640 := by
    have he := (center L).card_mul_index
    rw [hZ, index_eq_card, hquot] at he
    omega
  let C := centralizer (V : Set G)
  have hC : Nat.card C = 161280 := by
    have he := (L.subgroupOf C).card_mul_index
    have hcard : Nat.card (L.subgroupOf C) = Nat.card L :=
      Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv
    rw [hcard, hL] at he
    change L.relIndex C = 2 at hindex
    change 80640 * L.relIndex C = Nat.card C at he
    rw [hindex] at he
    omega
  have hmap := Theory.Quasithin.map_centralizer (MulAut.conj g) V
  have hc : Nat.card (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) =
      Nat.card C := by
    rw [← hmap]
    exact (Nat.card_congr ((MulAut.conj g).subgroupMap C).toEquiv).symm
  intro hle
  have hd := card_dvd_of_le hle
  rw [hB, hc, hC] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
