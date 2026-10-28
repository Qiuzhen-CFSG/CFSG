module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.Representatives
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.Quasithin.EvenCharacteristic

/-!
# The representative line in the central plane

A nontrivial normal subgroup of the two-group S meets Z(S). This makes the
intersection of the definite plane with C_V(S) nontrivial. If the intersection
had order four, the plane would equal C_V(S). An automorphism preserving V
and S but interchanging the disjoint definite planes rules this out. Thus the
intersection has order two, as needed by `exists_fixed_line_generator`.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, the plane setup
and 15.3.8 on printed p.1122; the choice of v in 15.3.38, p.1136.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
variable {G : Type*} [Group G]

/-- The four-element fixed plane meets either interchanged definite plane
in a line. Nontriviality uses the center theorem for the two-group S; the
interchange excludes a four-element intersection. -/
theorem fixed_plane_intersection_card_two [Finite G]
    (S V W₁ W₂ : Subgroup G) (hS : IsPGroup 2 S)
    (hWS : W₁ ≤ S) (hWV : W₁ ≤ V)
    (hSW : S ≤ normalizer (W₁ : Set G))
    (hW : Nat.card W₁ = 4) (hZ : Nat.card (fixedPlane V S) = 4)
    (hdis : Disjoint W₁ W₂)
    (e : G ≃* G) (hSe : S.map e.toMonoidHom = S)
    (hVe : V.map e.toMonoidHom = V) (hWe : W₁.map e.toMonoidHom = W₂) :
    Nat.card (fixedPlane V S ⊓ W₁ : Subgroup G) = 2 := by
  let Z := fixedPlane V S
  let A := W₁.subgroupOf S
  let : A.Normal := normal_subgroupOf_of_le_normalizer hSW
  have hA : A ≠ ⊥ := by
    intro he
    have hc : Nat.card A = 4 := (Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv).trans hW
    rw [he] at hc
    norm_num at hc
  have hZA : center S ⊓ A ≠ ⊥ := center_inf_ne_bot_of_normal hS A hA
  obtain ⟨z, hz, hz1⟩ := (center S ⊓ A).bot_or_exists_ne_one.resolve_left hZA
  have hzZ : (z : G) ∈ Z := by
    refine ⟨hWV hz.2, ?_⟩
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hz.1 ⟨s, hs⟩)
  have hline : Z ⊓ W₁ ≠ ⊥ := by
    intro he
    have hz' : (z : G) ∈ Z ⊓ W₁ := ⟨hzZ, hz.2⟩
    rw [he, mem_bot] at hz'
    exact hz1 (Subtype.ext hz')
  have hZe : Z.map e.toMonoidHom = Z := by
    change (V ⊓ centralizer (S : Set G)).map e.toMonoidHom = _
    rw [map_inf _ _ _ e.injective, Theory.Quasithin.map_centralizer, hSe, hVe]
    rfl
  have hne4 : Nat.card (Z ⊓ W₁ : Subgroup G) ≠ 4 := by
    intro hc
    have hLW : Z ⊓ W₁ = W₁ := eq_of_le_of_card_ge inf_le_right (by omega)
    have hWZ : W₁ ≤ Z := hLW ▸ inf_le_left
    have hWZeq : W₁ = Z := eq_of_le_of_card_ge hWZ (by exact le_of_eq (hZ.trans hW.symm))
    have hW₂ : W₂ = Z := by rw [← hWe, hWZeq, hZe]
    have hbot : W₁ = ⊥ := by
      have hd := hdis
      rw [hW₂, ← hWZeq] at hd
      exact disjoint_self.mp hd
    rw [hbot] at hW
    norm_num at hW
  have hd : Nat.card (Z ⊓ W₁ : Subgroup G) ∣ 2 ^ 2 := by
    simpa [hW] using card_dvd_of_le (inf_le_right : Z ⊓ W₁ ≤ W₁)
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · have hc : Nat.card (Z ⊓ W₁ : Subgroup G) = 1 := by simpa using he
    exact (hline ((card_eq_one).mp hc)).elim
  · simpa using he
  · exact (hne4 (by simpa using he)).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
