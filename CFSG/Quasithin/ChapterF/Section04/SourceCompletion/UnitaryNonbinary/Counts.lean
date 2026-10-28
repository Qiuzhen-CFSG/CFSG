module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Geometry

/-!
# Counting through full unitary extensions

The common-overlap representative gives bijections on each of the two coset
spaces. The native graph isomorphism preserves valence at each marked type.
For any finite faithful completion, the order bound on the entire extension
then bounds its two coset spaces by the corresponding native coset spaces.
No equality of the two valencies or oddness of the outer degree is used.

This is the algebraic counting bridge in Aschbacher–Smith F.4.13 and F.4.24,
printed pp.280 and287. It does not yet supply the native Hermitian counts or
the short-path and recognition arguments.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁)
variable (hi : Function.Injective (MulAut.conj : B →* MulAut B))

/-- The native-to-extension coset map is onto, separately at each type. -/
theorem cosetMap_surjective (i : Bool) : Function.Surjective (E.cosetMap hi i) := by
  intro q
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b,hb⟩ := E.exists_native_representative a
  exact ⟨b,hb i⟩

/-- The extension changes stabilizers, but not either native coset space. -/
theorem card_coset_eq_native
    (hi : Function.Injective (MulAut.conj : B →* MulAut B)) (i : Bool) :
    Nat.card (E.carrier ⧸ E.family i) =
      Nat.card (B ⧸ nativeFamily (P₀ := P₀) (P₁ := P₁) i) :=
  (Nat.card_congr (Equiv.ofBijective (E.cosetMap hi i)
    ⟨E.cosetMap_injective hi i,E.cosetMap_surjective hi i⟩)).symm

/-- Both unequal native valencies are retained in the full extension. -/
theorem card_neighbors_eq_native
    (hi : Function.Injective (MulAut.conj : B →* MulAut B)) (i : Bool) :
    Nat.card ((graph E.family).neighborSet (base E.family i)) =
      Nat.card ((graph (nativeFamily (P₀ := P₀) (P₁ := P₁))).neighborSet
        (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i)) := by
  have hh := Nat.card_congr ((E.graphIso hi).mapNeighborSet
    (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i))
  change Nat.card ((graph (nativeFamily (P₀ := P₀) (P₁ := P₁))).neighborSet
    (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i)) =
      Nat.card ((graph E.family).neighborSet (E.vertexMap hi
        (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i))) at hh
  rw [E.vertexMap_base hi i] at hh
  exact hh.symm

/-- Whole-overlap covers transfer the valence at each marked type. -/
theorem completion_card_neighbors_eq_native
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (hgen : P₀ ⊔ P₁ = ⊤) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily i)) =
      Nat.card ((graph (nativeFamily (P₀ := P₀) (P₁ := P₁))).neighborSet
        (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i)) := by
  let cc := RankTwoAmalgam.Universal.coverData_of_overlap E.amalgam c hoverlap
  let cm := RankTwoAmalgam.Universal.coverData_of_overlap E.amalgam
    (E.completion hgen) (E.completion_overlap hgen)
  let v := base (RankTwoAmalgam.Universal.cosetFamily E.amalgam) i
  have hc := Nat.card_congr (Equiv.ofBijective (cc.hom.mapNeighborSet v) (cc.neighbor_bijective v))
  have hm := Nat.card_congr (Equiv.ofBijective (cm.hom.mapNeighborSet v) (cm.neighbor_bijective v))
  have hcm := hc.symm.trans hm
  change Nat.card ((graph c.cosetFamily).neighborSet (cc.vertex v)) =
    Nat.card ((graph (E.completion hgen).cosetFamily).neighborSet (cm.vertex v)) at hcm
  dsimp only [v] at hcm
  rw [cc.vertex_base,cm.vertex_base,E.completion_family hgen] at hcm
  exact hcm.trans (E.card_neighbors_eq_native hi i)

/-- The full carrier order bound gives the native bound on each coset orbit.
The endpoint order cancels because both completions retain the same marking. -/
theorem completion_card_coset_le_native [Finite B]
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (hgen : P₀ ⊔ P₁ = ⊤) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤
      Nat.card (B ⧸ nativeFamily (P₀ := P₀) (P₁ := P₁) i) := by
  have hlocal : Nat.card (c.cosetFamily i) = Nat.card (E.family i) := by
    rw [← E.completion_family hgen]
    cases i
    · exact c.left_card.trans (E.completion hgen).left_card.symm
    · exact c.right_card.trans (E.completion hgen).right_card.symm
  rw [← E.card_coset_eq_native hi i, ← index_eq_card, ← index_eq_card]
  apply Nat.le_of_mul_le_mul_right _ (Nat.card_pos (α := E.family i))
  calc
    (c.cosetFamily i).index * Nat.card (E.family i) = Nat.card M := by
      rw [← hlocal, index_mul_card]
    _ ≤ Nat.card E.carrier := horder
    _ = (E.family i).index * Nat.card (E.family i) := (E.family i).index_mul_card.symm

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
