module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.NativeWeyl
public import Theory.GroupTheory.Amalgam.RankTwoTransport

/-!
# The pure inner extension of a native marked pair

Conjugation realizes any centre-free group as its inner automorphism group.
Its marked parabolics and their entire intersection form a source extension
with no outer part. All three comparison maps are the same conjugation map,
including when the native middle is only propositionally the intersection.
Consequently the whole middle of any completion is its native middle image.

This is the pure-inner case of Aschbacher–Smith F.4.3, printed p.274, used
in the exact marked lifting argument for 5.3.2, printed p.659. It does not
identify an external source completion or remove an outer defect there.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter5.UnitaryNativeLift
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary

variable {B : Type*} [Group B] (P Q : Subgroup B)

/-- The extension containing exactly the inner automorphisms. -/
def pure : SourceExtension P Q where
  carrier := inner B
  left := P.map MulAut.conj
  right := Q.map MulAut.conj
  left_le := Subgroup.map_le_range _ _
  right_le := Subgroup.map_le_range _ _
  contains_inner := le_rfl
  preserves_types := by
    rintro a ⟨b, rfl⟩
    exact ⟨⟨b, rfl⟩, ⟨b, rfl⟩⟩
  left_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  right_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  factor := by
    rintro a ⟨b, rfl⟩
    exact ⟨b, 1, ⟨one_mem _, one_mem _⟩, (mul_one _).symm⟩

namespace Pure
variable (hi : Function.Injective (MulAut.conj : B →* MulAut B))
include hi

/-- The native group, with its literal conjugation map, is the pure carrier. -/
def baseEquiv : B ≃* (pure P Q).carrier := MonoidHom.ofInjective hi

@[simp] theorem baseEquiv_val (b : B) :
    (baseEquiv P Q hi b).val = MulAut.conj b := rfl

theorem middle_eq : (pure P Q).middle = (P ⊓ Q).map MulAut.conj :=
  (Subgroup.map_inf P Q MulAut.conj hi).symm

/-- A comparison retaining the original middle and both inclusion maps. -/
def comparison (D : Subgroup B) (hP : D ≤ P) (hQ : D ≤ Q)
    (hD : P ⊓ Q = D) :
    RankTwoAmalgam.Iso (.ofSubgroups P D Q hP hQ) (pure P Q).amalgam where
  left := P.equivMapOfInjective MulAut.conj hi
  right := Q.equivMapOfInjective MulAut.conj hi
  middle := (D.equivMapOfInjective MulAut.conj hi).trans
    (MulEquiv.subgroupCongr (by rw [← hD, ← middle_eq P Q hi]))
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

@[simp] theorem comparison_left_val (D : Subgroup B) (hP : D ≤ P) (hQ : D ≤ Q)
    (hD : P ⊓ Q = D) (x : P) :
    ((comparison P Q hi D hP hQ hD).left x).val = MulAut.conj x.val := rfl

@[simp] theorem comparison_middle_val (D : Subgroup B) (hP : D ≤ P) (hQ : D ≤ Q)
    (hD : P ⊓ Q = D) (x : D) :
    ((comparison P Q hi D hP hQ hD).middle x).val = MulAut.conj x.val := rfl

@[simp] theorem comparison_right_val (D : Subgroup B) (hP : D ≤ P) (hQ : D ≤ Q)
    (hD : P ⊓ Q = D) (x : Q) :
    ((comparison P Q hi D hP hQ hD).right x).val = MulAut.conj x.val := rfl

theorem nativeMiddle_surjective : Function.Surjective (pure P Q).nativeMiddle := by
  intro d
  have hd : d.val ∈ (P ⊓ Q).map MulAut.conj := middle_eq P Q hi ▸ d.property
  obtain ⟨b, hb, he⟩ := hd
  exact ⟨⟨b, hb⟩, Subtype.ext he⟩

/-- There is no outer part in the middle of a pure-inner completion. -/
theorem innerMiddle_range {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion (pure P Q).amalgam (G := M)) :
    ((pure P Q).innerMiddle c).range = c.middle.range := by
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    exact ⟨(pure P Q).nativeMiddle b, rfl⟩
  · rintro _ ⟨d, rfl⟩
    obtain ⟨b, rfl⟩ := nativeMiddle_surjective P Q hi d
    exact ⟨b, rfl⟩

/-- Generation of the inner images is exactly native generation. -/
theorem endpoints_generate_iff :
    (pure P Q).left ⊔ (pure P Q).right = (pure P Q).carrier ↔ P ⊔ Q = ⊤ := by
  constructor
  · intro h
    apply Subgroup.map_injective hi
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map]
    exact h
  · exact (pure P Q).endpoints_generate

end Pure
end CFSG.Quasithin.Chapter5.UnitaryNativeLift
