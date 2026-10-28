module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow

/-!
# Excluding quaternion sections from dihedral or abelian Sylow geometry

If a finite group has a Sylow two-subgroup that is dihedral or abelian, no
subgroup admits a surjective homomorphism onto `QuaternionGroup 2`. Thus the
conclusion excludes quaternion sections, not merely quaternion subgroups.
The dihedral alternative uses Mathlib's explicit model with arbitrary natural
parameter, without imposing any additional order hypotheses.

A putative surjection remains surjective on a Sylow two-subgroup of its
domain: surjective homomorphisms map Sylow subgroups to Sylow subgroups, and
the quaternion group has order eight. Embed this domain Sylow into an ambient
Sylow and transport it to the Sylow in the hypothesis by conjugacy. In the
abelian case its image is commutative. In the dihedral case, two rotations
commute, while every reflection squares to one. A kernel-checked calculation
in the eight-element quaternion model shows that every element squaring to
one is central, so every pair of image elements again commutes. The explicit
elements `a 1` and `xa 0` of the quaternion group do not commute, giving the
contradiction in both cases.

This supplies the final elementary obstruction in Alperin–Brauer–Gorenstein,
Chapter II, Section 5, Lemma 5, article p.48 / PDF p.49, transcribed in
`refs/latex/alperin-brauer-gorenstein-pages/page-049.tex`. The result and its
proof depend only on Mathlib, independently of the ABG and Stellmacher APIs.
-/

private theorem quaternion_square_one_central :
    ∀ x y : QuaternionGroup 2, x * x = 1 → x * y = y * x := by decide

private theorem quaternion_noncommuting :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide

private theorem dihedral_image_commutes {B : Type*} [Group B] {n : ℕ}
    (embedding : B →* DihedralGroup n) (hinj : Function.Injective embedding)
    (projection : B →* QuaternionGroup 2) (left right : B) :
    projection left * projection right = projection right * projection left := by
  have central (element : B) (index : ZMod n)
      (helement : embedding element = DihedralGroup.sr index) (other : B) :
      projection element * projection other = projection other * projection element := by
    apply quaternion_square_one_central
    rw [← map_mul]
    have hsquare : element * element = 1 := by
      apply hinj
      simp [helement]
    rw [hsquare, map_one]
  cases hleft : embedding left with
  | sr index => exact central left index hleft right
  | r index =>
    cases hright : embedding right with
    | sr other => exact (central right other hright left).symm
    | r other =>
      have hcomm : left * right = right * left := by
        apply hinj
        simp [hleft, hright, add_comm]
      rw [← map_mul, hcomm, map_mul]

public theorem no_quaternion_section_of_dihedral_or_abelian_sylow
    {H : Type*} [Group H] [Finite H]
    (shape : (∃ S : Sylow 2 H, ∃ n : ℕ, Nonempty (S ≃* DihedralGroup n)) ∨
      (∃ S : Sylow 2 H, IsMulCommutative S))
    (A : Subgroup H) (projection : A →* QuaternionGroup 2) :
    ¬ Function.Surjective projection := by
  classical
  intro onto
  let P : Sylow 2 A := default
  have hquaternion : IsPGroup 2 (QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    rfl
  have htop : ((P.mapSurjective onto) : Subgroup (QuaternionGroup 2)) = ⊤ :=
    ((P.mapSurjective onto).is_maximal' (hquaternion.to_subgroup ⊤) le_top).symm
  let restricted : P →* QuaternionGroup 2 := projection.comp P.toSubgroup.subtype
  have hrestricted : Function.Surjective restricted := by
    intro element
    have hmem : element ∈ P.toSubgroup.map projection := by
      change element ∈ ((P.mapSurjective onto) : Subgroup (QuaternionGroup 2))
      rw [htop]
      trivial
    obtain ⟨preimage, hpreimage, heq⟩ := hmem
    exact ⟨⟨preimage, hpreimage⟩, heq⟩
  obtain ⟨T, hT⟩ := P.exists_comap_subtype_eq
  let intoAmbient : P →* T :=
    { toFun := fun element => ⟨element.val.val, by
        exact (show P.toSubgroup ≤ T.toSubgroup.comap A.subtype from hT.ge)
          element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective intoAmbient := by
    intro left right heq
    exact Subtype.ext (Subtype.ext (congrArg (fun element : T => (element : H)) heq))
  have hcomm : ∀ left right : P,
      restricted left * restricted right = restricted right * restricted left := by
    rcases shape with ⟨S, n, ⟨equivalence⟩⟩ | ⟨S, commutative⟩
    · let embedding := equivalence.toMonoidHom.comp ((T.equiv S).toMonoidHom.comp intoAmbient)
      exact dihedral_image_commutes embedding
        (equivalence.injective.comp ((T.equiv S).injective.comp hinj)) restricted
    · let := commutative
      let embedding := (T.equiv S).toMonoidHom.comp intoAmbient
      have hembedding : Function.Injective embedding := (T.equiv S).injective.comp hinj
      intro left right
      have heq : left * right = right * left := by
        apply hembedding
        simp only [map_mul]
        exact mul_comm' _ _
      rw [← map_mul, heq, map_mul]
  obtain ⟨left, hleft⟩ := hrestricted (QuaternionGroup.a 1)
  obtain ⟨right, hright⟩ := hrestricted (QuaternionGroup.xa 0)
  exact quaternion_noncommuting (by simpa [hleft, hright] using hcomm left right)
