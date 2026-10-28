module

public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveNormalizer

/-!
# Order-ten subgroups are self-normalizing in A₆

The unique Sylow five-subgroup is characteristic in an order-ten subgroup.
Its A₆ normalizer already has order ten, leaving no larger normalizer for
the original subgroup. The second statement transports the equality to an
arbitrary actual A₆ model, as needed for the literal J₃ cubic quotient.
-/

public noncomputable section

open Subgroup
namespace AlternatingSix.TenSelfNormalizer

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every actual order-ten subgroup of A₆ is self-normalizing. -/
theorem ten_normalizer_eq (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : Nat.card D = 10) : normalizer (D : Set (alternatingGroup (Fin 6))) = D := by
  let S : Sylow 5 D := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity, hD]; decide +kernel
  have hi : (S : Subgroup D).index = 2 := by
    have hh := (S : Subgroup D).card_mul_index
    rw [hS, hD] at hh
    omega
  let : (S : Subgroup D).Normal := normal_of_index_eq_two hi
  let : (S : Subgroup D).Characteristic := S.characteristic_of_normal inferInstance
  let P := (S : Subgroup D).map D.subtype
  have hP : Nat.card P = 5 := (card_map_of_injective D.subtype_injective).trans hS
  have hle : normalizer (D : Set (alternatingGroup (Fin 6))) ≤
      normalizer (P : Set (alternatingGroup (Fin 6))) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    let a := D.normalizerMonoidHom ⟨g, hg⟩
    have hfixed : (S : Subgroup D).comap a.toMonoidHom = S :=
      (inferInstance : (S : Subgroup D).Characteristic).fixed a
    have hay : a y ∈ (S : Subgroup D) := by
      change y ∈ (S : Subgroup D).comap a.toMonoidHom
      rwa [hfixed]
    exact mem_map.mpr ⟨a y, hay, rfl⟩
  apply (eq_of_le_of_card_ge D.le_normalizer ?_).symm
  calc
    Nat.card (normalizer (D : Set (alternatingGroup (Fin 6)))) ≤
        Nat.card (normalizer (P : Set (alternatingGroup (Fin 6)))) := card_le_of_le hle
    _ = 10 := PGLNineFiveNormalizer.alternating_five_normalizer_card P hP
    _ = Nat.card D := hD.symm

/-- The equality holds for the original order-ten subgroup in any actual A₆ model. -/
theorem ten_normalizer_eq_of_equiv {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) (D : Subgroup H) (hD : Nat.card D = 10) :
    normalizer (D : Set H) = D := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq]
  exact ten_normalizer_eq _ ((card_map_of_injective e.injective).trans hD)

end AlternatingSix.TenSelfNormalizer
