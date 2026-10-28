module

public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels

/-!
# An actual order-24 subgroup of PSL3(2) is symmetric four

Its Sylow two-subgroup has the full ambient Sylow order. The existing
marked parabolic theorem therefore identifies the actual subgroup with a
point or line parabolic. No abstract extension classification is used.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two

/-- The actual order-24 subgroup has the symmetric-four model. -/
theorem subgroup_twentyFour_equiv_symmetric (A : Subgroup PSL)
    (hA : Nat.card A=24) : Nonempty (A≃*Equiv.Perm (Fin 4)) := by
  let R : Sylow 2 A := Classical.choice inferInstance
  let B := (R : Subgroup A).map A.subtype
  have hB : Nat.card B=8 := by
    rw [card_map_of_injective A.subtype_injective,R.card_eq_multiplicity,hA]
    decide +kernel
  let S : Sylow 2 PSL := Sylow.ofCard B (by rw [hB,card_PSL]; decide +kernel)
  have hSA : (S : Subgroup PSL)≤A := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hne : A≠⊤ := by
    intro he
    rw [he,card_top,card_PSL] at hA
    omega
  have hn : ¬IsPGroup 2 A := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hA] at hn
    exact (by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow
      (hn ▸ (by decide : 3∣24)))
  obtain ⟨e,_,he⟩ := exists_sylow_line_marking (MulEquiv.refl PSL) S A hSA hne hn
  exact ⟨((e.subgroupMap A).trans (MulEquiv.subgroupCongr he)).trans
    MarkedAutomorphisms.lineEquivSymmetric⟩

end Matrix.PSL3Two
