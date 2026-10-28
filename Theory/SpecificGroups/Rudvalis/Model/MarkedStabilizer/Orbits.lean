module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.FullModel
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.FirstCertificate
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
/-!
# Native Rudvalis suborbits and their local subgroup orders

The proved orbital invariance identifies the full point-stabilizer orbits
with the already counted forest components. The marked first point2325 lies
in the1755 component; point6 lies in the2304 component. Orbit--stabilizer
then gives local subgroup orders20480 and15600 on the original action.
-/
public section
namespace Rudvalis.MarkedStabilizer
open MulAction OuterNormalizer PrimitiveData

private theorem invariant : modelSubgroup≤relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut

theorem orbit_eq_root (x : Fin 4060) :
    orbit pointStabilizer x={y | root y=root x} := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ((root_eq_iff invariant x (g • x)).mpr ⟨g,g.property,rfl⟩).symm
  · intro h
    obtain ⟨g,h0,hg⟩ := (root_eq_iff invariant x y).mp h.symm
    exact ⟨⟨g,h0⟩,hg⟩

theorem first_orbit_card : Nat.card (orbit pointStabilizer firstPoint)=1755 := by
  rw [Nat.card_coe_set_eq,orbit_eq_root,firstPoint_root]
  exact root_one_card

theorem second_orbit_card : Nat.card (orbit pointStabilizer (6 : Fin 4060))=2304 := by
  rw [Nat.card_coe_set_eq,orbit_eq_root]
  have h : root (6 : Fin 4060)=6 := by decide +kernel
  rw [h]
  exact root_six_card

theorem orbit_partition : orbit pointStabilizer (6 : Fin 4060)=
    (({0} : Set (Fin 4060))∪orbit pointStabilizer firstPoint)ᶜ := by
  rw [orbit_eq_root,orbit_eq_root,firstPoint_root]
  have h6 : root (6 : Fin 4060)=6 := by decide +kernel
  rw [h6]
  ext x
  change root x=6 ↔ ¬(x=0 ∨ root x=1)
  rw [← root_zero x]
  rcases root_cases x with h | h | h <;> simp [h]

theorem first_stabilizer_card :
    Nat.card (stabilizer pointStabilizer firstPoint)=20480 := by
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup pointStabilizer firstPoint)
  rw [Nat.card_prod,first_orbit_card,pointStabilizer_card] at h
  omega

theorem second_stabilizer_card :
    Nat.card (stabilizer pointStabilizer (6 : Fin 4060))=15600 := by
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup pointStabilizer (6 : Fin 4060))
  rw [Nat.card_prod,second_orbit_card,pointStabilizer_card] at h
  omega
end Rudvalis.MarkedStabilizer
