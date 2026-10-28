module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The central-derived trace of a field-involution centralizer

The two binary simple-root elements are fixed by every field automorphism
and do not commute. A two-group containing them has nontrivial derived
subgroup; its intersection with the center is nontrivial. When that derived
subgroup lies in the marked unitriangular group, commuting with the two
simple roots puts this characteristic intersection in the highest root.

This is the intrinsic linear calculation in Aschbacher–Smith F.4.37,
printed p.293 of `refs/quasithin.pdf`. The ambient Sylow argument is separate.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry
variable {G : Type*} [Group G] [Finite G]
  (F : Type*) [Field F]

/-- A field-marked involution has a nontrivial characteristic central-derived
subgroup in every two-group centralizer with derived subgroup in the marked U. -/
theorem field_centralizer_characteristic_line
    (S E : Subgroup G) (e : U F ≃* S) (t : G) (σ : F ≃+* F)
    (hp : IsPGroup 2 E)
    (hfix : ∀ u : U F, t * markedHom F S e u * t⁻¹ =
      markedHom F S e ⟨σ u.x,σ u.y,σ u.c⟩)
    (hle : S ⊓ centralizer ({t} : Set G) ≤ E)
    (hder : ⁅E,E⁆ ≤ S) :
    let Q := center E ⊓ _root_.commutator E
    Q ≠ ⊥ ∧ Q.map E.subtype ≤ centerIn S := by
  let j := markedHom F S e
  have hj : Function.Injective j := markedHom_injective F S e
  let a : U F := ⟨1,0,0⟩
  let b : U F := ⟨0,1,0⟩
  have ha : j a ∈ E := by
    apply hle
    refine ⟨(e a).property,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := hfix a
    have he : (⟨σ a.x,σ a.y,σ a.c⟩ : U F) = a := by
      apply U.ext <;> simp [a]
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hb : j b ∈ E := by
    apply hle
    refine ⟨(e b).property,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := hfix b
    have he : (⟨σ b.x,σ b.y,σ b.c⟩ : U F) = b := by
      apply U.ext <;> simp [b]
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hd : _root_.commutator E ≠ ⊥ := by
    intro hd
    have hh : ⁅(⟨j a,ha⟩ : E),(⟨j b,hb⟩ : E)⁆ = 1 := by
      apply mem_bot.mp
      rw [←hd]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have hc : j a * j b = j b * j a := congrArg E.subtype (commutatorElement_eq_one_iff_mul_comm.mp hh)
    have hab : a*b=b*a := hj (by simpa only [map_mul] using hc)
    have h01 := (mul_comm_iff F a b).mp hab
    simp [a,b] at h01
  refine ⟨center_inf_ne_bot_of_normal hp _ hd,?_⟩
  rintro x ⟨v,hv,rfl⟩
  have hvS : v.val ∈ S := hder (by
    rw [←map_subtype_commutator]
    exact mem_map_of_mem E.subtype hv.2)
  let u := e.symm ⟨v.val,hvS⟩
  have hu : j u=v.val := congrArg S.subtype (e.apply_symm_apply ⟨v.val,hvS⟩)
  have hcomm (w : U F) (hw : j w ∈ E) : w*u=u*w := by
    apply hj
    rw [map_mul,map_mul,hu]
    exact congrArg E.subtype (mem_center_iff.mp hv.1 ⟨j w,hw⟩)
  have h₁ := (mul_comm_iff F a u).mp (hcomm a ha)
  have h₂ := (mul_comm_iff F b u).mp (hcomm b hb)
  have huz : u ∈ Z F := by
    apply (mem_Z F u).mpr
    constructor
    · simpa [b] using h₂.symm
    · simpa [a] using h₁
  have hz : j u ∈ centerIn S := by
    rw [centerIn_eq_map_center,marked_center F S e]
    exact mem_map_of_mem j huz
  rwa [hu] at hz
end Matrix.PSL3.LinearAmbientGeometry
