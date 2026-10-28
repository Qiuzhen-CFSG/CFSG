module
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# No square-preserving shear along a singular binary line

Let z be central and let z,u be commuting involutions. An automorphism
whose displacement lies in their four-group and fixes every square must
have central displacement. Outside C(u), square preservation forbids a
displacement involving u; multiplying by one fixed outside representative
then proves the same conclusion inside C(u). The group may be infinite.

In the extraspecial application, this excludes a singular transvection in
the orthogonal quotient and makes the automorphism inner. Source:
Aschbacher, *Sporadic Groups* (1994), Lemma 45.3(3), printed p. 243.
-/

open Subgroup

namespace MulAut
variable {P : Type*} [Group P]

/-- A square-preserving automorphism cannot shear along a singular binary line. -/
public theorem central_displacement_of_four_displacement
    (α : MulAut P) (z u : P) (hz : z^2=1) (hu : u^2=1)
    (hzZ : z ∈ center P) (huZ : u ∉ center P)
    (hsq : ∀ x : P, α (x^2) = x^2)
    (hfour : ∀ x : P, α x*x⁻¹ ∈ closure ({z,u} : Set P)) :
    ∀ x : P, α x*x⁻¹ ∈ center P := by
  let δ := fun x : P => α x*x⁻¹
  have hzu : Commute z u := (mem_center_iff.mp hzZ u).symm
  have hcases (x : P) : δ x=1 ∨ δ x=z ∨ δ x=u ∨ δ x=z*u :=
    (Subgroup.mem_closure_pair_iff z u (by simpa only [pow_two] using hz)
      (by simpa only [pow_two] using hu) hzu _).mp (hfour x)
  have hd2 (x : P) : δ x^2=1 := by
    rcases hcases x with he | he | he | he
    · rw [he,one_pow]
    · exact he ▸ hz
    · exact he ▸ hu
    · rw [he,hzu.mul_pow,hz,hu,one_mul]
  have hdx (x : P) : Commute (δ x) x := by
    have he : (δ x*x)^2=x^2 := by
      rw [show δ x*x=α x by simp [δ],← map_pow,hsq]
    change δ x*x=x*δ x
    calc
      δ x*x = δ x*(x^2)*x⁻¹ := by group
      _ = δ x*((δ x*x)^2)*x⁻¹ := by rw [he]
      _ = (δ x*δ x)*x*δ x := by simp only [pow_two]; group
      _ = x*δ x := by rw [← pow_two,hd2 x,one_mul]
  let C := centralizer ({u} : Set P)
  have hout (x : P) (hx : x ∉ C) : δ x ∈ center P := by
    rcases hcases x with he | he | he | he
    · rw [he]; exact (center P).one_mem
    · exact he ▸ hzZ
    · exact (hx (mem_centralizer_singleton_iff.mpr ((he ▸ hdx x).symm))).elim
    · exfalso
      apply hx
      apply mem_centralizer_singleton_iff.mpr
      have hd : (z*u)*x=x*(z*u) := he ▸ (hdx x).eq
      have hzcomm : x*z=z*x := mem_center_iff.mp hzZ x
      apply mul_left_cancel (a:=z)
      calc
        z*(x*u) = x*(z*u) := by rw [← mul_assoc,← hzcomm,mul_assoc]
        _ = (z*u)*x := hd.symm
        _ = z*(u*x) := mul_assoc _ _ _
  obtain ⟨v,hv⟩ : ∃ v : P, v ∉ C := by
    by_contra hn
    apply huZ
    apply mem_center_iff.mpr
    intro v
    exact mem_centralizer_singleton_iff.mp (not_not.mp (fun h => hn ⟨v,h⟩))
  intro x
  by_cases hx : x ∈ C
  · have hxv : x*v ∉ C := fun hh => hv ((C.mul_mem_cancel_left hx).mp hh)
    have hdv := hout v hv
    have hdxv := hout (x*v) hxv
    have he : δ (x*v) = δ x * δ v := by
      dsimp [δ]
      rw [map_mul,mul_inv_rev]
      calc
        α x*α v*(v⁻¹*x⁻¹) = α x*(α v*v⁻¹)*x⁻¹ := by group
        _ = α x*x⁻¹*(α v*v⁻¹) := by
          rw [mul_assoc,← mem_center_iff.mp hdv x⁻¹]
          dsimp [δ]
          group
    have hm := (center P).mul_mem hdxv ((center P).inv_mem hdv)
    rw [he,mul_inv_cancel_right] at hm
    exact hm
  · exact hout x hx
end MulAut
