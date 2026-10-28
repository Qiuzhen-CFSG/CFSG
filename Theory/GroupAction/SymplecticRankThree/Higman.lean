module
public import Theory.GroupAction.SymplecticRankThree.ProjectiveCoordinates
public import Theory.GroupAction.SymplecticRankThree.AlternatingPolarity
public import Theory.GroupAction.SymplecticRankThree.Coordinatized
public import Theory.GroupAction.SymplecticRankThree.BinaryHigman
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport

/-!
# The binary-field condition-(i) rank-three recognition theorem

For the faithful primitive, self-paired action supplied by the original source,
the actual three suborbits and kernel lower bound construct the polarity design.
Spatial affine and projective coordinatization realize its null polarity as an
alternating form. The kernel contains all symplectic elations; generation and
conjugation give a normal full Sp₄ subgroup. No coordinate or model-map premise
is assumed. The q=2 branch uses the separately proved binary reconstruction,
which gives the whole Sp₄(2), never its derived A₆.

The source coset action proves primitivity and supplies its literal reversing
Weyl element before applying this specialization. Recognition applies for every
positive binary field degree, without Higman's alternative condition (ii).

Source: Higman (1964), Theorem 2(i), pp.154–155; Fong–Seitz II (7C), (8A).
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree
open Subgroup MulAction
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
variable {F G Ω : Type*} [Field F] [Finite F] [CharP F 2]
  [Group G] [Fintype Ω] [MulAction G Ω] [FaithfulSMul G Ω] [IsPreprimitive G Ω]

/-- The complete condition-(i) specialization used by the actual C₂ source:
all geometric and model-recognition premises have been discharged. -/
theorem condition_i_recognition
    (a b c : Ω) (hab : a ≠ b) (t : G) (hta : t • a = b) (htb : t • b = a)
    (hc : orbit (stabilizer G a) c = (insert a (orbit (stabilizer G a) b))ᶜ)
    (hdegree : Nat.card Ω = (Nat.card F)^3+(Nat.card F)^2+Nat.card F+1)
    (hsubdegree : Nat.card (orbit (stabilizer G a) b) = Nat.card F*(Nat.card F+1))
    (hk : Nat.card F ≤ Nat.card (fixingSubgroup G (insert a (orbit (stabilizer G a) b)))) :
    ∃ K : Subgroup G, K.Normal ∧ Nonempty (K ≃* Sp F) := by
  by_cases hF : Nat.card F = 2
  · obtain ⟨D,_,_,E,e,_,_⟩ := binary_condition_i_recognition a b c hab t hta htb hc
      (by rw [hF] at hdegree; exact hdegree.trans (by decide)) (by rw [hF] at hsubdegree; exact hsubdegree.trans (by decide))
      (by simpa only [hF] using hk)
    exact ⟨⊤,inferInstance,⟨(Subgroup.topEquiv.trans e).trans
      (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF).symm)⟩⟩
  · have hq : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
    obtain ⟨D,hD,hblock,hl⟩ := condition_i_lines hq a b c hab t hta htb hc hdegree hsubdegree hk
    obtain ⟨f,_⟩ := D.exists_affineFrame hl hq hdegree a
    obtain ⟨C,hC⟩ := f.exists_projective_space_coordinates hl hq F rfl hF
    obtain ⟨E,hE⟩ := D.polar_coordinates_of_line_coordinates hF C hC
    have hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y := by
      intro g x y
      rw [hD,hD,SwappedOrbital.adj_smul_iff]
      exact or_congr (MulAction.injective g).eq_iff Iff.rfl
    have hcC : c ∈ (insert a (orbit (stabilizer G a) b))ᶜ := hc ▸ mem_orbit_self c
    have hac : ¬ D.incident a c := by
      intro hh
      rcases (hD a c).mp hh with hh | hh
      · exact hcC (Or.inl hh)
      · exact hcC (Or.inr ((SwappedOrbital.adj_base a b hab t hta htb c).mp hh))
    exact D.normal_symplectic_of_coordinates E hact hE hac (hblock.symm ▸ hk)

end Theory.GroupAction.SymplecticRankThree
