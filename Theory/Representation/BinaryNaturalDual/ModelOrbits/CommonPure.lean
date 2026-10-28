module
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Common pure vectors across singular commutator images

A nontrivial conjugate of the central point in a singular image cannot be
pure when the marked pure orbit avoids the point class. It identifies the
singular diagonal orbit with that class. A pure vector in the image is
therefore still pure at the opposite endpoint. The argument uses the literal
section kernel and both subgroup images, without a fusion-control assumption.
Orthogonal product profiles supply singularity and a nonzero pure vector.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

public section
open Subgroup Representation
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
namespace BinaryNaturalDual.ModelOrbits
variable {G : Type*} [Group G]

private theorem pure_or_diagonal_of_singular
    (v : Space (Fin 3 → ZMod 2)) (hv : v ≠ 0) (hq : quadratic v = 0) :
    IsPure v ∨ IsSingularDiagonal v := by
  by_cases h₁ : v.1 = 0
  · exact Or.inl (Or.inr ⟨h₁,fun h₂ => hv (Prod.ext h₁ h₂)⟩)
  by_cases h₂ : v.2 = 0
  · exact Or.inl (Or.inl ⟨h₁,h₂⟩)
  exact Or.inr ⟨h₁,h₂,hq⟩

/-- The two singular images contain a common pure lift. The orbit hypotheses
are local to the marked classes and are discharged by the source consumer. -/
theorem common_pure_of_singular_images
    {A B Z W W' R : Subgroup G}
    {ρ : Representation (ZMod 2) A (Space (Fin 3 → ZMod 2))}
    (c : BinaryConjugationSection A B Z ρ)
    (hmarks : ∀ v : B, IsPure (c.coordinates v).toAdd ↔
      ((v : G) ∈ W ∨ (v : G) ∈ W') ∧ (v : G) ∉ Z)
    (g z : G) (hZ : ∀ w ∈ Z, w = 1 ∨ w = z)
    (hpoint : (MulAut.conj g) z ∈ R) (hpointZ : (MulAut.conj g) z ∉ Z)
    (hRB : R ≤ B) (hRBg : R ≤ B.map (MulAut.conj g).toMonoidHom)
    (hsingular : ∀ v ∈ c.imageSpace R, quadratic v = 0)
    (hsingular' : ∀ v ∈ c.imageSpace (R.map (MulAut.conj g⁻¹).toMonoidHom),
      quadratic v = 0)
    (hpure : ∃ v ∈ c.imageSpace R, IsPure v)
    (havoid : ∀ v : B, IsPure (c.coordinates v).toAdd → ¬ IsConj (v : G) z)
    (hdiagonal : ∀ v w : B, IsSingularDiagonal (c.coordinates v).toAdd →
      IsSingularDiagonal (c.coordinates w).toAdd → IsConj (v : G) (w : G)) :
    ∃ a b : G, (a ∈ W ∨ a ∈ W') ∧ (b ∈ W ∨ b ∈ W') ∧
      a ∉ Z ∧ b ∉ Z ∧ (MulAut.conj g) b = a := by
  let zg : B := ⟨(MulAut.conj g) z,hRB hpoint⟩
  have hzg0 : (c.coordinates zg).toAdd ≠ 0 :=
    fun he => hpointZ ((c.coordinates_eq_one_iff zg).mp he)
  have hzgconj : IsConj (zg : G) z :=
    (isConj_iff.mpr ⟨g,rfl⟩ : IsConj z (zg : G)).symm
  have hzgdiag : IsSingularDiagonal (c.coordinates zg).toAdd := by
    have hq := hsingular _ ((c.mem_imageSpace_iff R _).mpr ⟨zg,hpoint,rfl⟩)
    rcases pure_or_diagonal_of_singular _ hzg0 hq with hp | hd
    · exact False.elim (havoid zg hp hzgconj)
    · exact hd
  have hdiagZ (v : B) (hv : IsSingularDiagonal (c.coordinates v).toAdd) :
      IsConj (v : G) z := (hdiagonal v zg hv hzgdiag).trans hzgconj
  obtain ⟨v,hv,hvp⟩ := hpure
  obtain ⟨a,ha,hav⟩ := (c.mem_imageSpace_iff R v).mp hv
  have hap : IsPure (c.coordinates a).toAdd := hav ▸ hvp
  obtain ⟨ham,haZ⟩ := (hmarks a).mp hap
  have havoidA := havoid a hap
  obtain ⟨b,hb,hba⟩ := hRBg ha
  let bB : B := ⟨b,hb⟩
  have hab : IsConj b (a : G) := isConj_iff.mpr ⟨g,hba⟩
  have hbZ : b ∉ Z := by
    intro hbz
    rcases hZ b hbz with rfl | rfl
    · have ha1 : (a : G) = 1 := by simpa using hba.symm
      exact haZ (ha1 ▸ Z.one_mem)
    · exact havoidA hab.symm
  have hbR : b ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := by
    refine ⟨a,ha,?_⟩
    rw [← hba]
    simp [MulAut.conj_apply,mul_assoc]
  have hb0 : (c.coordinates bB).toAdd ≠ 0 :=
    fun he => hbZ ((c.coordinates_eq_one_iff bB).mp he)
  have hbq := hsingular' _ ((c.mem_imageSpace_iff _ _).mpr ⟨bB,hbR,rfl⟩)
  have hbp : IsPure (c.coordinates bB).toAdd := by
    rcases pure_or_diagonal_of_singular _ hb0 hbq with hp | hd
    · exact hp
    · exact False.elim (havoidA (hab.symm.trans (hdiagZ bB hd)))
  exact ⟨a,b,ham,((hmarks bB).mp hbp).1,haZ,hbZ,hba⟩

/-- Literal coordinate-axis markings identify the pure lifts outside the kernel. -/
theorem pure_iff_mem_marked_supports
    {A B Z W W' : Subgroup G}
    {ρ : Representation (ZMod 2) A (Space (Fin 3 → ZMod 2))}
    (c : BinaryConjugationSection A B Z ρ)
    (hW : ∀ v : B, (v : G) ∈ W ↔ (c.coordinates v).toAdd.2 = 0)
    (hW' : ∀ v : B, (v : G) ∈ W' ↔ (c.coordinates v).toAdd.1 = 0)
    (v : B) : IsPure (c.coordinates v).toAdd ↔
      ((v : G) ∈ W ∨ (v : G) ∈ W') ∧ (v : G) ∉ Z := by
  have hzero : (v : G) ∈ Z ↔
      (c.coordinates v).toAdd.1 = 0 ∧ (c.coordinates v).toAdd.2 = 0 := by
    rw [← c.coordinates_eq_one_iff]
    exact ⟨fun h => ⟨congrArg (fun x => x.toAdd.1) h,
        congrArg (fun x => x.toAdd.2) h⟩,
      fun h => Multiplicative.toAdd.injective (Prod.ext h.1 h.2)⟩
  rw [hW,hW',hzero]
  unfold IsPure
  tauto

/-- Both source profiles, a line times a line and a plane times its
annihilator line, are singular and contain a nonzero pure vector. -/
theorem orthogonal_product_profile
    {A B Z R : Subgroup G}
    {ρ : Representation (ZMod 2) A (Space (Fin 3 → ZMod 2))}
    (c : BinaryConjugationSection A B Z ρ)
    (P : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (Q : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)))
    (he : c.imageSpace R = P.prod Q)
    (horth : ∀ x ∈ P, ∀ f ∈ Q, f x = 0)
    (hne : P ≠ ⊥ ∨ Q ≠ ⊥) :
    (∀ v ∈ c.imageSpace R, quadratic v = 0) ∧
      ∃ v ∈ c.imageSpace R, IsPure v := by
  constructor
  · intro v hv
    rw [he] at hv
    exact horth v.1 hv.1 v.2 hv.2
  · rcases hne with hp | hq
    · obtain ⟨x,hx,hx0⟩ := P.ne_bot_iff.mp hp
      exact ⟨(x,0),he.symm ▸ (show (x,0) ∈ P.prod Q from ⟨hx,Q.zero_mem⟩),
        Or.inl ⟨hx0,rfl⟩⟩
    · obtain ⟨f,hf,hf0⟩ := Q.ne_bot_iff.mp hq
      exact ⟨(0,f),he.symm ▸ (show (0,f) ∈ P.prod Q from ⟨P.zero_mem,hf⟩),
        Or.inr ⟨rfl,hf0⟩⟩

end BinaryNaturalDual.ModelOrbits
