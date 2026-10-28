module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.MarkedFourPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer

/-!
# Simultaneous sign and Frobenius coordinates for the ambient actor

The image of C_T(A) under conjugation on a normal subgroup is a two-group
fixing the transported A pointwise. First normalize the original Hermitian
form and the marked involution, then place that four-group, then conjugate
the whole fixer image once. Composing these equivalences gives the literal
coordinate premise of `escape_of_sign_coordinates` for every ambient actor.

The final theorem discharges the marked-four placement and standard-fixer
premises using their matrix proofs. Simplicity of the identity Gram model
is transported from the given normal subgroup through the actual projective
equivalence. For p congruent to one modulo four, the result supplies the
coordinate premise of `escape_of_sign_coordinates`. This coordinate step
needs only normality and simplicity of the modeled subgroup, so it applies
in particular to the generalized Fitting subgroup in the SQTK source setup.

Source: Aschbacher--Smith E.1.14(7), printed p.214, A.3.21, printed p.55,
and Aschbacher (1982), Lemma 4.11.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]

variable {G : Type*} [Group G]

/-- The image of the actual ambient centralizer actor is a two-group fixing
pointwise the actual image of the four-group. No faithfulness or innerness
assumption on the ambient action is used. -/
theorem centralizer_actor_image (L : Subgroup G) [L.Normal]
    {K : Type*} [Group K] (e : L ≃* K)
    (T : Sylow 2 G) (A : Subgroup G) :
    let f := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
    let U := ((T : Subgroup G) ⊓ centralizer (A : Set G)).map f
    IsPGroup 2 U ∧ ∀ a ∈ U, ∀ x ∈ (A.subgroupOf L).map e.toMonoidHom, a x = x := by
  dsimp only
  refine ⟨(T.isPGroup'.to_le inf_le_left).map _, ?_⟩
  rintro a ⟨g, hg, rfl⟩ x ⟨b, hb, rfl⟩
  change e (MulAut.conjNormal g (e.symm (e b))) = e b
  rw [e.symm_apply_apply]
  apply congrArg e
  apply Subtype.ext
  change g * b.val * g⁻¹ = b.val
  have hc := mem_centralizer_iff.mp hg.2 b.val hb
  rw [← hc, mul_inv_cancel_right]

/-- The two intrinsic model calculations suffice for the literal ambient
coordinate statement, with a single equivalence for the whole actor. -/
theorem exists_sign_coordinates_of_model_inputs [Finite F]
    (L : Subgroup G) [L.Normal] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e₀ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hAL : A ≤ L)
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hplace : MarkedFourPlacement (HermitianForm.IdentityGram.identityGram J) rfl)
    (hfix : StandardFixerCoordinates (HermitianForm.IdentityGram.identityGram J)) :
    ∃ e : L ≃* ProjectiveSpecialUnitaryMatrixGroup (HermitianForm.IdentityGram.identityGram J),
      e ⟨z, hAL hzA⟩ = (HermitianForm.IdentityGram.identityGram J).specialToProjective
        (Matrix.SU3.standardInvolution (HermitianForm.IdentityGram.identityGram J) rfl) ∧
      ∀ g ∈ (T : Subgroup G) ⊓ centralizer (A : Set G),
        HasSignSemilinearForm (HermitianForm.IdentityGram.identityGram J)
          (MulAut.congr e (MulAut.conjNormal g)) := by
  let J₁ := HermitianForm.IdentityGram.identityGram J
  let zL : L := ⟨z, hAL hzA⟩
  have hzL : orderOf zL = 2 := by
    rw [← orderOf_injective L.subtype L.subtype_injective zL]
    exact hz
  obtain ⟨e₁, he₁⟩ := exists_marked_identityGram_equiv J hp ho hcard hc e₀ zL hzL
  let B := (A.subgroupOf L).map e₁.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map e₁.toMonoidHom
  have hBcard : Nat.card B = 4 := by
    rw [card_map_of_injective e₁.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hzB : J₁.specialToProjective (Matrix.SU3.standardInvolution J₁ rfl) ∈ B := by
    rw [← he₁]
    exact mem_map_of_mem e₁.toMonoidHom (show zL ∈ A.subgroupOf L from hzA)
  obtain ⟨b, hbz, hbB⟩ := hplace B hB hBcard hzB
  let e₂ := e₁.trans b
  have hB₂ : (A.subgroupOf L).map e₂.toMonoidHom = standardFour J₁ := by
    rw [← hbB]
    change _ = ((A.subgroupOf L).map e₁.toMonoidHom).map b.toMonoidHom
    rw [Subgroup.map_map]
    rfl
  have he₂ : e₂ zL = J₁.specialToProjective (Matrix.SU3.standardInvolution J₁ rfl) := by
    change b (e₁ zL) = _
    rw [he₁, hbz]
  let f := (MulAut.congr e₂).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
  let U := ((T : Subgroup G) ⊓ centralizer (A : Set G)).map f
  obtain ⟨hU, hfixU⟩ := centralizer_actor_image L e₂ T A
  rw [hB₂] at hfixU
  obtain ⟨c, hcz, hcoord⟩ := hfix U hU hfixU
  refine ⟨e₂.trans c, ?_, ?_⟩
  · change c (e₂ zL) = _
    rw [he₂]
    exact hcz _ (standardInvolution_mem_standardFour J₁ rfl)
  · intro g hg
    have hh := hcoord (f g) (mem_map_of_mem f hg)
    have heq : MulAut.congr c (f g) = MulAut.congr (e₂.trans c) (MulAut.conjNormal g) := by
      ext x
      rfl
    rwa [heq] at hh

/-- One equivalence simultaneously marks the involution and puts the entire
ambient four-group centralizer into sign and Frobenius coordinates. This
normal-subgroup version applies to the simple generalized Fitting subgroup
in E.1.14(7), without using the additional SQTK and Sylow-supplement inputs. -/
theorem exists_sign_coordinates [Finite F]
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e₀ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hAL : A ≤ L)
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2) :
    ∃ e : L ≃* ProjectiveSpecialUnitaryMatrixGroup (HermitianForm.IdentityGram.identityGram J),
      e ⟨z, hAL hzA⟩ = (HermitianForm.IdentityGram.identityGram J).specialToProjective
        (Matrix.SU3.standardInvolution (HermitianForm.IdentityGram.identityGram J) rfl) ∧
      ∀ g ∈ (T : Subgroup G) ⊓ centralizer (A : Set G),
        HasSignSemilinearForm (HermitianForm.IdentityGram.identityGram J)
          (MulAut.congr e (MulAut.conjNormal g)) := by
  obtain ⟨_, _, ep, _⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J p hp hcard hc
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup
      (HermitianForm.IdentityGram.identityGram J)) := (e₀.trans ep).symm.isSimpleGroup
  exact exists_sign_coordinates_of_model_inputs L J hp ho hcard hc e₀ T A hA hAL z hzA hz
    (markedFourPlacement (HermitianForm.IdentityGram.identityGram J) rfl hp ho hcard hc)
    (standardFixerCoordinates (HermitianForm.IdentityGram.identityGram J) rfl
      hp ho hm hcard hc)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
