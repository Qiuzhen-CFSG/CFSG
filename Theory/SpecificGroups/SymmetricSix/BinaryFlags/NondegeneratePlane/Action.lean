module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Cubic
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Complement
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# The two cubic moving planes in the actual S₆ action

The cubic axis on the first three letters fixes the complementary plane
and moves the whole canonical plane; the other axis does the reverse.
Form invariance bounds each displacement image by the relevant perpendicular,
and two explicit vector displacements give the reverse inclusion. Conjugation
then gives the full family for every original nondegenerate plane, retaining
the literal natural representation, cubic subgroups, and stabilizer.

Source: Aschbacher--Smith, Lemma 13.5.6, printed p.917. The final
`exists_cubic_decomposition` is the native action input for the two A₃-block
lift in that source proof; it has no model or action certificate premise.
-/

@[expose] public section

open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
open NaturalGeometry NaturalPairing Representation.BinaryOffender SymmetricThreeProduct

theorem right_fixes_plane (g : S) (hg : g ∈ cubicRight) :
    ∀ v ∈ plane, naturalRepresentation Ω g v = v := by
  apply (fixes_plane_iff g).mpr
  obtain ⟨x,hx,rfl⟩ := hg
  have h : ∀ x : TriplePerm × TriplePerm, x ∈ rightThree →
      tripleProductHom x 0=0 ∧ tripleProductHom x 1=1 ∧ tripleProductHom x 2=2 := by
    change ∀ x : TriplePerm × TriplePerm, x.1=1 ∧ x.2^3=1 → _
    decide
  exact h x hx

theorem left_fixes_secondPlane (g : S) (hg : g ∈ cubicLeft) :
    ∀ v ∈ secondPlane, naturalRepresentation Ω g v = v := by
  obtain ⟨x,hx,rfl⟩ := hg
  have h : ∀ x : TriplePerm × TriplePerm, x ∈ leftThree →
      tripleProductHom x 3=3 ∧ tripleProductHom x 4=4 ∧ tripleProductHom x 5=5 := by
    change ∀ x : TriplePerm × TriplePerm, x.1^3=1 ∧ x.2=1 → _
    decide
  obtain ⟨h3,h4,h5⟩ := h x hx
  intro v hv
  rw [secondPlane_span] at hv
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [map_add,map_smul,map_smul,pairVector_map,pairVector_map,h3,h4,h5]

noncomputable abbrev movedSpace (A : Subgroup S) : Submodule (ZMod 2) V :=
  Representation.Coinvariants.ker ((naturalRepresentation Ω).comp A.subtype)

private theorem movedSpace_le_orthogonal (A : Subgroup S) (W : Submodule (ZMod 2) V)
    (hf : ∀ g ∈ A, ∀ v ∈ W, naturalRepresentation Ω g v = v) :
    movedSpace A ≤ form.orthogonal W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩ w hw
  change form w (naturalRepresentation Ω g v - v) = 0
  have h := form_invariant g w v
  rw [hf g g.property w hw] at h
  rw [map_sub,h,sub_self]

private theorem left_moves_first :
    naturalRepresentation Ω cycleLeft (pairVector 1 2) - pairVector 1 2 = pairVector 0 1 := by
  rw [pairVector_map,ZModModule.sub_eq_add]
  change pairVector 2 0 + pairVector 1 2 = pairVector 0 1
  rw [pairVector_comm 1 2,pairVector_triangle]

private theorem left_moves_second :
    naturalRepresentation Ω cycleLeft (pairVector 0 1) - pairVector 0 1 = pairVector 0 2 := by
  rw [pairVector_map,ZModModule.sub_eq_add]
  change pairVector 1 2 + pairVector 0 1 = pairVector 0 2
  rw [pairVector_comm 0 1,pairVector_triangle,pairVector_comm 2 0]

private theorem right_moves_first :
    naturalRepresentation Ω cycleRight (pairVector 4 5) - pairVector 4 5 = pairVector 3 4 := by
  rw [pairVector_map,ZModModule.sub_eq_add]
  change pairVector 5 3 + pairVector 4 5 = pairVector 3 4
  rw [pairVector_comm 4 5,pairVector_triangle]

private theorem right_moves_second :
    naturalRepresentation Ω cycleRight (pairVector 3 4) - pairVector 3 4 = pairVector 3 5 := by
  rw [pairVector_map,ZModModule.sub_eq_add]
  change pairVector 4 5 + pairVector 3 4 = pairVector 3 5
  rw [pairVector_comm 3 4,pairVector_triangle,pairVector_comm 5 3]

theorem cubicLeft_movedSpace : movedSpace cubicLeft = plane := by
  apply le_antisymm
  · rw [plane_eq_orthogonal_second]
    exact movedSpace_le_orthogonal cubicLeft secondPlane left_fixes_secondPlane
  · rw [plane]
    apply Submodule.span_le.mpr
    have h1 := Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp cubicLeft.subtype)
      (⟨cycleLeft,cycleLeft_mem⟩ : cubicLeft) (pairVector 1 2)
    have h2 := Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp cubicLeft.subtype)
      (⟨cycleLeft,cycleLeft_mem⟩ : cubicLeft) (pairVector 0 1)
    change naturalRepresentation Ω cycleLeft (pairVector 1 2) - pairVector 1 2 ∈ movedSpace cubicLeft at h1
    change naturalRepresentation Ω cycleLeft (pairVector 0 1) - pairVector 0 1 ∈ movedSpace cubicLeft at h2
    rw [left_moves_first] at h1
    rw [left_moves_second] at h2
    rintro v (rfl | rfl)
    · exact h1
    · exact h2

theorem cubicRight_movedSpace : movedSpace cubicRight = secondPlane := by
  apply le_antisymm
  · rw [secondPlane_eq_orthogonal]
    exact movedSpace_le_orthogonal cubicRight plane right_fixes_plane
  · rw [secondPlane_span]
    apply Submodule.span_le.mpr
    have h1 := Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp cubicRight.subtype)
      (⟨cycleRight,cycleRight_mem⟩ : cubicRight) (pairVector 4 5)
    have h2 := Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp cubicRight.subtype)
      (⟨cycleRight,cycleRight_mem⟩ : cubicRight) (pairVector 3 4)
    change naturalRepresentation Ω cycleRight (pairVector 4 5) - pairVector 4 5 ∈ movedSpace cubicRight at h1
    change naturalRepresentation Ω cycleRight (pairVector 3 4) - pairVector 3 4 ∈ movedSpace cubicRight at h2
    rw [right_moves_first] at h1
    rw [right_moves_second] at h2
    rintro v (rfl | rfl)
    · exact h1
    · exact h2


theorem movedSpace_map_conj (A : Subgroup S) (g : S) :
    movedSpace (A.map (MulAut.conj g).toMonoidHom) = move g (movedSpace A) := by
  have hd (a : S) (v : V) :
      naturalRepresentation Ω (g*a*g⁻¹) v-v =
        naturalRepresentation Ω g (naturalRepresentation Ω a (naturalRepresentation Ω g⁻¹ v)-naturalRepresentation Ω g⁻¹ v) := by
    simp only [map_sub,map_mul,Module.End.mul_apply,Representation.self_inv_apply]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    change naturalRepresentation Ω a.val v-v ∈ _
    change g*b*g⁻¹=a.val at he
    rw [← he,hd]
    exact ⟨_,Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp A.subtype) ⟨b,hb⟩ _,rfl⟩
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    change naturalRepresentation Ω g (naturalRepresentation Ω a.val v-v) ∈ movedSpace (A.map (MulAut.conj g).toMonoidHom)
    have he := hd a.val (naturalRepresentation Ω g v)
    rw [Representation.inv_self_apply] at he
    rw [← he]
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := (naturalRepresentation Ω).comp (A.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨g*a.val*g⁻¹,⟨a.val,a.property,rfl⟩⟩ _

theorem orthogonal_move (g : S) (W : Submodule (ZMod 2) V) :
    move g (form.orthogonal W) = form.orthogonal (move g W) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [form_invariant]
    exact hx y hy
  · rw [move_finrank,LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,move_finrank]

theorem fixes_move_conj (A : Subgroup S) (W : Submodule (ZMod 2) V)
    (hf : ∀ a ∈ A, ∀ v ∈ W, naturalRepresentation Ω a v = v) (g : S) :
    ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ v ∈ move g W,
      naturalRepresentation Ω a v = v := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨v,hv,rfl⟩
  change naturalRepresentation Ω (g*a*g⁻¹) (naturalRepresentation Ω g v) = _
  simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply,hf a ha v hv]

/-- Every nondegenerate-plane stabilizer has the actual two-block symmetric model. -/
theorem nondegeneratePlane_stabilizer_model (W : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W=2)
    (hn : ¬∀ x∈W,∀ y∈W,form x y=0) :
    Nonempty ((TriplePerm × TriplePerm) ≃* flagStabilizer W) := by
  obtain ⟨g,rfl⟩ := exists_plane_marking W hd hn
  rw [flagStabilizer_move]
  exact ⟨tripleProductEquiv.trans ((MulAut.conj g).subgroupMap planeStabilizer)⟩

theorem nondegeneratePlane_isCompl (W : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W=2)
    (hn : ¬∀ x∈W,∀ y∈W,form x y=0) : IsCompl W (form.orthogonal W) := by
  obtain ⟨g,rfl⟩ := exists_plane_marking W hd hn
  rw [← orthogonal_move,← secondPlane_eq_orthogonal]
  exact ⟨Submodule.disjoint_map ((naturalRepresentation Ω).apply_bijective g).injective
    plane_secondPlane_disjoint,
    Submodule.codisjoint_map ((naturalRepresentation Ω).apply_bijective g).surjective
      plane_secondPlane_isCompl.codisjoint⟩

/-- The cubic axes and their complementary moving planes, in the original
natural action, for every genuine nondegenerate plane. -/
theorem exists_cubic_decomposition (W : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W=2)
    (hn : ¬∀ x∈W,∀ y∈W,form x y=0) :
    ∃ A B : Subgroup S,
      Nat.card A=3 ∧ Nat.card B=3 ∧ Disjoint A B ∧
      (∀ a∈A,∀ b∈B,Commute a b) ∧
      A⊔B ≤ flagStabilizer W ∧ A⊔B ≤ alternatingGroup Ω ∧
      Nat.card (A⊔B : Subgroup S)=9 ∧ IsElementaryAbelian 3 (A⊔B : Subgroup S) ∧
      flagStabilizer W ≤ normalizer (A : Set S) ∧
      flagStabilizer W ≤ normalizer (B : Set S) ∧
      movedSpace A=W ∧ movedSpace B=form.orthogonal W ∧
      (∀ a∈A,∀ v∈form.orthogonal W,naturalRepresentation Ω a v=v) ∧
      (∀ b∈B,∀ v∈W,naturalRepresentation Ω b v=v) := by
  obtain ⟨g,rfl⟩ := exists_plane_marking W hd hn
  let f := (MulAut.conj g).toMonoidHom
  refine ⟨cubicLeft.map f,cubicRight.map f,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [card_map_of_injective (MulAut.conj g).injective,cubicLeft_card]
  · rw [card_map_of_injective (MulAut.conj g).injective,cubicRight_card]
  · exact Subgroup.disjoint_map (MulAut.conj g).injective cubic_disjoint
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact (cubic_commute a b ha hb).map f
  · rw [← Subgroup.map_sup,cubic_sup,flagStabilizer_move]
    exact Subgroup.map_mono nineCore_le
  · rw [← Subgroup.map_sup,cubic_sup]
    rintro _ ⟨a,ha,rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance a (nineCore_even ha) g
  · rw [← Subgroup.map_sup,cubic_sup,card_map_of_injective (MulAut.conj g).injective,nineCore_card]
  · rw [← Subgroup.map_sup,cubic_sup]
    exact IsElementaryAbelian.map f
  · rw [flagStabilizer_move]
    exact (Subgroup.map_mono stabilizer_normalizes_left).trans (Subgroup.le_normalizer_map f)
  · rw [flagStabilizer_move]
    exact (Subgroup.map_mono stabilizer_normalizes_right).trans (Subgroup.le_normalizer_map f)
  · exact (movedSpace_map_conj cubicLeft g).trans (congrArg (move g) cubicLeft_movedSpace)
  · rw [movedSpace_map_conj,cubicRight_movedSpace,secondPlane_eq_orthogonal,orthogonal_move]
  · rw [← orthogonal_move,← secondPlane_eq_orthogonal]
    exact fixes_move_conj cubicLeft secondPlane left_fixes_secondPlane g
  · exact fixes_move_conj cubicRight plane right_fixes_plane g

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
