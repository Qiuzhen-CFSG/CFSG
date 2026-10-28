module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal
public import Theory.SpecificGroups.SymmetricFourSylow

/-!
# The literal D₈ × S₄ vertex intersection

The first vertex pairs the four singular lines in its three-space by the
permutation (01)(23). The corresponding embedded D₈ is its centralizer in
S₄. Its inverse image under the already proved S₄ × S₄ equivalence fixes the
vertex; the three-point orbit proves equality. Both restriction equations
retain the original inclusions and the factor order. The independent second
S₄ factor is distinguished from any larger C₂ × S₄ subgroup.
Source: Aschbacher--Smith F.5.7, printed pp.302--303.
-/

@[expose] public section

namespace OmegaSixThree.TriangleLocal
open SixTernaryCoordinates OrthogonalityGraph
abbrev Four := Equiv.Perm (Fin 4)

/-- The double transposition pairing the four lines through the first vertex. -/
def delta : Four := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The first-factor dihedral subgroup with its literal four-point embedding. -/
def square : Subgroup Four := Subgroup.centralizer ({delta} : Set Four)

instance : DecidablePred (· ∈ square) := fun p =>
  decidable_of_iff (p * delta = delta * p) Subgroup.mem_centralizer_singleton_iff.symm

/-- The actual vertex intersection as a subgroup of the local triangle group. -/
def vertexLocal : Subgroup H := MulAction.stabilizer H standardFirst

def pairOmega : omegaPlusSixThree := ⟨signChange {0,1},pairSignChange_mem_omegaPlusSixThree⟩

theorem pairOmega_point (i : Fin 3) : pairOmega • negativePoint i = negativePoint i := by
  apply (point_eq_iff _ _ _ _).mpr
  change signed (pairOmega.val (negativeBasis i)) (negativeBasis i)
  revert i
  unfold signed
  decide +kernel

theorem pairOmega_mem : pairOmega ∈ H := by
  apply (mem_triangleStabilizer_iff _).mpr
  apply Set.EqOn.image_eq_self
  intro p hp
  obtain ⟨i,rfl⟩ := (mem_standardTriangle_iff p).mp hp
  exact pairOmega_point i

def pairElement : H := ⟨pairOmega,pairOmega_mem⟩

theorem pairElement_image : toProduct pairElement = (delta,1) := by
  apply Prod.ext <;> apply Equiv.ext <;> intro i
  · apply imageIndex_eq
    exact (show ∀ i : Fin 4, signed (pairOmega.val (tetra false i)) (tetra false (delta i)) by
      unfold signed; decide +kernel) i
  · apply imageIndex_eq
    exact (show ∀ i : Fin 4, signed (pairOmega.val (tetra true i)) (tetra true i) by
      unfold signed; decide +kernel) i

private theorem fixed_of_commute_pair (g : H) (hg : g * pairElement = pairElement * g) :
    g ∈ vertexLocal := by
  obtain ⟨j,hj⟩ := negativeBasis_image g 0
  have he := congrArg (fun a : H => a.val.val (negativeBasis 0)) hg
  change g.val.val (pairOmega.val (negativeBasis 0)) = pairOmega.val (g.val.val (negativeBasis 0)) at he
  rw [show pairOmega.val (negativeBasis 0) = negativeBasis 0 by decide +kernel] at he
  have hz : ∀ j : Fin 3, pairOmega.val (negativeBasis j) = negativeBasis j ↔ j = 0 := by
    decide +kernel
  have hj0 : j = 0 := by
    apply (hz j).mp
    rcases hj with hj | hj
    · rw [hj] at he
      exact he.symm
    · rw [hj,map_neg] at he
      exact (neg_inj.mp he).symm
  subst j
  exact (point_eq_iff _ _ _ _).mpr hj

theorem square_preimage_le_vertex : (square.prod ⊤).comap toProduct ≤ vertexLocal := by
  intro g hg
  apply fixed_of_commute_pair
  apply toProduct_injective
  rw [map_mul,map_mul,pairElement_image]
  apply Prod.ext
  · exact Subgroup.mem_centralizer_singleton_iff.mp hg.1
  · simp

private theorem negativePoint_injective : Function.Injective negativePoint := by
  intro i j h
  have hh := (point_eq_iff _ _ _ _).mp h
  exact (show ∀ i j : Fin 3, signed (negativeBasis i) (negativeBasis j) → i=j by
    unfold signed; decide +kernel) i j hh

private theorem local_orbit_eq : MulAction.orbit H standardFirst = standardTriangle := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact triangleStabilizer_smul_mem g.property (by simp [standardTriangle])
  · intro hp
    obtain ⟨i,rfl⟩ := (mem_standardTriangle_iff p).mp hp
    fin_cases i
    · exact ⟨1,rfl⟩
    · obtain ⟨g,hg,hgx,_,_⟩ := exists_local_swap
      exact ⟨⟨g,hg⟩,hgx⟩
    · obtain ⟨g,hg,hgx,_,_⟩ := exists_local_swap
      obtain ⟨h,hh,_,hhy,_⟩ := exists_local_flip
      exact ⟨⟨h*g,H.mul_mem hh hg⟩,by change (h*g) • standardFirst = standardThird; rw [mul_smul,hgx,hhy]⟩

theorem local_card : Nat.card H = 576 := by

  rw [Nat.card_congr productEquiv.toEquiv,Nat.card_prod,Nat.card_eq_fintype_card]
  norm_num [Fintype.card_perm,Nat.factorial]

theorem vertexLocal_card : Nat.card vertexLocal = 192 := by

  have ho : Nat.card (MulAction.orbit H standardFirst) = 3 := by
    rw [local_orbit_eq]
    let f : Fin 3 → standardTriangle := fun i => ⟨negativePoint i,negativePoint_mem i⟩
    have hf : Function.Bijective f := ⟨fun i j hij => negativePoint_injective (congrArg Subtype.val hij), by
      rintro ⟨p,hp⟩
      obtain ⟨i,rfl⟩ := (mem_standardTriangle_iff p).mp hp
      exact ⟨i,rfl⟩⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 3)
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H standardFirst)
  rw [Nat.card_prod,ho,local_card] at h
  change 3 * Nat.card vertexLocal = 576 at h
  omega

theorem square_card : Nat.card square = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def squareToVertex : (square.prod (⊤ : Subgroup Four)) →* vertexLocal :=
  ((productEquiv.symm.toMonoidHom.comp (square.prod ⊤).subtype).codRestrict vertexLocal (by
    intro p
    apply square_preimage_le_vertex
    change productEquiv (productEquiv.symm p.val) ∈ square.prod ⊤
    simpa only [productEquiv.apply_symm_apply] using p.property))

theorem squareToVertex_bijective : Function.Bijective squareToVertex := by
  let : Finite H := Finite.of_injective toProduct toProduct_injective
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply productEquiv.symm.injective
    exact congrArg Subtype.val hpq
  · rw [vertexLocal_card]
    rw [Nat.card_congr (Subgroup.prodEquiv square (⊤ : Subgroup Four)).toEquiv,Nat.card_prod,
      square_card,Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Four) ≃* Four).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

/-- Exact restriction of the original product equivalence to the vertex
intersection; the target keeps the actual embedded dihedral subgroup. -/
noncomputable def vertexProductEquiv : vertexLocal ≃* square × Four :=
  (MulEquiv.ofBijective squareToVertex squareToVertex_bijective).symm.trans
    ((Subgroup.prodEquiv square (⊤ : Subgroup Four)).trans
      (MulEquiv.prodCongr (MulEquiv.refl _) Subgroup.topEquiv))

set_option backward.isDefEq.respectTransparency false in
theorem vertexProductEquiv_first (g : vertexLocal) :
    (vertexProductEquiv g).1.val = (productEquiv g.val).1 := by
  have h := (MulEquiv.ofBijective squareToVertex squareToVertex_bijective).apply_symm_apply g
  have hh := congrArg (fun a : vertexLocal => productEquiv a.val) h
  change productEquiv (productEquiv.symm _) = _ at hh
  rw [productEquiv.apply_symm_apply] at hh
  exact congrArg Prod.fst hh

set_option backward.isDefEq.respectTransparency false in
theorem vertexProductEquiv_second (g : vertexLocal) :
    (vertexProductEquiv g).2 = (productEquiv g.val).2 := by
  have h := (MulEquiv.ofBijective squareToVertex squareToVertex_bijective).apply_symm_apply g
  have hh := congrArg (fun a : vertexLocal => productEquiv a.val) h
  change productEquiv (productEquiv.symm _) = _ at hh
  rw [productEquiv.apply_symm_apply] at hh
  exact congrArg Prod.snd hh


/-- The vertex intersection is exactly the first-factor square stabilizer. -/
theorem vertexLocal_eq : vertexLocal = (square.prod ⊤).comap toProduct := by
  apply le_antisymm _ square_preimage_le_vertex
  intro g hg
  change (toProduct g).1 ∈ square ∧ (toProduct g).2 ∈ (⊤ : Subgroup Four)
  refine ⟨?_,Subgroup.mem_top _⟩
  have hh := (vertexProductEquiv ⟨g,hg⟩).1.property
  rwa [vertexProductEquiv_first] at hh

/-- The embedded first factor is genuinely dihedral of order eight. -/
theorem square_dihedral : Nonempty (square ≃* DihedralGroup 4) := by
  let S : Sylow 2 Four := Sylow.ofCard square (by
    rw [square_card]
    have h : Nat.card Four = 24 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [h,show 24 = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization])
  exact Equiv.Perm.sylow_two_equiv_dihedral_four S

noncomputable def vertexDihedralEquiv : vertexLocal ≃* DihedralGroup 4 × Four :=
  vertexProductEquiv.trans (MulEquiv.prodCongr square_dihedral.some (MulEquiv.refl _))

/-- The original ambient intersection is the same subgroup under its inclusion. -/
def intersectionEquiv :
    (triangleStabilizer ⊓ MulAction.stabilizer omegaPlusSixThree standardFirst : Subgroup omegaPlusSixThree) ≃* vertexLocal where
  toFun g := ⟨⟨g.val,g.property.1⟩,g.property.2⟩
  invFun g := ⟨g.val.val,g.val.property,g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The literal ambient intersection, with the same first and second factors. -/
noncomputable def intersectionProductEquiv :
    (triangleStabilizer ⊓ MulAction.stabilizer omegaPlusSixThree standardFirst : Subgroup omegaPlusSixThree) ≃* square × Four :=
  intersectionEquiv.trans vertexProductEquiv

/-- The independent second S₄ factor, distinguished from the larger C₂ × S₄. -/
noncomputable def complementFactor : Subgroup H := ((⊥ : Subgroup Four).prod ⊤).comap toProduct

theorem complementFactor_le_vertexLocal : complementFactor ≤ vertexLocal := by
  rw [vertexLocal_eq]
  exact Subgroup.comap_mono (Subgroup.prod_mono bot_le le_rfl)


/-- The local vertex stabilizer has index three in the original triangle group. -/
theorem vertexLocal_index : vertexLocal.index = 3 := by
  have h := vertexLocal.card_mul_index
  rw [vertexLocal_card,local_card] at h
  omega

end OmegaSixThree.TriangleLocal
