module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms

/-!
# Involution commutators cannot be transvections in a symplectic two-group

In the four actual unipotent coordinates, an involution has one outside
coordinate zero. Its commutator has central coordinates (c²v+b²a, cv+ba).
Natural displacement of dimension at most one forces the second coordinate
zero, and the involution equation then forces the first zero as well.
Inner Sylow conjugacy transports the calculation to every two-subgroup,
preserving the natural moved space, rather than an abstract Sylow marking.

This is the Sylow calculation used in MS93 (3.6), printed p.871, before
centralization of the secondary commutator. The original-geometry consumer
is CoreReconstruction.RootCommutator and GenerationTwoSymplecticCommutator.
-/

public noncomputable section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

private theorem theta_move (s t : F) (v : Vector F) :
    (theta s t).val • v - v =
      Sum.elim ![s * v (.inr 0) + t * v (.inr 1),t * v (.inr 0)] 0 := by
  rw [smul_eq_mulVec]
  change (element 0 s t 0).val.val *ᵥ v - v = _
  rw [element_matrix]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks]

private theorem theta_movedSpace (s : F) {t : F} (ht : t ≠ 0) :
    movedSpace (theta s t).val = plane F := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    change (theta s t).val • v - v ∈ plane F
    rw [theta_move]
    intro i
    rfl
  · intro hx
    refine ⟨Sum.elim 0 ![x (.inl 1) / t,(x (.inl 0) - s * (x (.inl 1) / t)) / t],?_⟩
    change (theta s t).val • (Sum.elim 0 ![x (.inl 1) / t,
      (x (.inl 0) - s * (x (.inl 1) / t)) / t] : Vector F) - _ = _
    simp only [LinearMap.id_apply]
    rw [theta_move]
    funext i
    rcases i with i | i <;> fin_cases i
    · change s * (x (.inl 1) / t) + t * ((x (.inl 0) - s * (x (.inl 1) / t)) / t) = x (.inl 0)
      field_simp [ht]
      ring
    · change t * (x (.inl 1) / t) = x (.inl 1)
      field_simp [ht]
    · exact ((mem_plane _).mp hx 0).symm
    · exact ((mem_plane _).mp hx 1).symm

/-- The second central root coordinate vanishes when the natural movement
has dimension at most one. -/
theorem theta_second_eq_zero_of_movedSpace_le_one (s t : F)
    (hd : Module.finrank F (movedSpace (theta s t).val) ≤ 1) : t = 0 := by
  by_contra ht
  rw [theta_movedSpace s ht,finrank_plane] at hd
  omega

/-- The actual two-coordinate Sylow commutator formula. -/
theorem element_commutator (b u w v c z t a : F) :
    ⁅element b u w v,element c z t a⁆ = theta (c^2*v+b^2*a) (c*v+b*a) := by
  rw [commutatorElement_def,mul_inv_eq_iff_eq_mul,mul_inv_eq_iff_eq_mul]
  rw [theta,element_mul,element_mul,element_mul,element_eq_iff]
  constructor
  · ring
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · ring

variable [Finite F]

/-- A Sylow commutator with an involution cannot be a nonidentity
transvection in the natural four-space. -/
theorem involution_commutator_eq_one_of_movedSpace_le_one
    (x y : unipotent (F := F)) (hx : x^2 = 1)
    (hd : Module.finrank F (movedSpace (⁅x,y⁆ : unipotent (F := F)).val) ≤ 1) :
    ⁅x,y⁆ = 1 := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
  dsimp only [Prod.fst, Prod.snd] at hx hd ⊢
  rw [element_commutator] at hd ⊢
  have hzero := theta_second_eq_zero_of_movedSpace_le_one _ _ hd
  rw [element_square,theta,←element_zero,element_eq_iff] at hx
  have hbv : b*v=0 := hx.2.2.1
  rcases mul_eq_zero.mp hbv with hb | hv
  · rw [hb,zero_mul,add_zero] at hzero
    rcases mul_eq_zero.mp hzero with hc | hv
    · simp [hb,hc,theta,element_zero]
    · simp [hb,hv,theta,element_zero]
  · rw [hv,mul_zero,zero_add] at hzero
    rcases mul_eq_zero.mp hzero with hb | ha
    · simp [hv,hb,theta,element_zero]
    · simp [hv,ha,theta,element_zero]

/-- The same calculation in any actual two-subgroup of Sp₄, transported
by an inner Sylow conjugation, so natural moved spaces are preserved. -/
theorem twoGroup_involution_commutator_eq_one
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (P : Subgroup (Sp F)) (hp : IsPGroup 2 P)
    (x y : Sp F) (hxP : x ∈ P) (hyP : y ∈ P) (hx : x^2=1)
    (hd : Module.finrank F (movedSpace ⁅x,y⁆) ≤ 1) : ⁅x,y⁆ = 1 := by
  obtain ⟨S,hPS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
  have hmap : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let f := (MulAut.conj g).toMonoidHom
  let X : unipotent (F := F) := ⟨f x,hmap ▸ mem_map_of_mem f (hPS hxP)⟩
  let Y : unipotent (F := F) := ⟨f y,hmap ▸ mem_map_of_mem f (hPS hyP)⟩
  have hX : X^2=1 := by
    apply Subtype.ext
    change (f x)^2 = 1
    rw [←map_pow,hx,map_one]
  have hXY : (⁅X,Y⁆ : unipotent (F := F)).val = g*⁅x,y⁆*g⁻¹ :=
    (map_commutatorElement f x y).symm
  have hdim : Module.finrank F (movedSpace (⁅X,Y⁆ : unipotent (F := F)).val) ≤ 1 := by
    rw [hXY,movedSpace_conj,(toLinear g).finrank_map_eq]
    exact hd
  have he := congrArg Subtype.val (involution_commutator_eq_one_of_movedSpace_le_one X Y hX hdim)
  apply (MulAut.conj g).injective
  simpa only [hXY,Subgroup.coe_one,map_one,MulAut.conj_apply] using he

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
