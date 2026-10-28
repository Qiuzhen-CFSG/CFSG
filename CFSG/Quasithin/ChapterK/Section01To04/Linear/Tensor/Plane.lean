module

public import CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor
public import CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# The attaining plane radical for the Hermitian tensor

Inside each literal source overgroup, the two root planes are mapped from the
natural SL₃ cover. The map is proved injective on the whole unitriangular
group; no faithfulness of the cover representation is assumed. The plane
radical has binary rank 4n and fixes the Hermitian upper left block, also of
binary dimension 4n. Its successive displacements kill the last diagonal,
then the last column, then the whole vector. Thus it is cubic and attains
ratio 5/4 on the actual descended module of dimension 9n.

This proves the upper bound in K.3.2.4. The global lower bound, quadratic
exclusion and minimizing-actor classification are separate obligations.
The image and overgroup conventions retain SL₃ for even n and PSL₃ for odd n.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467; H.4.4(1), printed pp.380–381.
-/

@[expose] public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

def coverToOvergroup : Cover n →* M :=
  (binaryActionHom n).codRestrict M (fun g => sourceOvergroup_contains_image n M hM ⟨g, rfl⟩)

def unipotentToOvergroup : U (E n) →* M :=
  (coverToOvergroup n M hM).comp (specialLinear (E n))

def planeActor : Subgroup M := (coverPlaneRadical n).map (coverToOvergroup n M hM)
def pointActor : Subgroup M := (coverPointRadical n).map (coverToOvergroup n M hM)

theorem planeActor_eq_map : planeActor n M hM =
    (V₂ (E n)).map (unipotentToOvergroup n M hM) := by
  rw [planeActor, coverPlaneRadical, Subgroup.map_map]
  rfl

theorem pointActor_eq_map : pointActor n M hM =
    (V₁ (E n)).map (unipotentToOvergroup n M hM) := by
  rw [pointActor, coverPointRadical, Subgroup.map_map]
  rfl

theorem unipotentToOvergroup_injective :
    Function.Injective (unipotentToOvergroup n M hM) := by
  apply (unipotentToOvergroup n M hM).ker_eq_bot_iff.mp
  apply bot_unique
  intro u hu
  have hu' : specialLinear (E n) u ∈ (binaryActionHom n).ker :=
    congrArg Subtype.val hu
  rw [binaryActionHom_ker_eq] at hu'
  obtain ⟨c, hc, _, _⟩ := (mem_actionHom_ker_iff n _).mp hu'
  have hc1 : (1 : E n) = c := by
    have h := congrArg (fun A : Mat n => A 0 0) hc
    exact h
  have hu1 : specialLinear (E n) u = 1 := by
    apply Subtype.ext
    simpa [← hc1] using hc
  exact (specialLinear_injective (E n)) (hu1.trans (map_one _).symm)

theorem card_planeActor : Nat.card (planeActor n M hM) = 2 ^ (4 * n) := by
  rw [planeActor_eq_map,
    ← Nat.card_congr ((V₂ (E n)).equivMapOfInjective _
      (unipotentToOvergroup_injective n M hM)).toEquiv,
    card_V₂, card_E, ← pow_mul]
  congr 1
  omega

theorem rank_planeActor : rank (planeActor n M hM) = 4 * n := by
  rw [rank, card_planeActor, Nat.log_pow (by decide : 1 < 2)]

theorem planeActor_elementary : IsElementaryTwo (planeActor n M hM) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hr := rank_planeActor n M hM
    rw [h, Representation.BinaryOffender.rank_bot] at hr
    have hn := NeZero.ne n
    omega
  · rw [planeActor_eq_map]
    exact IsElementaryAbelian.map _

/-- Matrix coordinates for a member of the plane radical, in the literal SL₃ cover. -/
def planeElement (a b : E n) : Cover n := specialLinear (E n) ⟨0,a,b⟩

omit hM M [NeZero n] in
theorem planeElement_matrix (a b : E n) :
    (planeElement n a b).val = !![1,0,b;0,1,a;0,0,1] := rfl

theorem planeElement_mem (a b : E n) :
    coverToOvergroup n M hM (planeElement n a b) ∈ planeActor n M hM := by
  rw [planeActor_eq_map]
  exact ⟨⟨0,a,b⟩, (mem_V₂ _ _).mpr rfl, rfl⟩

theorem planeActor_elements (g : M) : g ∈ planeActor n M hM ↔
    ∃ a b : E n, coverToOvergroup n M hM (planeElement n a b) = g := by
  rw [planeActor_eq_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hx := (mem_V₂ _ _).mp hu
    refine ⟨u.y, u.c, ?_⟩
    change unipotentToOvergroup n M hM ⟨0,u.y,u.c⟩ = unipotentToOvergroup n M hM u
    congr 1
    exact U.ext hx.symm rfl rfl
  · rintro ⟨a,b,rfl⟩
    exact ⟨⟨0,a,b⟩, (mem_V₂ _ _).mpr rfl, rfl⟩

omit hM M in
theorem planeElement_fixed (a b : E n) (X : Space n)
    (h02 : X.val 0 2 = 0) (h12 : X.val 1 2 = 0) (h22 : X.val 2 2 = 0) :
    action n (planeElement n a b) X = X := by
  have h20 : X.val 2 0 = 0 := by rw [← entry_conjugate n X 2 0, h02, map_zero]
  have h21 : X.val 2 1 = 0 := by rw [← entry_conjugate n X 2 1, h12, map_zero]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action_apply, planeElement_matrix, adjoint,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h02, h12, h22, h20, h21]

theorem mem_plane_fixed (X : Space n) :
    X ∈ fixedSpace (overgroupAction n M) (planeActor n M hM) ↔
      X.val 0 2 = 0 ∧ X.val 1 2 = 0 ∧ X.val 2 2 = 0 := by
  constructor
  · intro h
    have hz : action n (root n) X = X :=
      h ⟨coverToOvergroup n M hM (planeElement n 0 1), planeElement_mem n M hM 0 1⟩
    obtain ⟨h22,h12,_⟩ := (root_action_iff n X).mp hz
    have hy := congrArg (fun Y : Space n => Y.val 0 1)
      (h ⟨coverToOvergroup n M hM (planeElement n 1 0), planeElement_mem n M hM 1 0⟩)
    change (action n (planeElement n 1 0) X).val 0 1 = X.val 0 1 at hy
    have h02 : X.val 0 2 = 0 := by
      simpa [action_apply, planeElement_matrix, adjoint,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using hy
    exact ⟨h02,h12,h22⟩
  · rintro ⟨h02,h12,h22⟩ g
    obtain ⟨a,b,hg⟩ := (planeActor_elements n M hM g.val).mp g.property
    change overgroupAction n M g.val X = X
    rw [← hg]
    exact planeElement_fixed n a b X h02 h12 h22

/-- The fixed matrices are precisely the Hermitian upper left 2-by-2 block. -/
def planeFixedCoordinates :
    fixedSpace (overgroupAction n M) (planeActor n M hM) ≃ ((Fin 2 → F n) × E n) where
  toFun X := (![⟨X.val.val 0 0, entry_conjugate n X.val 0 0⟩,
    ⟨X.val.val 1 1, entry_conjugate n X.val 1 1⟩], X.val.val 0 1)
  invFun v := ⟨(Representation.HermitianTensorThree.coordinates n).symm
    (![v.1 0,v.1 1,0], ![v.2,0,0]), (mem_plane_fixed n M hM _).mpr ⟨rfl,rfl,rfl⟩⟩
  left_inv X := by
    obtain ⟨h02,h12,h22⟩ := (mem_plane_fixed n M hM X.val).mp X.property
    have h20 : X.val.val 2 0 = 0 := by
      rw [← entry_conjugate n X.val 2 0, h02, map_zero]
    have h21 : X.val.val 2 1 = 0 := by
      rw [← entry_conjugate n X.val 2 1, h12, map_zero]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Representation.HermitianTensorThree.coordinates, entry_conjugate, h02, h12, h22, h20, h21]
  right_inv v := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl

theorem finrank_plane_fixed :
    Module.finrank (ZMod 2) (fixedSpace (overgroupAction n M) (planeActor n M hM)) = 4 * n := by
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (overgroupAction n M) (planeActor n M hM))
  have hc : Nat.card (ZMod 2) = 2 := by simp
  rw [hc, Nat.card_congr (planeFixedCoordinates n M hM), Nat.card_prod,
    Nat.card_fun, Nat.card_fin, card_F, card_E, ← pow_mul, ← pow_add] at h2
  have he := (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2
  omega

theorem codim_plane_fixed : fixedCodim (overgroupAction n M) (planeActor n M hM) = 5 * n := by
  have h := fixedCodim_add_finrank (overgroupAction n M) (planeActor n M hM)
  rw [finrank_plane_fixed, finrank_binary] at h
  omega

omit hM M in
theorem plane_displacement_column (a b : E n) (X : Space n) :
    let D := binaryAction n (planeElement n a b) X - X
    D.val 0 2 = b * X.val 2 2 ∧ D.val 1 2 = a * X.val 2 2 ∧ D.val 2 2 = 0 := by
  dsimp only
  change (action n (planeElement n a b) X - X).val 0 2 = _ ∧ _
  simp [binaryAction_apply, action_apply, planeElement_matrix, adjoint,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem planeActor_cubic : IsCubic (overgroupAction n M) (planeActor n M hM) := by
  intro a ha b hb c hc X
  obtain ⟨a₁,a₂,rfl⟩ := (planeActor_elements n M hM a).mp ha
  obtain ⟨b₁,b₂,rfl⟩ := (planeActor_elements n M hM b).mp hb
  obtain ⟨c₁,c₂,rfl⟩ := (planeActor_elements n M hM c).mp hc
  let Y := binaryAction n (planeElement n c₁ c₂) X - X
  let Z := binaryAction n (planeElement n b₁ b₂) Y - Y
  have hY := (plane_displacement_column n c₁ c₂ X).2.2
  have hZ := plane_displacement_column n b₁ b₂ Y
  have hz02 : Z.val 0 2 = 0 := by rw [hZ.1, hY, mul_zero]
  have hz12 : Z.val 1 2 = 0 := by rw [hZ.2.1, hY, mul_zero]
  exact sub_eq_zero.mpr (planeElement_fixed n a₁ a₂ Z hz02 hz12 hZ.2.2)

theorem planeActor_ratio : actionRatio (overgroupAction n M) (planeActor n M hM) = 5 / 4 := by
  rw [actionRatio, codim_plane_fixed, rank_planeActor, Nat.cast_mul, Nat.cast_mul]
  have hn : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [ENNReal.mul_div_mul_right _ _ hn (by simp)]
  norm_num

include hM in
theorem cubicRatio_le_five_fourths : cubicRatio (overgroupAction n M) ≤ 5 / 4 := by
  exact (iInf_le_of_le (planeActor n M hM)
    (iInf_le_of_le ⟨planeActor_elementary n M hM, planeActor_cubic n M hM⟩ le_rfl)).trans_eq
      (planeActor_ratio n M hM)

end CFSG.Quasithin.ChapterK.Linear.Tensor
