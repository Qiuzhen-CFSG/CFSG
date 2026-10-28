module
public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Coordinates
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Representation.HermitianTensorThree.Root
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Maximal elementary subgroups of the descended Hermitian image

Sylow conjugacy in the actual special-linear cover puts an elementary
subgroup into the upper-unitriangular group. A subgroup of binary rank
4n is then one of its two root planes. Their fixed Hermitian matrices
have respectively one fixed-field coordinate and a two-by-two Hermitian
corner, of binary dimensions n and 4n. Thus the latter fixed dimension
selects the marked plane root group, including n = 1.

The same calculation proves uniqueness inside a common two-subgroup.
Consequently a two-subgroup of the binary normalizer containing this
inner actor normalizes it. These are literal subgroup and action
identifications, used for the relative-normality assertion in 8.2.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof
of H.4.4, printed p.381, and the Hermitian row of 8.2.5, printed pp.716–717.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.HermitianTensorThree.UnipotentRadicals
variable (n : ℕ) [NeZero n]
local instance : Finite (Space n ≃ₗ[ZMod 2] Space n) :=
  Finite.of_injective (fun e : Space n ≃ₗ[ZMod 2] Space n => (e : Space n → Space n))
    DFunLike.coe_injective

def unipotentHom : U (E n) →* (Space n ≃ₗ[ZMod 2] Space n) :=
  (binaryActionHom n).comp (specialLinear (E n))

def point : Subgroup (Space n ≃ₗ[ZMod 2] Space n) := (V₁ (E n)).map (unipotentHom n)
def plane : Subgroup (Space n ≃ₗ[ZMod 2] Space n) := (V₂ (E n)).map (unipotentHom n)

theorem unipotentHom_injective : Function.Injective (unipotentHom n) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply _root_.eq_bot_iff.mpr
  intro a ha
  have hk : specialLinear (E n) a ∈ (binaryActionHom n).ker := ha
  rw [binaryActionHom_ker_eq, mem_actionHom_ker_iff] at hk
  obtain ⟨c, hc, _, _⟩ := hk
  have hc1 : c = 1 := (congrArg (fun X : Mat n => X 0 0) hc).symm
  apply specialLinear_injective (E n)
  rw [map_one]
  apply Subtype.ext
  simpa [hc1] using hc

private def coverSylow : Sylow 2 (Cover n) := by
  let P := Matrix.PSL3.LinearThree.unipotentSL (E n)
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := (2*n)*3) (by
    rw [Matrix.PSL3.LinearThree.card_unipotentSL, card_E, ← pow_mul])
  apply hp.toSylow
  have hc : Nat.card (Cover n) = Nat.card (E n)^3 *
      (Nat.card (E n)^3-1) * (Nat.card (E n)^2-1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Cover n)),
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    exact Matrix.PSL3.LinearThree.card_projective_mul_scalar (E n)
  have hi := P.card_mul_index
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, hc] at hi
  have hi' : P.index = (Nat.card (E n)^3-1) * (Nat.card (E n)^2-1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card (E n)^3 from pow_pos Nat.card_pos _)
    simpa only [mul_assoc] using hi
  rw [hi']
  have he : Nat.card (E n) % 2 = 0 := by
    rw [card_E]
    simp [Nat.pow_mod, Nat.ne_of_gt (NeZero.pos n)]
  have h2 : ¬ 2 ∣ Nat.card (E n)^2-1 := by
    have hp : 0 < Nat.card (E n)^2 := pow_pos Nat.card_pos _
    have : Nat.card (E n)^2 % 2 = 0 := by simp [Nat.pow_mod, he]
    omega
  have h3 : ¬ 2 ∣ Nat.card (E n)^3-1 := by
    have hp : 0 < Nat.card (E n)^3 := pow_pos Nat.card_pos _
    have : Nat.card (E n)^3 % 2 = 0 := by simp [Nat.pow_mod, he]
    omega
  exact Nat.prime_two.not_dvd_mul h3 h2

private def imageSylow : Sylow 2 (binaryImage n) :=
  (coverSylow n).mapSurjective (MonoidHom.rangeRestrict_surjective (binaryActionHom n))

private theorem imageSylow_map :
    ((imageSylow n : Subgroup (binaryImage n)).map (binaryImage n).subtype) =
      (unipotentHom n).range := by
  change (((coverSylow n : Subgroup (Cover n)).map
    (binaryActionHom n).rangeRestrict).map (binaryImage n).subtype) = _
  change (((coverSylow n : Subgroup (Cover n)).map
    (binaryActionHom n).rangeRestrict).map (binaryActionHom n).range.subtype) = _
  rw [map_map]
  change (Matrix.PSL3.LinearThree.unipotentSL (E n)).map (binaryActionHom n) = _
  rw [← Matrix.PSL3.LinearThree.specialLinear_range, ← MonoidHom.range_comp]
  rfl

private theorem maximal_elementary_in_unipotent
    (A : Subgroup (U (E n))) [IsElementaryAbelian 2 A] (hA : rank A = 4*n) :
    A = V₁ (E n) ∨ A = V₂ (E n) := by
  have hcard : Nat.card A = 2^(4*n) := by
    rw [← hA]
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [rank, hm, Nat.log_pow (by decide : 1 < 2)]
  have hc₁ : Nat.card (V₁ (E n)) = 2^(4*n) := by
    rw [card_V₁, card_E, ← pow_mul]
    congr 1
    omega
  have hc₂ : Nat.card (V₂ (E n)) = 2^(4*n) := by
    rw [card_V₂, card_E, ← pow_mul]
    congr 1
    omega
  rcases elementary_le_plane (E n) A with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [hcard, hc₁]))
  · exact Or.inr (eq_of_le_of_card_ge h (by rw [hcard, hc₂]))

theorem maximal_elementary_conjugate
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAL : A ≤ binaryImage n) (hA : rank A = 4*n) :
    ∃ c : Cover n, A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom = point n ∨
      A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom = plane n := by
  let A' := A.subgroupOf (binaryImage n)
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAL
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 A').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (binaryImage n) S (imageSylow n)
  obtain ⟨c, hc⟩ := g.property
  let f := (MulAut.conj g.val).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g.val).injective
  have hB : A.map f ≤ (unipotentHom n).range := by
    rw [← imageSylow_map]
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hS
    change _ ≤ ((g • S : Sylow 2 (binaryImage n)) : Subgroup (binaryImage n)) at hmap
    rw [hg] at hmap
    have hh := map_mono (f := (binaryImage n).subtype) hmap
    rw [map_map] at hh
    have he : (binaryImage n).subtype.comp (MulAut.conj g).toMonoidHom =
        f.comp (binaryImage n).subtype := rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hAL] at hh
    exact hh
  let B := (A.map f).comap (unipotentHom n)
  have hBinj : Function.Injective ((unipotentHom n).subgroupComap (A.map f)) :=
    fun a b h => Subtype.ext (unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hBinj
  have hBm : B.map (unipotentHom n) = A.map f := map_comap_eq_self hB
  have hBr : rank B = 4*n := by
    rw [← rank_map_injective (unipotentHom n) (unipotentHom_injective n), hBm,
      rank_map_injective f hf, hA]
  refine ⟨c, ?_⟩
  rw [hc]
  rcases maximal_elementary_in_unipotent n B hBr with hb | hb
  · exact Or.inl (hBm.symm.trans (congrArg (Subgroup.map (unipotentHom n)) hb))
  · exact Or.inr (hBm.symm.trans (congrArg (Subgroup.map (unipotentHom n)) hb))

/-- These are the binary images of the previously marked root planes. -/
theorem point_eq_marked : point n = (coverPointRadical n).map (binaryActionHom n) := by
  rw [coverPointRadical, map_map]
  rfl

theorem plane_eq_marked : plane n = (coverPlaneRadical n).map (binaryActionHom n) := by
  rw [coverPlaneRadical, map_map]
  rfl

def ambientAction : Representation (ZMod 2) (Space n ≃ₗ[ZMod 2] Space n) (Space n) where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem fixed_conditions (X : Space n)
    (h : ∀ t : E n, action n (rootHom n (Multiplicative.ofAdd t)) X = X) :
    X.val 2 2 = 0 ∧ X.val 1 2 = 0 ∧ X.val 0 2 = 0 := by
  obtain ⟨h22, h12, h02⟩ := (root_action_iff n X).mp (h 1)
  obtain ⟨t, ht⟩ := FieldSections.exists_sigma_ne n
  have he := congrArg (fun Y : Space n => Y.val 0 0) (h t)
  change ((!![1,0,t;0,1,0;0,0,1] : Mat n) * X.val *
    adjoint n !![1,0,t;0,1,0;0,0,1]) 0 0 = X.val 0 0 at he
  have h20 : X.val 2 0 = X.val 0 2 := (entry_conjugate n X 2 0).symm.trans h02
  simp only [adjoint, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.transpose_apply, Matrix.map_apply] at he
  simp [h22, h20] at he
  have hz : (t + sigma n t) * X.val 0 2 = 0 := by linear_combination he
  have hn : t + sigma n t ≠ 0 := fun hh => ht (CharTwo.add_eq_zero.mp hh).symm
  exact ⟨h22, h12, (mul_eq_zero.mp hz).resolve_left hn⟩

theorem mem_plane_fixed_iff (X : Space n) :
    X ∈ fixedSpace (ambientAction n) (plane n) ↔
      X.val 2 2 = 0 ∧ X.val 1 2 = 0 ∧ X.val 0 2 = 0 := by
  constructor
  · intro h
    apply fixed_conditions n X
    intro t
    exact h ⟨unipotentHom n ⟨0,0,t⟩,
      mem_map_of_mem _ ((mem_V₂ (E n) _).mpr rfl)⟩
  · rintro ⟨h22,h12,h02⟩ ⟨_, a, ha, rfl⟩
    have hx : a.x = 0 := (mem_V₂ (E n) a).mp ha
    have h20 : X.val 2 0 = 0 := by rw [← entry_conjugate n X 2 0,h02,map_zero]
    have h21 : X.val 2 1 = 0 := by rw [← entry_conjugate n X 2 1,h12,map_zero]
    apply Subtype.ext
    change matrix (E n) a * X.val * adjoint n (matrix (E n) a) = X.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix,hx,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
        h22,h12,h02,h20,h21]

theorem mem_point_fixed_iff (X : Space n) :
    X ∈ fixedSpace (ambientAction n) (point n) ↔
      X.val 1 1 = 0 ∧ X.val 2 2 = 0 ∧ X.val 0 1 = 0 ∧
        X.val 0 2 = 0 ∧ X.val 1 2 = 0 := by
  constructor
  · intro h
    have hroot (a c : E n) : action n (specialLinear (E n) ⟨a,0,c⟩) X = X :=
      h ⟨unipotentHom n ⟨a,0,c⟩,
        mem_map_of_mem _ ((mem_V₁ (E n) _).mpr rfl)⟩
    obtain ⟨h22,h12,h02⟩ := fixed_conditions n X (fun c => hroot 0 c)
    have h11 : X.val 1 1 = 0 := by
      have hh := congrArg (fun Y : Space n => Y.val 0 1) (hroot 1 0)
      change ((!![1,1,0;0,1,0;0,0,1] : Mat n) * X.val *
        adjoint n !![1,1,0;0,1,0;0,0,1]) 0 1 = X.val 0 1 at hh
      simpa [adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three] using hh
    have he (t : E n) := congrArg (fun Y : Space n => Y.val 0 0) (hroot t 0)
    have he' (t : E n) : t * X.val 1 0 + sigma n t * X.val 0 1 = 0 := by
      have hh := he t
      change ((!![1,t,0;0,1,0;0,0,1] : Mat n) * X.val *
        adjoint n !![1,t,0;0,1,0;0,0,1]) 0 0 = X.val 0 0 at hh
      simp only [adjoint,Matrix.mul_apply,
        Fin.sum_univ_three,Matrix.transpose_apply,Matrix.map_apply] at hh
      simp [h11] at hh
      linear_combination hh
    have h10 : X.val 1 0 = X.val 0 1 := by
      have hh := he' 1
      simpa only [map_one,one_mul,CharTwo.add_eq_zero] using hh
    obtain ⟨t,ht⟩ := FieldSections.exists_sigma_ne n
    have hz : (t+sigma n t)*X.val 0 1 = 0 := by
      have hh := he' t
      rw [h10] at hh
      linear_combination hh
    have hn : t+sigma n t ≠ 0 := fun hh => ht (CharTwo.add_eq_zero.mp hh).symm
    exact ⟨h11,h22,(mul_eq_zero.mp hz).resolve_left hn,h02,h12⟩
  · rintro ⟨h11,h22,h01,h02,h12⟩ ⟨_, a, ha, rfl⟩
    have hy : a.y = 0 := (mem_V₁ (E n) a).mp ha
    have h10 : X.val 1 0 = 0 := by rw [← entry_conjugate n X 1 0,h01,map_zero]
    have h20 : X.val 2 0 = 0 := by rw [← entry_conjugate n X 2 0,h02,map_zero]
    have h21 : X.val 2 1 = 0 := by rw [← entry_conjugate n X 2 1,h12,map_zero]
    apply Subtype.ext
    change matrix (E n) a * X.val * adjoint n (matrix (E n) a) = X.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix,hy,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
        h11,h22,h01,h12,h02,h10,h20,h21]

/-- The point radical fixes just the first diagonal coordinate. -/
def pointFixedCoordinates : fixedSpace (ambientAction n) (point n) ≃ F n where
  toFun X := ⟨X.val.val 0 0, entry_conjugate n X.val 0 0⟩
  invFun c := ⟨(HermitianTensorThree.coordinates n).symm (![c,0,0], ![0,0,0]),
    (mem_point_fixed_iff n _).mpr ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  left_inv X := by
    obtain ⟨h11,h22,h01,h02,h12⟩ := (mem_point_fixed_iff n X.val).mp X.property
    have h10 : X.val.val 1 0 = 0 := by rw [← entry_conjugate n X.val 1 0,h01,map_zero]
    have h20 : X.val.val 2 0 = 0 := by rw [← entry_conjugate n X.val 2 0,h02,map_zero]
    have h21 : X.val.val 2 1 = 0 := by rw [← entry_conjugate n X.val 2 1,h12,map_zero]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianTensorThree.coordinates,h11,h22,h01,h02,h12,h10,h20,h21]
  right_inv _ := rfl

/-- The plane radical fixes the Hermitian two-by-two corner. -/
def planeFixedCoordinates : fixedSpace (ambientAction n) (plane n) ≃ (F n × F n) × E n where
  toFun X := ((⟨X.val.val 0 0, entry_conjugate n X.val 0 0⟩,
    ⟨X.val.val 1 1, entry_conjugate n X.val 1 1⟩), X.val.val 0 1)
  invFun v := ⟨(HermitianTensorThree.coordinates n).symm (![v.1.1,v.1.2,0], ![v.2,0,0]),
    (mem_plane_fixed_iff n _).mpr ⟨rfl,rfl,rfl⟩⟩
  left_inv X := by
    obtain ⟨h22,h12,h02⟩ := (mem_plane_fixed_iff n X.val).mp X.property
    have h20 : X.val.val 2 0 = 0 := by rw [← entry_conjugate n X.val 2 0,h02,map_zero]
    have h21 : X.val.val 2 1 = 0 := by rw [← entry_conjugate n X.val 2 1,h12,map_zero]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianTensorThree.coordinates,entry_conjugate,h22,h12,h02,h20,h21]
  right_inv _ := rfl

theorem finrank_point_fixed : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) (point n)) = n := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (ambientAction n) (point n))
  rw [Nat.card_zmod, Nat.card_congr (pointFixedCoordinates n),card_F] at h
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) h).symm

theorem finrank_plane_fixed : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) (plane n)) = 4*n := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (ambientAction n) (plane n))
  rw [Nat.card_zmod, Nat.card_congr (planeFixedCoordinates n),
    Nat.card_prod,Nat.card_prod,card_F,card_E,← pow_add,← pow_add] at h
  have hh := (Nat.pow_right_injective (by decide : 2 ≤ 2)) h
  omega

/-- The fixed rank in the saturated offender selects the plane radical,
including half-degree one. -/
theorem maximal_elementary_plane_of_fixedRank
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAL : A ≤ binaryImage n) (hA : rank A = 4*n)
    (hfix : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) A) = 4*n) :
    ∃ c : Cover n, A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom = plane n := by
  obtain ⟨c,hc | hc⟩ := maximal_elementary_conjugate n A hAL hA
  · have hd := (fixedSpaceConjEquiv (ambientAction n) A (binaryActionHom n c)).finrank_eq
    rw [hc,finrank_point_fixed,hfix] at hd
    have hn := NeZero.pos n
    omega
  · exact ⟨c,hc⟩

private theorem two_subgroup_conjugate_le_unipotent
    (P : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hp : IsPGroup 2 P) (hPL : P ≤ binaryImage n) :
    ∃ c : Cover n, P.map (MulAut.conj (binaryActionHom n c)).toMonoidHom ≤
      (unipotentHom n).range := by
  let P' := P.subgroupOf (binaryImage n)
  have hp' : IsPGroup 2 P' := hp.comap_subtype
  obtain ⟨S, hS⟩ := hp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (binaryImage n) S (imageSylow n)
  obtain ⟨c, hc⟩ := g.property
  refine ⟨c, ?_⟩
  rw [hc, ← imageSylow_map]
  have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hS
  change _ ≤ ((g • S : Sylow 2 (binaryImage n)) : Subgroup (binaryImage n)) at hmap
  rw [hg] at hmap
  have hh := map_mono (f := (binaryImage n).subtype) hmap
  rw [map_map] at hh
  have he : (binaryImage n).subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp (binaryImage n).subtype := rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hPL] at hh
  exact hh

private theorem eq_plane_of_le_unipotent
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAU : A ≤ (unipotentHom n).range) (hA : rank A = 4*n)
    (hfix : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) A) = 4*n) : A = plane n := by
  let B := A.comap (unipotentHom n)
  have hi : Function.Injective ((unipotentHom n).subgroupComap A) :=
    fun a b h => Subtype.ext (unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hi
  have hm : B.map (unipotentHom n) = A := map_comap_eq_self hAU
  have hr : rank B = 4*n := by
    rw [← rank_map_injective (unipotentHom n) (unipotentHom_injective n),hm,hA]
  rcases maximal_elementary_in_unipotent n B hr with h | h
  · have he : A = point n := hm.symm.trans (congrArg (Subgroup.map (unipotentHom n)) h)
    rw [he, finrank_point_fixed] at hfix
    have hn := NeZero.pos n
    omega
  · exact hm.symm.trans (congrArg (Subgroup.map (unipotentHom n)) h)

/-- In a common two-subgroup of the component image the saturated plane
radical is unique, as measured by its actor and fixed ranks. -/
theorem eq_of_le_two_subgroup
    (P : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hp : IsPGroup 2 P) (hPL : P ≤ binaryImage n)
    (A B : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAP : A ≤ P) (hBP : B ≤ P) (hA : rank A = 4*n) (hB : rank B = 4*n)
    (hAf : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) A) = 4*n)
    (hBf : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) B) = 4*n) : A = B := by
  obtain ⟨c,hc⟩ := two_subgroup_conjugate_le_unipotent n P hp hPL
  let f := (MulAut.conj (binaryActionHom n c)).toMonoidHom
  have he (D : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 D]
      (hDP : D ≤ P) (hr : rank D = 4*n)
      (hd : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) D) = 4*n) :
      D.map f = plane n := by
    let : IsElementaryAbelian 2 (D.map f) := IsElementaryAbelian.map f
    apply eq_plane_of_le_unipotent n (D.map f) ((map_mono hDP).trans hc)
    · rwa [rank_map_conj]
    · exact (fixedSpaceConjEquiv (ambientAction n) D (binaryActionHom n c)).finrank_eq.symm.trans hd
  exact Subgroup.map_injective (MulAut.conj (binaryActionHom n c)).injective
    ((he A hAP hA hAf).trans (he B hBP hB hBf).symm)

/-- A two-subgroup of the full normalizer containing a saturated inner
plane radical normalizes it. Normality is relative to that two-subgroup. -/
theorem le_normalizer_of_le_two_subgroup
    (P : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hp : IsPGroup 2 P) (hPN : P ≤ binaryNormalizer n)
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAP : A ≤ P) (hAL : A ≤ binaryImage n) (hA : rank A = 4*n)
    (hAf : Module.finrank (ZMod 2) (fixedSpace (ambientAction n) A) = 4*n) :
    P ≤ normalizer (A : Set (Space n ≃ₗ[ZMod 2] Space n)) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  let f := (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hconj : A.map f ≤ P ⊓ binaryImage n := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨P.mul_mem (P.mul_mem hg (hAP ha)) (P.inv_mem hg),
      (mem_normalizer_iff.mp (hPN hg) a).mp (hAL ha)⟩
  apply eq_of_le_two_subgroup n (P ⊓ binaryImage n) hp.to_inf_left inf_le_right
    (A.map f) A hconj (le_inf hAP hAL)
  · rwa [rank_map_conj]
  · exact hA
  · exact (fixedSpaceConjEquiv (ambientAction n) A g).finrank_eq.symm.trans hAf
  · exact hAf

end Representation.HermitianTensorThree.UnipotentRadicals
