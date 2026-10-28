module

public import Theory.SpecificGroups.Suzuki.RootSquareFibers
public import Theory.GroupTheory.CoveringMultiplierAction
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# The Sylow preimage in a covering of Sz(8)

Compose the given covering with the actual matrix isomorphism, and take
its full preimage of the standard root subgroup. A kernel of order four
makes this preimage a Sylow two-subgroup of order 256. Central Sylow
transfer places the kernel in its derived subgroup; that derived subgroup
therefore has order 32, since the root group's derived subgroup has order 8.

These are the cardinality and transfer steps in GLS3, section 6.3,
`refs/KGroup/GLS3/chapter6.tex`, the Sz(8) case on printed p.337.
No assertion about the field action on the kernel is an input or conclusion.
-/

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory PFAppendixIII

universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- The specified covering, with its target identified with the matrix model. -/
@[expose] public noncomputable def matrixProjection
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) : U →* SuzukiMatrixGroup 1 :=
  e.toMonoidHom.comp f.toMonoidHom

@[simp] public theorem matrixProjection_ker
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    (matrixProjection e f).ker = f.toMonoidHom.ker :=
  MonoidHom.ker_comp_of_injective _ _ e.injective

public theorem matrixProjection_surjective
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    Function.Surjective (matrixProjection e f) := e.surjective.comp f.surjective

/-- The full preimage of the literal standard root group. -/
@[expose] public noncomputable def rootPreimage
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) : Subgroup U :=
  (SuzukiRootSubgroup 1).comap (matrixProjection e f)

/-- Restrict the original map to the root preimage, retaining the root carrier. -/
@[expose] public noncomputable def rootProjection
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    rootPreimage e f →* SuzukiRootSubgroup 1 :=
  ((matrixProjection e f).comp (rootPreimage e f).subtype).codRestrict
    (SuzukiRootSubgroup 1) (fun x => x.property)

public theorem rootProjection_surjective
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    Function.Surjective (rootProjection e f) := by
  intro x
  obtain ⟨y, hy⟩ := matrixProjection_surjective e f x
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change matrixProjection e f y ∈ SuzukiRootSubgroup 1
  rw [hy]
  exact x.property

public theorem ker_le_rootPreimage
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    f.toMonoidHom.ker ≤ rootPreimage e f := by
  rw [← matrixProjection_ker e f]
  exact (SuzukiRootSubgroup 1).ker_le_comap _

@[simp] public theorem rootProjection_ker
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    (rootProjection e f).ker = f.toMonoidHom.ker.subgroupOf (rootPreimage e f) := by
  ext x
  change (⟨matrixProjection e f x, _⟩ : SuzukiRootSubgroup 1) = 1 ↔ f x = 1
  rw [Subtype.ext_iff]
  change e (f x) = 1 ↔ f x = 1
  rw [← e.map_one, e.injective.eq_iff]

public theorem rootProjection_ker_card
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Nat.card (rootProjection e f).ker = 4 := by
  rw [rootProjection_ker, Nat.card_congr
    (subgroupOfEquivOfLe (ker_le_rootPreimage e f)).toEquiv, hfour]

public theorem rootProjection_ker_le_center
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    (rootProjection e f).ker ≤ center (rootPreimage e f) := by
  rw [rootProjection_ker]
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hx) y)

/-- The full root preimage is Sylow, since the full covering kernel is a two-group. -/
public theorem rootPreimage_isSylow
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    ∃ P : Sylow 2 U, (P : Subgroup U) = rootPreimage e f := by
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
  have hk : IsPGroup 2 (matrixProjection e f).ker := by
    rw [matrixProjection_ker]
    exact IsPGroup.of_card (p := 2) (n := 2) hfour
  refine ⟨R.comapOfKerIsPGroup (matrixProjection e f) hk ?_, ?_⟩
  · rw [MonoidHom.range_eq_top.mpr (matrixProjection_surjective e f)]
    exact le_top
  · change (R : Subgroup _).comap (matrixProjection e f) = _
    rw [hR]
    rfl

/-- A four-kernel makes the lifted Sylow group have order 4·64. -/
public theorem rootPreimage_card
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Nat.card (rootPreimage e f) = 256 := by
  have h := (rootProjection e f).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (rootProjection_surjective e f),
    card_top, rootProjection_ker_card e f hfour,
    suzukiRootSubgroup_card 1 (by decide)] at h
  norm_num at h
  exact h.symm

/-- Central Sylow transfer puts the actual restricted kernel in the derived group. -/
public theorem rootProjection_ker_le_commutator
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    (rootProjection e f).ker ≤ _root_.commutator (rootPreimage e f) := by
  obtain ⟨P, hP⟩ := rootPreimage_isSylow e f hfour
  rw [rootProjection_ker]
  intro x hx
  have htransfer : (x : U) ∈ ⁅rootPreimage e f, rootPreimage e f⁆ := by
    have hxP : (x : U) ∈ (P : Subgroup U) := by simpa only [hP] using x.property
    have ht : (x : U) ∈ ⁅(P : Subgroup U), (P : Subgroup U)⁆ :=
      center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨f.ker_le_center hx, by
        rw [Group.IsPerfect.commutator_eq_top]
        exact mem_top _⟩, hxP⟩
    simpa only [hP] using ht
  rw [← map_subtype_commutator] at htransfer
  obtain ⟨y, hy, he⟩ := htransfer
  exact (Subtype.ext he : y = x) ▸ hy

/-- The standard root group's derived group has order eight. -/
public theorem root_commutator_card : Nat.card (_root_.commutator (SuzukiRootSubgroup 1)) = 8 := by
  let F := BinaryGaloisField 3
  let pi : F ≃+* F := iterateFrobeniusEquiv F 2 2
  have hpi : ∀ x : F, pi x = x ^ (2 ^ 2) := iterateFrobeniusEquiv_def F 2 2
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _, _⟩ :=
    External.huppert_blackburn_XI_3_1 1 (by decide) pi
      (External.binaryGaloisField_tits_formula_sq 1 pi hpi)
  change _root_.commutator (SuzukiRootClosure 1) = center (SuzukiRootClosure 1) at hc
  let eR : SuzukiRootSubgroup 1 ≃* SuzukiRootClosure 1 :=
    subgroupOfEquivOfLe (suzukiRootClosure_le 1)
  calc
    Nat.card (_root_.commutator (SuzukiRootSubgroup 1)) =
        Nat.card ((_root_.commutator (SuzukiRootSubgroup 1)).map eR.toMonoidHom) :=
      (card_map_of_injective eR.injective).symm
    _ = Nat.card (center (SuzukiRootClosure 1)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eR.surjective]
      change Nat.card (_root_.commutator (SuzukiRootClosure 1)) = _
      rw [hc]
    _ = Nat.card (center (SuzukiRootSubgroup 1)) :=
      (Nat.card_congr (centerCongr eR).toEquiv).symm
    _ = 8 := suzukiRootSubgroup_center_card 1 (by decide)

/-- The derived subgroup of the lifted Sylow has order 4·8, independently of
any assumption about the field action. -/
public theorem rootPreimage_commutator_card
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Nat.card (_root_.commutator (rootPreimage e f)) = 32 := by
  let q := rootProjection e f
  let D := _root_.commutator (rootPreimage e f)
  have hk : q.ker ≤ D := rootProjection_ker_le_commutator e f hfour
  have hker : Nat.card (q.ker.subgroupOf D) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv).trans
      (rootProjection_ker_card e f hfour)
  have himage : D.map q = _root_.commutator (SuzukiRootSubgroup 1) := by
    dsimp only [D]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (rootProjection_surjective e f)]
    rfl
  have h := (q.ker.subgroupOf D).card_mul_index
  change Nat.card (q.ker.subgroupOf D) * q.ker.relIndex D = Nat.card D at h
  rw [relIndex_ker, hker, himage, root_commutator_card] at h
  exact h.symm

end BenderSuzuki.MatrixGroups.MultiplierFieldAction
