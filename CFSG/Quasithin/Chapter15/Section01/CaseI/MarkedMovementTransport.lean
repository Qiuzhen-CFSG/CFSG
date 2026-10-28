module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedTransport
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Literal residual movement for a marked Case-I vector

The centralizer of the selected vector projects onto its actual image
stabilizer. Its two-residual has exactly the image residual, and the
linear displacement space therefore computes the original ambient
commutator. A bound on the fixed space then puts the central seed in
the join of the marked line and this moved subgroup. Residual
commutator idempotence supplies full movement without a model premise.

Source: Aschbacher--Smith 15.1.16 and 15.1.19(1), printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

/-- The literal residual acts fully on its original moved subgroup. -/
theorem marked_residual_movement
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (Z1 : Subgroup G) :
    let R := (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype
    ⁅V,R⁆ ≤ V ∧ ⁅⁅V,R⁆,R⁆ = ⁅V,R⁆ := by
  intro R
  have hRn : R ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans hn
  exact ⟨le_normalizer_iff_commutator_le_left.mp hRn,
    commutator_isPPerfect_idempotent R V (isPPerfect_embedded_pResidual 2 _)
      (IsElementaryAbelian.isPGroup 2 V) hRn⟩

/-- The original centralizer residual has the marked stabilizer residual as image. -/
theorem marked_residual_action_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let R := (pResidual 2 C).map C.subtype
    let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
    let a : R →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hRM)
    a.range = (pResidual 2 K).map K.subtype := by
  dsimp only
  let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
  let R := (pResidual 2 C).map C.subtype
  let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  let f := (actionHom M V hn).rangeRestrict
  let a := f.comp (inclusion hRM)
  obtain ⟨q,hq,hker,hcoord⟩ := vector_stabilizer_projection M V hn v K hK
  have he : (pResidual 2 C).map q = pResidual 2 K := map_pResidual_of_surjective 2 q hq
  change a.range = _
  rw [← he, map_map]
  ext d
  constructor
  · rintro ⟨r,rfl⟩
    obtain ⟨c,hc,hcr⟩ := r.property
    refine ⟨c,hc,?_⟩
    change (q c : internalActionImage M V hn) = f (inclusion hRM r)
    rw [hcoord]
    congr 1
    exact Subtype.ext hcr
  · rintro ⟨c,hc,rfl⟩
    refine ⟨⟨c,mem_map_of_mem C.subtype hc⟩,?_⟩
    change f ⟨(c:G),c.property.1⟩ = (q c : internalActionImage M V hn)
    exact (hcoord c).symm

/-- The model displacement is exactly the original ambient commutator. -/
theorem marked_residual_commutator_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let R := (pResidual 2 C).map C.subtype
    ⁅V,R⁆.subgroupOf V = binarySubgroup
      (subspaceCommutator (imageRepresentation M V hn) ⊤
        ((pResidual 2 K).map K.subtype)) := by
  intro C R
  let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  let a : R →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hRM)
  have hh := commutator_image_eq (imageRepresentation M V hn) V V R
    (hRM.trans hn) le_rfl a (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by
      ext x
      simp [binarySubgroup])
  rw [map_id] at hh
  have he : a.range = (pResidual 2 K).map K.subtype :=
    marked_residual_action_image M V hn v K hK
  rw [he] at hh
  exact hh

/-- A marked fixed-space bound places the actual central seed. -/
theorem marked_fixedSpace_seed_bound
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hb : fixedSpace (imageRepresentation M V hn)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ≤
      Submodule.span (ZMod 2) {v} ⊔ subspaceCommutator (imageRepresentation M V hn)
        ⊤ ((pResidual 2 K).map K.subtype)) :
    let Z1 := zpowers (v.toMul : G)
    let R := (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype
    centralInvolutions T ⊓ V ≤ Z1 ⊔ ⁅V,R⁆ := by
  intro Z1 R
  let W := binarySpace ((Z1 ⊔ ⁅V,R⁆).subgroupOf V)
  have hline : Submodule.span (ZMod 2) {v} ≤ W := by
    apply Submodule.span_le.mpr
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact (show Z1 ≤ Z1 ⊔ ⁅V,R⁆ from le_sup_left) (mem_zpowers _)
  have hmove : subspaceCommutator (imageRepresentation M V hn) ⊤
      ((pResidual 2 K).map K.subtype) ≤ W := by
    intro w hw
    have hh : w.toMul ∈ ⁅V,R⁆.subgroupOf V := by
      rw [marked_residual_commutator_image M V hn v K hK]
      exact hw
    exact (show ⁅V,R⁆ ≤ Z1 ⊔ ⁅V,R⁆ from le_sup_right) hh
  intro z hz
  let w : Additive V := Additive.ofMul ⟨z,hz.2⟩
  have hw : w ∈ fixedSpace (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) := by
    rintro ⟨d,⟨t,ht,rfl⟩⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (t:G) * z * (t:G)⁻¹ = z
    rw [((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.2 t ht, mul_inv_cancel_right]
  exact (sup_le hline hmove) (hb hw)
end CFSG.Quasithin.Chapter15.Section01
