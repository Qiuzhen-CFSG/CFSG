module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Coordinates
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ElementaryPlanes
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo

/-!
# The actual elementary sixteen-groups of the returning-core product

The proved H-type coordinates identify R with UT₃(F₄). Transporting its two
root planes constructs distinct elementary abelian subgroups A₁ and A₂ of
order sixteen in the original group. They generate R, intersect in E, and
exhaust its elementary subgroups of order sixteen. Neither lies in the
original extraspecial core. No model subgroup is substituted for an ambient
subgroup, and no assumption about the number of involution classes is used.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(1–2), pp.257–258.
This establishes the two planes inside R. The full Sylow-family assertion,
fusion control and the normalizers in 46.14(2–5) require further arguments.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory HyperbolicRecognition Matrix.PSL3Four
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D) (e : P.R ≃* RootNormalizerModel.Root)

def A₁ : Subgroup G := (transportedPlane₁ e).map P.R.subtype
def A₂ : Subgroup G := (transportedPlane₂ e).map P.R.subtype

instance A₁_elementary : IsElementaryAbelian 2 (P.A₁ e) :=
  IsElementaryAbelian.map P.R.subtype
instance A₂_elementary : IsElementaryAbelian 2 (P.A₂ e) :=
  IsElementaryAbelian.map P.R.subtype

theorem A₁_card : Nat.card (P.A₁ e) = 16 := by
  rw [A₁, card_map_of_injective P.R.subtype_injective, card_transportedPlane₁]
theorem A₂_card : Nat.card (P.A₂ e) = 16 := by
  rw [A₂, card_map_of_injective P.R.subtype_injective, card_transportedPlane₂]

theorem A₁_le_R : P.A₁ e ≤ P.R := map_subtype_le _
theorem A₂_le_R : P.A₂ e ≤ P.R := map_subtype_le _

theorem planes_inf : P.A₁ e ⊓ P.A₂ e = P.E := by
  rw [A₁, A₂, ← map_inf _ _ _ P.R.subtype_injective, transportedPlanes_inf,
    Geometry.E_center]

theorem planes_ne : P.A₁ e ≠ P.A₂ e :=
  fun h => transportedPlanes_ne e (map_injective P.R.subtype_injective h)

private theorem rootPlanes_sup : rootPlane₁ ⊔ rootPlane₂ = ⊤ := by
  apply top_unique
  intro q _
  let a : RootNormalizerModel.Root := ⟨q.x, 0, q.c - q.x * q.y⟩
  let b : RootNormalizerModel.Root := ⟨0, q.y, 0⟩
  have hq : a * b = q := by
    apply SylowModel.U.ext <;> dsimp [a, b, HMul.hMul, Mul.mul] <;> ring
  rw [← hq]
  exact (rootPlane₁ ⊔ rootPlane₂).mul_mem (mem_sup_left (by simp [a]))
    (mem_sup_right (by simp [b]))

theorem planes_sup : P.A₁ e ⊔ P.A₂ e = P.R := by
  rw [A₁, A₂, ← Subgroup.map_sup, transportedPlane₁, transportedPlane₂, ← Subgroup.map_sup,
    rootPlanes_sup, map_top_of_surjective _ e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- These are precisely the elementary subgroups of order sixteen in the actual R. -/
theorem elementary_sixteen_iff (A : Subgroup G) (hA : A ≤ P.R) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 16) ↔ A = P.A₁ e ∨ A = P.A₂ e := by
  constructor
  · rintro ⟨hE, hcard⟩
    let := hE
    have hsub : IsElementaryAbelian 2 (A.subgroupOf P.R) :=
      IsElementaryAbelian.subgroupOf hA
    have hc : Nat.card (A.subgroupOf P.R) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hcard
    rcases (transported_elementary_sixteen_iff e (A.subgroupOf P.R)).mp ⟨hsub,hc⟩ with h | h
    · left
      rw [← map_subgroupOf_eq_of_le hA, h]
      rfl
    · right
      rw [← map_subgroupOf_eq_of_le hA, h]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨inferInstance, P.A₁_card e⟩
    · exact ⟨inferInstance, P.A₂_card e⟩

private theorem not_le_core_of_elementary_sixteen (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16) (hE : P.E ≤ A) :
    ¬ A ≤ ambientCore D.z := by
  intro hle
  let Q := ambientCore D.z
  let : IsExtraspecial 2 Q := D.localType.ambientCore_isExtraspecial
  let : IsElementaryAbelian 2 (A.subgroupOf Q) := IsElementaryAbelian.subgroupOf hle
  have hc : Nat.card (A.subgroupOf Q) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hcard
  have hi : (A.subgroupOf Q).index = 2 := by
    have hh := (A.subgroupOf Q).card_mul_index
    rw [hc, D.localType.ambientCore_card] at hh
    omega
  have hZ : center Q ≤ A.subgroupOf Q := by
    intro q hq
    have hline : (q : G) ∈ zpowers D.z :=
      D.localType.core_center_image ▸ mem_map_of_mem Q.subtype hq
    exact hE ((zpowers_le.mpr P.z_mem_E) hline)
  exact IsExtraspecial.not_isMulCommutative_of_index_two
    (by rw [D.localType.ambientCore_card]; decide) (A.subgroupOf Q) hi hZ inferInstance

theorem A₁_not_le_core : ¬ P.A₁ e ≤ ambientCore D.z :=
  P.not_le_core_of_elementary_sixteen _ (P.A₁_card e) ((P.planes_inf e).symm ▸ inf_le_left)
theorem A₂_not_le_core : ¬ P.A₂ e ≤ ambientCore D.z :=
  P.not_le_core_of_elementary_sixteen _ (P.A₂_card e) ((P.planes_inf e).symm ▸ inf_le_right)

end ReturningPair

/-- Construction, not an extra source hypothesis: the actual two elementary
sixteen-groups inside the canonical returning-core product. -/
theorem exists_planes (D : Seed G) :
    ∃ (P : ReturningPair D) (A₁ A₂ : Subgroup G),
      IsElementaryAbelian 2 A₁ ∧ IsElementaryAbelian 2 A₂ ∧
      Nat.card A₁ = 16 ∧ Nat.card A₂ = 16 ∧ A₁ ≠ A₂ ∧
      A₁ ⊔ A₂ = P.R ∧ A₁ ⊓ A₂ = P.E ∧
      ¬ A₁ ≤ ambientCore D.z ∧ ¬ A₂ ≤ ambientCore D.z ∧
      ∀ A : Subgroup G, A ≤ P.R →
        ((IsElementaryAbelian 2 A ∧ Nat.card A = 16) ↔ A = A₁ ∨ A = A₂) := by
  obtain ⟨P⟩ := exists_returningPair D
  obtain ⟨e⟩ := Geometry.Coordinates.rootEquiv P
  exact ⟨P, P.A₁ e, P.A₂ e, inferInstance, inferInstance, P.A₁_card e, P.A₂_card e,
    P.planes_ne e, P.planes_sup e, P.planes_inf e, P.A₁_not_le_core e, P.A₂_not_le_core e,
    P.elementary_sixteen_iff e⟩
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
