module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Complement
public import CFSG.Quasithin.ChapterJ.Section04To05.CubicLift.SourceSelection

/-!
# The literal second source parabolic

For an actual Sylow three-subgroup X of G₂, form F₂=Q₅XA inside the original
ambient group. The preimage A is normal in F₂. The first isomorphism theorem
identifies the original quotient F₂/A with its literal image in G₂/A,
so the selected S₃ image supplies the required local quotient directly.

Source: Aschbacher–Smith, J.4.4(5) and J.4.5(4), printed pp.441–442.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The chosen Sylow three-subgroup, embedded in the original group. -/
def Plane.cubicSubgroup (X : Sylow 3 p.parabolic) : Subgroup G :=
  (X : Subgroup p.parabolic).map p.parabolic.subtype

/-- The second source parabolic Q₅XA, in the original group. -/
def Plane.F₂ (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) : Subgroup G :=
  (Q₅ d B5 ⊔ p.cubicSubgroup X) ⊔ p.A B5

theorem Plane.Q₅_le_parabolic (B5 : Sylow 5 d.toTypeRuSetup.H) : Q₅ d B5 ≤ p.parabolic :=
  (show Q₅ d B5 ≤ (d.T : Subgroup G) from (p.R₂_sup_Q₅ B5) ▸ le_sup_right).trans p.sylow_le_parabolic

theorem Plane.F₂_le_parabolic (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    p.F₂ B5 X ≤ p.parabolic :=
  sup_le (sup_le (p.Q₅_le_parabolic B5) (map_subtype_le _)) (p.A_le_parabolic B5)

theorem Plane.A_le_F₂ (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    p.A B5 ≤ p.F₂ B5 X := le_sup_right

theorem Plane.Q₅_le_F₂ (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    Q₅ d B5 ≤ p.F₂ B5 X := le_sup_left.trans le_sup_left

instance Plane.F₂_A_normal (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    ((p.A B5).subgroupOf (p.F₂ B5 X)).Normal :=
  normal_subgroupOf_of_le_normalizer ((p.F₂_le_parabolic B5 X).trans (p.A_normalized B5))

theorem Plane.F₂_subgroupOf (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    (p.F₂ B5 X).subgroupOf p.parabolic =
      ((Q₅ d B5).subgroupOf p.parabolic ⊔ (X : Subgroup p.parabolic)) ⊔
        (p.A B5).subgroupOf p.parabolic := by
  rw [Plane.F₂,Plane.cubicSubgroup,subgroupOf_sup (sup_le (p.Q₅_le_parabolic B5) (map_subtype_le _))
    (p.A_le_parabolic B5),subgroupOf_sup (p.Q₅_le_parabolic B5) (map_subtype_le _)]
  exact congrArg (fun B : Subgroup p.parabolic =>
    ((Q₅ d B5).subgroupOf p.parabolic ⊔ B) ⊔ (p.A B5).subgroupOf p.parabolic)
      (comap_map_eq_self_of_injective p.parabolic.subtype_injective _)

/-- The S₃ image of the actual selected Sylow gives the literal F₂/A quotient. -/
theorem Plane.F₂_quotient_of_image (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    [hn : ((p.A B5).subgroupOf p.parabolic).Normal]
    (h : Nonempty (((((Q₅ d B5).subgroupOf p.parabolic ⊔ (X : Subgroup p.parabolic)) ⊔
      (p.A B5).subgroupOf p.parabolic).map (QuotientGroup.mk' ((p.A B5).subgroupOf p.parabolic))) ≃*
        Equiv.Perm (Fin 3))) :
    Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) := by
  let q := QuotientGroup.mk' ((p.A B5).subgroupOf p.parabolic)
  let f := q.comp (inclusion (p.F₂_le_parabolic B5 X))
  have hk : f.ker = (p.A B5).subgroupOf (p.F₂ B5 X) := by
    ext x
    change q (inclusion (p.F₂_le_parabolic B5 X) x) = 1 ↔ (x:G) ∈ p.A B5
    exact QuotientGroup.eq_one_iff _
  have hr : f.range = (((Q₅ d B5).subgroupOf p.parabolic ⊔ (X : Subgroup p.parabolic)) ⊔
      (p.A B5).subgroupOf p.parabolic).map q := by
    rw [MonoidHom.range_comp,inclusion_range,p.F₂_subgroupOf]
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).trans ((MulEquiv.subgroupCongr hr).trans e))⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
