module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.FullCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.PlaneGeometry

/-!
# The genuine parabolic of the marked V₂-plane

A marked plane lies in an equivariantly embedded natural constituent of the
actual whole center. The constituent may be any natural copy in the doubled
module. Conjugation compatibility identifies its relative normalizer in L
with the full geometric plane stabilizer under the actual quotient map.
This proves the parabolic image, rather than assuming any matrix membership.

Source: Aschbacher--Smith, proof of 15.3.31, printed p.1132, first paragraph.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
open LinearThree LinearModels
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable {L : Subgroup G} {ρ : Representation (ZMod 2) SL V}

/-- A plane in an actual natural constituent of the whole center. -/
structure MarkedPlane (c : FullCenter L ρ) (E : Subgroup G) where
  space : Submodule (ZMod 2) Space
  dimension : Module.finrank (ZMod 2) space = 2
  embedding : Space →ₗ[ZMod 2] V
  injective : Function.Injective embedding
  equivariant : ∀ a v, embedding (natural a v) = ρ a (embedding v)
  contained : E ≤ coreCenter L
  membership : ∀ z : coreCenter L,
    (z : G) ∈ E ↔ ∃ v ∈ space, c.equiv z = Multiplicative.ofAdd (embedding v)

namespace MarkedPlane
variable {c : FullCenter L ρ} {E : Subgroup G} (m : MarkedPlane c E)

def lift (v : Space) : coreCenter L := c.equiv.symm (Multiplicative.ofAdd (m.embedding v))

theorem lift_mem (v : Space) : (m.lift v : G) ∈ E ↔ v ∈ m.space := by
  rw [m.membership]
  change (∃ w ∈ m.space, c.equiv (c.equiv.symm _) = _) ↔ _
  rw [MulEquiv.apply_symm_apply]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (m.injective (congrArg Multiplicative.toAdd he)).symm ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem conjugate_lift (l : L) (v : Space) :
    centerConjugate L l (m.lift v) = m.lift (natural (c.actor l) v) := by
  apply c.equiv.injective
  rw [c.action]
  change Multiplicative.ofAdd (ρ (c.actor l)
    (c.equiv (c.equiv.symm (Multiplicative.ofAdd (m.embedding v)))).toAdd) =
    c.equiv (c.equiv.symm (Multiplicative.ofAdd (m.embedding (natural (c.actor l) v))))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, m.equivariant]
  rfl

theorem normalizer_iff (l : L) :
    (l : G) ∈ normalizer (E : Set G) ↔ c.actor l ∈ PlaneGeometry.stabilizer m.space := by
  constructor
  · intro hl v
    change natural (c.actor l) v ∈ m.space ↔ v ∈ m.space
    rw [← m.lift_mem, ← m.lift_mem, ← m.conjugate_lift]
    exact ((mem_normalizer_iff.mp hl) (m.lift v)).symm
  · intro hl
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      let zC : coreCenter L := ⟨z,m.contained hz⟩
      obtain ⟨v,hv,he⟩ := (m.membership zC).mp hz
      have heq : zC = m.lift v := by
        apply c.equiv.injective
        exact he.trans (c.equiv.apply_symm_apply _).symm
      have hh := (m.lift_mem (natural (c.actor l) v)).mpr ((hl v).mpr hv)
      rw [← m.conjugate_lift, ← heq] at hh
      exact hh
    · intro hz
      have hzC : z ∈ coreCenter L :=
        ((mem_normalizer_iff.mp (normalizes_coreCenter L l.property)) z).mpr (m.contained hz)
      let zC : coreCenter L := ⟨z,hzC⟩
      obtain ⟨v,hv,he⟩ := (m.membership (centerConjugate L l zC)).mp hz
      have hzcoord : c.equiv zC =
          Multiplicative.ofAdd (m.embedding (natural (c.actor l)⁻¹ v)) := by
        have he' := congrArg (fun x : Multiplicative V => ρ (c.actor l)⁻¹ x.toAdd) he
        rw [c.action] at he'
        change ρ (c.actor l)⁻¹ (ρ (c.actor l) (c.equiv zC).toAdd) =
          ρ (c.actor l)⁻¹ (m.embedding v) at he'
        rw [inv_self_apply, ← m.equivariant] at he'
        exact congrArg Multiplicative.ofAdd he'
      apply (m.membership zC).mpr
      refine ⟨natural (c.actor l)⁻¹ v, ?_, hzcoord⟩
      apply (hl (natural (c.actor l)⁻¹ v)).mp
      change natural (c.actor l) (natural (c.actor l)⁻¹ v) ∈ m.space
      rwa [self_inv_apply]

theorem parabolic_image :
    ((normalizer (E : Set G)).subgroupOf L).map c.actor = PlaneGeometry.stabilizer m.space := by
  ext a
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact (m.normalizer_iff l).mp hl
  · intro ha
    obtain ⟨l,rfl⟩ := c.actor_surjective a
    exact mem_map.mpr ⟨l,(m.normalizer_iff l).mpr ha,rfl⟩

end MarkedPlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
