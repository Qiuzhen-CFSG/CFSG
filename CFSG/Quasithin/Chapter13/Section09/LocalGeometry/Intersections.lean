module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.ElementaryGeometry
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry.Intersections

/-!
# Intersection geometry in the original wreath Sylow

The four maximal elementary subgroups of the marked Sylow retain their
intersection orders and their explicit indexing. This identifies the actual
maximum family with the four vertices used in the normalizer action.

Source: Aschbacher–Smith 13.9.2(1–2), printed p.969 (PDF p.986).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem card_elementary_inf (a b c e : Bool) :
    Nat.card (m.elementaryGroup a b ⊓ m.elementaryGroup c e : Subgroup G) =
      (if a=c then 4 else 2)*(if b=e then 4 else 2) := by
  change Nat.card ((SymmetricFourWreath.elementary a b).map m.embedding ⊓
    (SymmetricFourWreath.elementary c e).map m.embedding : Subgroup G) = _
  rw [←map_inf _ _ m.embedding m.embedding_injective,card_map_of_injective m.embedding_injective]
  exact SymmetricFourWreath.card_elementary_inf a b c e

theorem elementary_injective : Function.Injective (fun p : Bool×Bool=>m.elementaryGroup p.1 p.2) := by
  intro p q he
  apply SymmetricFourWreath.elementary_injective
  exact (map_injective m.embedding_injective) he

@[expose] noncomputable def maximumElementaryEquiv : (Bool×Bool) ≃
    {E : Subgroup G // E∈Stellmacher.elementaryAbelianMaxSubgroups (d.T : Subgroup G)} :=
  Equiv.ofBijective (fun p=>⟨m.elementaryGroup p.1 p.2,(m.maximum_elementary _).mpr ⟨p.1,p.2,rfl⟩⟩)
    ⟨fun _ _ h=>m.elementary_injective (congrArg Subtype.val h),by
      rintro ⟨E,hE⟩
      obtain ⟨b,c,hbc⟩ := (m.maximum_elementary E).mp hE
      exact ⟨(b,c),Subtype.ext hbc.symm⟩⟩

theorem maximumElementaryEquiv_apply (p : Bool×Bool) :
    (m.maximumElementaryEquiv p).val = m.elementaryGroup p.1 p.2 := rfl

include m in
theorem card_maximum_elementary :
    Nat.card {E : Subgroup G // E∈Stellmacher.elementaryAbelianMaxSubgroups (d.T : Subgroup G)} = 4 := by
  rw [←Nat.card_congr m.maximumElementaryEquiv]
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card]

end CFSG.Quasithin.Chapter13.Section09.Marking
