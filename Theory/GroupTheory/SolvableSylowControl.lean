module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable overgroups of a marked Sylow subgroup

Suppose solvable Sylow overgroups in a finite group normalize that Sylow.
In an ambient group, a solvable subgroup normalizing a copy of this group
and containing its marked Sylow also normalizes the marked Sylow. Indeed,
the intersection with the copy has that Sylow as its characteristic p-core.
This formulation needs only relative normality and is invariant under actual
group equivalences.

Source: the elementary normalizer argument used in Aschbacher–Smith,
proof of 13.6.6, printed p.927, and proof of 13.8.20, printed p.954.
The intrinsic model assertion is an explicit premise, not proved here.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory

/-- An intrinsic property of a group, with the supplied Sylow retained. -/
def SolvableSylowControl (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (S : Sylow p G) (A : Subgroup G), Group.IsSolvable A →
    (S : Subgroup G) ≤ A → A ≤ normalizer (S : Set G)

namespace SolvableSylowControl
variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- Transport the intrinsic property along a genuine model equivalence. -/
theorem of_equiv [Finite G] [Fact p.Prime] (e : G ≃* H) (h : SolvableSylowControl p H) :
    SolvableSylowControl p G := by
  intro S A hA hSA
  let : Group.IsSolvable A := hA
  have hs : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hn := h (S.mapSurjective e.surjective) (A.map e.toMonoidHom) hs (map_mono hSA)
  change A.map e.toMonoidHom ≤ normalizer ((S : Subgroup G).map e.toMonoidHom : Set H) at hn
  rw [← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

/-- The marked Sylow is the p-core of the intersection with a solvable
overgroup. No normality in the whole ambient group is required. -/
theorem core_intersection (K A : Subgroup G) (h : SolvableSylowControl p K)
    [Group.IsSolvable A] (S : Sylow p K)
    (hSA : (S : Subgroup K).map K.subtype ≤ A) :
    (A ⊓ K).pCoreIn p = (S : Subgroup K).map K.subtype := by
  let C := A ⊓ K
  let U := (S : Subgroup K).map K.subtype
  have hUC : U ≤ C := le_inf hSA (map_subtype_le _)
  let N := A.subgroupOf K
  let i : N →* A := {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : A => x.val) hab))
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hi
  have hSN : (S : Subgroup K) ≤ N := fun x hx => hSA ⟨x, hx, rfl⟩
  have hNS := h S N inferInstance hSN
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc u hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨(⟨c, hc.2⟩ : K) * x * (⟨c, hc.2⟩ : K)⁻¹,
      le_normalizer_iff.mp hNS ⟨c, hc.2⟩ hc.1 x hx, rfl⟩
  have hUQ : U ≤ C.pCoreIn p := le_pCoreIn_of_normalizes
    (S.isPGroup'.map K.subtype) hUC hCU
  have hQK : C.pCoreIn p ≤ K := (pCoreIn_le p C).trans inf_le_right
  have hp : IsPGroup p ((C.pCoreIn p).subgroupOf K) :=
    (isPGroup_pCoreIn p C).comap_subtype
  have hle : (S : Subgroup K) ≤ (C.pCoreIn p).subgroupOf K :=
    fun x hx => hUQ ⟨x, hx, rfl⟩
  have he := S.is_maximal' hp hle
  have hm := congrArg (fun P => P.map K.subtype) he
  rwa [map_subgroupOf_eq_of_le hQK] at hm

/-- Relative normalization and intrinsic control imply normalization of
the actual marked Sylow in the ambient group. -/
theorem normalizes_sylow (K A : Subgroup G) (h : SolvableSylowControl p K)
    [Group.IsSolvable A] (S : Sylow p K)
    (hAK : A ≤ normalizer (K : Set G))
    (hSA : (S : Subgroup K).map K.subtype ≤ A) :
    A ≤ normalizer ((S : Subgroup K).map K.subtype : Set G) := by
  rw [← core_intersection K A h S hSA]
  exact ((le_inf A.le_normalizer hAK).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (A ⊓ K) (pCore p (A ⊓ K : Subgroup G)))

/-- A compatible marking carries a relative normalizer to the concrete
normalizer of the marked subgroup. This includes nonsplit overgroups. -/
theorem relative_normalizer_map (J U : Subgroup G) (hUJ : U ≤ J)
    (e : J ≃* H) (U₀ B₀ : Subgroup H)
    (hU : (U.subgroupOf J).map e.toMonoidHom = U₀)
    (hB : normalizer (U₀ : Set H) = B₀) :
    ((J ⊓ normalizer (U : Set G)).subgroupOf J).map e.toMonoidHom = B₀ := by
  have he : (J ⊓ normalizer (U : Set G)).subgroupOf J =
      normalizer (U.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hUJ]
    ext x
    exact and_iff_right x.property
  rw [he, map_equiv_normalizer_eq, hU, hB]

end SolvableSylowControl
end Theory.GroupTheory
