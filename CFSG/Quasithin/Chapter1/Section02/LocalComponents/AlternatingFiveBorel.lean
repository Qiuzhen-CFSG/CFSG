module
public import Theory.Alternating.FiveSylowCubicBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# The ambient A₅ Sylow--cubic Borel

The full Sylow normalizer calculation is transported through the literal
subgroup inclusion. Any group preserving the block and its Sylow
intersection consequently preserves this Borel; it need not preserve the
chosen cubic supplement separately.

Source application: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
open Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- The actual Sylow--cubic join is the relative Sylow normalizer. -/
theorem a5_sylow_cubic_borel_eq_normalizer
    (L P D : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hP : Chapter1.IsSylowIn 2 P L) (hDL : D ≤ L) (hD : Nat.card D=3)
    (hDP : D ≤ normalizer (P : Set G)) :
    P ⊔ D=L ⊓ normalizer (P : Set G) := by
  obtain ⟨Q,hQ⟩ := hP
  have hPL : P ≤ L := hQ ▸ map_subtype_le (Q : Subgroup L)
  have hPsub : P.subgroupOf L=(Q : Subgroup L) := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hPL,hQ]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hDN : D.subgroupOf L ≤ normalizer (Q : Set L) := by
    change D.subgroupOf L ≤ normalizer ((Q : Subgroup L) : Set L)
    rw [←hPsub,←subgroupOf_normalizer_eq hPL]
    exact fun _ hx => hDP hx
  have hD' : Nat.card (D.subgroupOf L)=3 := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have he := Theory.AlternatingFive.sylow_normalizer_eq_sup_cubic_of_two_kernel q hq
    (hk.symm ▸ pCore_isPGroup) Q (D.subgroupOf L) hD' hDN
  have hm := congrArg (map L.subtype) he
  change (normalizer ((Q : Subgroup L) : Set L)).map L.subtype=
    ((Q : Subgroup L) ⊔ D.subgroupOf L).map L.subtype at hm
  rw [Subgroup.map_sup,hQ,map_subgroupOf_eq_of_le hDL,←hPsub,
    ←subgroupOf_normalizer_eq hPL,subgroupOf_map_subtype,inf_comm] at hm
  exact hm.symm

/-- Preserving the component and Sylow intersection preserves the whole Borel. -/
theorem a5_sylow_cubic_borel_normalized
    (L S D R : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hP : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (hDL : D ≤ L) (hD : Nat.card D=3)
    (hDS : D ≤ normalizer (S : Set G))
    (hRL : R ≤ normalizer (L : Set G)) (hRS : R ≤ normalizer (S : Set G)) :
    R ≤ normalizer (((S ⊓ L) ⊔ D : Subgroup G) : Set G) := by
  have hDP : D ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf hDS (hDL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  rw [a5_sylow_cubic_borel_eq_normalizer L (S ⊓ L) D e hP hDL hD hDP]
  have hRP : R ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf hRS hRL).trans inf_normalizer_le_normalizer_inf
  exact (le_inf hRL (hRP.trans (normalizer ((S ⊓ L : Subgroup G) : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf
end CFSG.Quasithin.Chapter1
