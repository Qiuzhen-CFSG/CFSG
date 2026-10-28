module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Basic
public import Theory.SpecificGroups.SymplecticFour.TorusFixedUnipotent

/-!
# The full Cartan in a faithful symplectic extension completion

The inner image of the native Borel lies in the exact common subgroup.
Composing this inclusion with a faithful completion gives injective maps
from the entire native unipotent group and the two-parameter diagonal torus.
Their orders are q⁴ and (q−1)²; the latter normalizes the former and has
trivial common fixed subgroup when q > 2, including q = 4.

These facts hold for arbitrary extension degree. In particular, the torus
here is the native odd Cartan, not an asserted odd complement to an extended
Borel. No apartment, Weyl relation, smallness or recognition is assumed or
proved by these local calculations.

Source: Aschbacher–Smith F.4.3–4, F.4.10 and F.4.16, printed pp.274,279,282
of `refs/quasithin.pdf`. The actual normalizer-pair application is in
Chapter6/SourceReduction/RankOneModuleGenericGlobalSymplecticCompletion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]
namespace SourceExtension
variable (E : SourceExtension F)

/-- The native Borel embeds in the actual common subgroup, by conjugation. -/
def borelToMiddle : borel (F := F) →* E.middle :=
  ((MulAut.conj : Sp F →* MulAut (Sp F)).comp borel.subtype).codRestrict E.middle
    (fun b => (E.middle_inner.ge ⟨b.val,b.property,rfl⟩).1)

theorem borelToMiddle_injective : Function.Injective E.borelToMiddle := by
  intro a b he
  apply Subtype.ext
  apply inner_injective (F := F)
  exact congrArg Subtype.val he
end SourceExtension

abbrev Completion (E : SourceExtension F) (M : Type*) [Group M] :=
  RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M)

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

/-- The concrete native Borel, with the completion's original marking. -/
def borelMap : borel (F := F) →* M := c.middle.comp E.borelToMiddle

theorem borelMap_injective : Function.Injective c.borelMap :=
  c.middle_injective.comp E.borelToMiddle_injective

def unipotentMap : unipotent (F := F) →* M :=
  c.borelMap.comp (inclusion unipotent_le_borel)

def torusToBorel : (Fˣ × Fˣ) →* borel (F := F) :=
  CentralRootGeometry.diagonalTorusHom.codRestrict borel
    (fun a => diagonalTorus_mem_borel a.1 a.2)

/-- Both independent diagonal parameters, transported through the same Borel. -/
def torusMap : (Fˣ × Fˣ) →* M := c.borelMap.comp torusToBorel

theorem unipotentMap_injective : Function.Injective c.unipotentMap :=
  c.borelMap_injective.comp (inclusion_injective _)

theorem torusMap_injective : Function.Injective c.torusMap := by
  intro a b he
  have hh := c.borelMap_injective he
  apply Prod.ext
  · apply Units.ext
    exact congrArg (fun x : borel (F := F) => x.val.val (.inl 0) (.inl 0)) hh
  · apply Units.ext
    exact congrArg (fun x : borel (F := F) => x.val.val (.inl 1) (.inl 1)) hh

theorem card_unipotent_range [Finite F] : Nat.card c.unipotentMap.range = Nat.card F ^ 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective c.unipotentMap_injective).toEquiv,
    card_unipotent]

theorem card_torus_range [Finite F] : Nat.card c.torusMap.range = (Nat.card F - 1)^2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective c.torusMap_injective).toEquiv,
    Nat.card_prod,Nat.card_units,pow_two]

/-- The marked Cartan normalizes the entire marked unipotent subgroup. -/
theorem torus_normalizes_unipotent :
    c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set M) := by
  have he : c.unipotentMap.range = (unipotent.subgroupOf borel).map c.borelMap := by
    rw [unipotentMap,MonoidHom.range_comp,inclusion_range]
  have hh := (unipotent.subgroupOf borel).le_normalizer_map c.borelMap
  rw [normalizer_eq_top,← MonoidHom.range_eq_map,← he] at hh
  rintro x ⟨a,rfl⟩
  exact hh ⟨torusToBorel a,rfl⟩

/-- In every faithful completion of the extension, the whole marked unipotent
subgroup has trivial fixed subgroup under the marked rank-two Cartan. -/
theorem unipotent_inf_centralizer_torus [Finite F] (hF : 2 < Nat.card F) :
    c.unipotentMap.range ⊓ centralizer (c.torusMap.range : Set M) = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨u,rfl⟩,hx⟩
  have hc : u.val ∈ centralizer ((CentralRootGeometry.diagonalTorusHom (F := F)).range : Set (Sp F)) := by
    rintro t ⟨a,rfl⟩
    have hh := hx (c.torusMap a) ⟨a,rfl⟩
    have he : torusToBorel a * inclusion unipotent_le_borel u =
        inclusion unipotent_le_borel u * torusToBorel a := by
      apply c.borelMap_injective
      simpa only [map_mul, torusMap, unipotentMap, MonoidHom.comp_apply] using hh
    exact congrArg (fun b : borel (F := F) => b.val) he
  have hu : u.val = 1 := mem_bot.mp
    ((CentralRootGeometry.unipotent_torus_fixed_eq_bot hF).le ⟨u.property,hc⟩)
  have hu' : u = 1 := Subtype.ext hu
  exact mem_bot.mpr (by rw [hu',map_one])
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
