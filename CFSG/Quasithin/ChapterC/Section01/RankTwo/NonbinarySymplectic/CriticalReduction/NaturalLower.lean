module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalIndex
public import Theory.Representation.ScalarCoinvariants
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.GroupTheory.SmallMoverFamily

/-!
# A field-sized movement bound on the full original natural layer

Every subgroup outside the original vertex kernel has nontrivial image in
the faithful symplectic action. Its positive field codimension multiplies
by the unchanged field degree on scalar restriction. Exact central-cover
indices give the same lower bound on the full U-layer, retaining its fixed
central attachment. No elementary or Sylow condition on the actor is needed.

Source application: Niles (1979), Lemmas 2.9 and 7.4, for the original F₀
in MS93 (5.1), printed p.913. RootProductNilesOffenders applies this bound
to its literal core omega and maximum abelian subgroups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h


/-- Every actor outside the original vertex kernel moves at least one field dimension
on the full original U-layer. -/
theorem Input.replacement_natural_fixed_index_lower
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical a)
    (hne : ¬ A ≤ Q d.radical a) :
    Nat.card F ≤ (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  let V := stabilizer d.radical a
  let A₀ := A.subgroupOf V
  let U₀ := (U d.radical a).subgroupOf V
  have hUS : U d.radical a ≤ V := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hAn : A₀.map f ≠ ⊥ := by
    intro he
    apply hne
    have hh := map_mono (f := V.subtype) ((map_eq_bot_iff A₀).mp he)
    rwa [map_subgroupOf_eq_of_le hA,hfQ] at hh
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hfaithful : Function.Injective τ := by
    intro x y he
    apply Subtype.ext
    apply Matrix.mulVec_injective
    exact funext (fun v => LinearMap.congr_fun he v)
  have hpos := fixedCodim_pos_of_faithful τ hfaithful hAn
  have he := fixedCodim_restrictScalars (symplecticNatural (k := E.Carrier) 2) (A₀.map f)
  have hd : Module.finrank (ZMod 2) E.Carrier = n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
    rw [Nat.card_zmod,E.card_eq,hE] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  rw [hd] at he
  have hlow : n ≤ fixedCodim τ (A₀.map f) := by
    change fixedCodim τ (A₀.map f) = _ at he
    rw [he] at hpos ⊢
    exact Nat.le_mul_of_pos_right n (Nat.pos_of_mul_pos_left hpos)
  have hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      2 ^ fixedCodim τ (A₀.map f) := by
    have hh := hidx A₀
    rw [←Subgroup.SmallMover.centralizer_index_map V.subtype V.subtype_injective,
      map_subgroupOf_eq_of_le hA,map_subgroupOf_eq_of_le hUS] at hh
    exact hh
  rw [hi,h.field_card]
  exact Nat.pow_le_pow_right (by decide) hlow

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
