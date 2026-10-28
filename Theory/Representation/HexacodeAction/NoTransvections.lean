module
public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import Theory.Representation.BinaryOffender.SectionLinear
/-!
# No binary transvections in the full hexacode action

Even actors have even fixed codimension, since their fixed space is stable
under the cubic field scalar. An actor of binary fixed codimension one
fixes its displacement line, hence is an involution. An odd involution is a
field involution and has fixed codimension three. Both cases exclude rank
one, for the entire group rather than only its even cover.

Source: Aschbacher–Smith, B.4.5 and 13.8.21(2), printed pp.87 and 956.
The concrete action and field involution retain their existing ATLAS
attribution through HexacodeAction.ThompsonOffenders.
-/

public section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode
/-- No element of the full hexacode group acts as a binary transvection. -/
theorem no_transvections (g : HexAutomorphisms) :
    fixedCodim action (zpowers g) ≠ 1 := by
  intro hr
  have hg1 : g ≠ 1 := by
    intro h
    subst g
    have hz := (fixedCodim_eq_zero_iff action ⊥).mpr (fixedSpace_bot action)
    have hh : fixedCodim action (zpowers (1 : HexAutomorphisms)) = 0 := by simpa using hz
    omega
  by_cases he : hexSign g = 1
  · let a : HexEvenAutomorphisms := ⟨g,he⟩
    have hne : zpowers a ≠ ⊥ := by
      intro h
      have ha := mem_zpowers a
      rw [h] at ha
      exact hg1 (congrArg Subtype.val ha)
    have hh := ThompsonOffenders.fixedCodim_ge_two (zpowers a) hne
    have hcd : fixedCodim evenAction (zpowers a) = fixedCodim action (zpowers g) := by
      change fixedCodim (action.comp hexSign.ker.subtype) _ = _
      unfold fixedCodim
      rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
      rfl
    rw [hcd,hr] at hh
    omega
  · have ho : hexSign g = -1 := (Int.units_eq_one_or _).resolve_left he
    have hp : g ^ 2 = 1 := by
      apply action_injective
      apply LinearMap.ext
      intro v
      have hh := fixes_displacement_of_commute_rank_one action g g
        ((fixedCodim_zpowers_eq_displacement_rank action g).symm ▸ hr) (Commute.refl g) v
      have hneg (w : hexacode) : -w = w :=
        neg_eq_of_add_eq_zero_left (ZModModule.add_self w)
      rw [map_sub] at hh
      have ht := (sub_eq_iff_eq_add).mp hh
      simp only [sub_eq_add_neg,hneg,add_comm _ (action g v),←add_assoc,
        ZModModule.add_self,zero_add] at ht
      simpa only [pow_two,map_mul,Module.End.mul_apply,map_one,Module.End.one_apply] using ht
    have hh := ThompsonOffenders.odd_involution_fixedCodim g ho hp
    omega
end Representation.Hexacode
