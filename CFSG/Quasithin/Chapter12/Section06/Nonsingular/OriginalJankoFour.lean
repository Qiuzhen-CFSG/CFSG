module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleJankoFourCentralLine
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.Janko

/-!
# Excluding the original nonsingular J₄ component

The actual A₆ action and selected Sylow geometry put the nonidentity local
fixed involution in the full center of K_v. The literal map from K_v to its
marked J₄ central quotient is a finite perfect central cover. The native
two-primary multiplier calculation makes its kernel odd, contradicting that
involution. No replacement component, action, or covering kernel is used.

Source: Aschbacher--Smith 12.6.12, printed pp.825--826, and I.1.3,
printed p.407. The native multiplier proof retains its ATLAS local data.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The selected original nonsingular component cannot have central quotient J₄. -/
theorem SourceHypothesis.original_nonsingular_not_jankoFour
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) : False := by
  let := hK
  let C := Kv (v : G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hk : f.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let c : PerfectCentralCovering.Cover C Janko4.Model :=
    ⟨f, e.surjective.comp (QuotientGroup.mk'_surjective _), inferInstance, hk.le⟩
  have hodd := Janko4.TwoPrimary.kernel_not_two c
  change ¬ 2 ∣ Nat.card f.ker at hodd
  rw [hk] at hodd
  obtain ⟨z,hz,_,hzc⟩ := H.nonsingular_jankoFour_fixed_line_central D v hv hK hTV hi e
  have hz' : orderOf z = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hd := orderOf_dvd_natCard (⟨z,hzc⟩ : center C)
  rw [←Subgroup.orderOf_coe,hz'] at hd
  exact hodd hd

end CFSG.Quasithin.Chapter12.Section06
