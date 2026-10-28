module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Geometry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Marking

/-!
# The original terminal three-space and escaping quaternion

The original Sylow-invariant flag makes the point stabilizer normalize the
actual order-eight subgroup. Transporting the flag through the faithful
component marking places its image in the ambient point-core commutator.
The native quaternion centralizes that commutator; its intersection with
the original module normalizer has order at most four. Its order eight
therefore proves centralizer escape for this original marking.

The ambient contradiction and the unchanged terminal-witness application
are assembled in `OriginalOddNormalizer.TerminalRudvalis`.
Source: Aschbacher--Smith 4.4.3 case (c), p.623, referring to the
Rudvalis calculation in the proof of 4.2.13, pp.611--612.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Transport the original invariant flag through the actual component marking. -/
theorem unitary_terminal_native_original_three (s : Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let Zbar := (Z.subgroupOf J).map j.toMonoidHom
    let Ubar := (U.subgroupOf J).map j.toMonoidHom
    ∀ z ∈ Zbar, z ≠ 1 →
      Ubar ≤ ⁅(centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2,
        (centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2⁆ := by
  let E := (V.subgroupOf J).map j.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  let Zbar := (Z.subgroupOf J).map j.toMonoidHom
  let Ubar := (U.subgroupOf J).map j.toMonoidHom
  have hZE : Zbar ≤ E := map_mono (subgroupOf_mono J hZV)
  have hUE : Ubar ≤ E := map_mono (subgroupOf_mono J hUV)
  have hZcard : Nat.card Zbar = 2 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hZV.trans hV)).toEquiv,hZ]
  have hUcard : Nat.card Ubar = 8 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hUV.trans hV)).toEquiv,hU]
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  obtain ⟨rho,coords,he,_,_,hz,_,hu⟩ := exists_unitary_flag_marking T L Z B U
    s.chosen.normalizes hNL s.actor s.coordinates s.equivariant hTN
    hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hNU : normalizer (V : Set G) ⊓ centralizer (Z : Set G) ≤ normalizer (U : Set G) :=
    point_centralizer_normalizes_marked_seed U Z _ rho coords he hu hz hUV inf_le_left inf_le_right
  dsimp only
  intro z hzbar hzne
  have hZcyclic : Zbar ≤ zpowers z := by
    intro w hw
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hZcard
      (show (⟨z,hzbar⟩ : Zbar) ≠ 1 from fun h => hzne (congrArg Subtype.val h))
      (g' := ⟨w,hw⟩))
    exact mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩
  apply unitary_terminal_native_invariant_three s A hAN hcomm hodd hAV J j hV hR
    ⟨z,hZE hzbar⟩ (fun h => hzne (congrArg Subtype.val h)) Ubar hUE hUcard
  intro x hx
  have hxC : x ∈ ((normalizer (V : Set G)).subgroupOf J).map j.toMonoidHom := by
    have hh := hx.1
    change x ∈ normalizer ((V.subgroupOf J).map j.toMonoidHom : Set Rudvalis.Model) at hh
    rwa [←map_normalizer_eq_of_bijective _ j.bijective,←subgroupOf_normalizer_eq hV] at hh
  obtain ⟨y,hy,rfl⟩ := hxC
  have hyZ : (y : G) ∈ centralizer (Z : Set G) := by
    intro w hw
    let wJ : J := ⟨w,(hZV.trans hV) hw⟩
    have hxc : j y ∈ centralizer (zpowers z : Set Rudvalis.Model) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.2
    have hh := hxc (j wJ) (hZcyclic (mem_map_of_mem j.toMonoidHom hw))
    have hh' : wJ*y = y*wJ := j.injective (by simpa only [map_mul] using hh)
    exact congrArg J.subtype hh'
  have hyn : y ∈ normalizer (U.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (hUV.trans hV)]
    exact hNU ⟨hy,hyZ⟩
  exact (U.subgroupOf J).le_normalizer_map j.toMonoidHom (mem_map_of_mem j.toMonoidHom hyn)

/-- The native quaternion centralizes this original three-space and escapes
its full module normalizer. -/
theorem unitary_terminal_native_three_escape (s : Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    let Ubar := (U.subgroupOf J).map j.toMonoidHom
    ¬ centralizer (Ubar : Set Rudvalis.Model) ≤ normalizer (E : Set Rudvalis.Model) := by
  let E := (V.subgroupOf J).map j.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  let Zbar := (Z.subgroupOf J).map j.toMonoidHom
  let Ubar := (U.subgroupOf J).map j.toMonoidHom
  have hZcard : Nat.card Zbar = 2 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hZV.trans hV)).toEquiv,hZ]
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
    (Zbar.one_lt_card_iff_ne_bot.mp (by omega))
  have hZE : Zbar ≤ E := map_mono (subgroupOf_mono J hZV)
  let zE : E := ⟨z,hZE z.property⟩
  have hzE : zE ≠ 1 := fun h => hz (Subtype.ext (congrArg (fun v : E => (v : Rudvalis.Model)) h))
  obtain ⟨X,hXC,hbound⟩ := unitary_terminal_native_cubic_sylow
    s A hAN hcomm hodd hAV J j hV hR zE hzE
  obtain ⟨hel,hE,hRcard,hcore,hEB,hBE,ht,_⟩ :=
    unitary_terminal_native_centralizer s A hAN hcomm hodd hAV J j hV hR
  let : IsElementaryAbelian 2 E := hel
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
    (Rudvalis.transitive_sixtyFour_involution_class
      (((oddActorResidual L A).subgroupOf J).map j.toMonoidHom) E hBE hE
      (by rw [hRcard]; exact dvd_mul_left _ _) ht zE hzE).1
  obtain ⟨Q,⟨q⟩,hQcore,hQX,hQderived⟩ :=
    Rudvalis.PointQuaternion.exists_quaternion_sylow_derived z hclass X
  have hUderived := unitary_terminal_native_original_three s Z B U hZV hBV hUV
    hTZ hTB hTU hZ hB hU A hAN hcomm hodd hAV J j hV hR z z.property
      (fun h => hz (Subtype.ext h))
  have hQcard : Nat.card Q = 8 := (Nat.card_congr q.toEquiv).trans
    (by rw [Nat.card_eq_fintype_card,QuaternionGroup.card])
  have hQC : Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 :=
    (card_le_of_le (inf_le_inf (le_inf hQcore hQX) le_rfl)).trans hbound
  change ¬ centralizer (Ubar : Set Rudvalis.Model) ≤ C
  intro hC
  have hQ : Q ≤ C := (hQderived.trans (centralizer_le hUderived)).trans hC
  rw [inf_eq_left.mpr hQ,hQcard] at hQC
  omega

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
