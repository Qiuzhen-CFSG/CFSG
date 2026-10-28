module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCoreRecovery
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer

/-!
# The original normalizer is KT in the Held branch

The full automizer embeds in the actual hexacode automorphism group and
the original K image is its even subgroup. Thus the faithful action gives
[N_G(K):K] dividing two once C_G(U)=U≤K. The original Sylow subgroup is
already contained in KT, so its odd index forces N_G(K)=KT.

Source: Aschbacher--Smith12.7.6(2), printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original maximal two-local is the literal Sylow join KT. -/
theorem original_tripleSix_held_normalizer_eq_join
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    normalizer (K : Set G) = K ⊔ (T : Subgroup G) := by
  obtain ⟨_,_,_,hN,hC⟩ := original_tripleSix_held_core_recovery
    h structural D a t ht heven hB hcenter e
  obtain ⟨f,hf,_,himage,_⟩ := original_tripleSix_full_automizer h structural D a
  let A := inducedAutomizer U K
  have htwo : hexSign.ker.index = 2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
    simp [Nat.card_eq_fintype_card]
  have ha : A.index ∣ 2 := by
    have hh := A.index_map_of_injective hf
    rw [himage,htwo] at hh
    exact ⟨f.range.index,hh⟩
  let M := normalizer (K : Set G)
  let N := normalizer (U : Set G)
  let H := K ⊔ (T : Subgroup G)
  have hk : U.normalizerMonoidHom.rangeRestrict.ker ≤ K.subgroupOf N := by
    rw [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker]
    exact subgroupOf_mono N (hC.le.trans D.le_component)
  have hi : A.index = K.relIndex M := by
    rw [show A = (K.subgroupOf N).map U.normalizerMonoidHom.rangeRestrict from rfl,
      (K.subgroupOf N).index_map_eq
        U.normalizerMonoidHom.rangeRestrict_surjective hk]
    change K.relIndex N = K.relIndex M
    rw [show N=M from hN]
  have hHM : H ≤ M := sup_le K.le_normalizer D.sylow_normalizes_component
  have hd : H.relIndex M ∣ 2 :=
    (relIndex_dvd_of_le_left M (show K ≤ H from le_sup_left)).trans (hi ▸ ha)
  have hn : ¬ 2 ∣ H.relIndex M := by
    intro hh
    exact T.not_dvd_index (hh.trans ((relIndex_dvd_index_of_le hHM).trans
      (index_dvd_of_le (show (T : Subgroup G) ≤ H from le_sup_right))))
  have he : H.relIndex M = 1 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right
    (fun he => hn (he ▸ dvd_rfl))
  exact le_antisymm (relIndex_eq_one.mp he) hHM

end CFSG.Quasithin.Chapter12.Section07
