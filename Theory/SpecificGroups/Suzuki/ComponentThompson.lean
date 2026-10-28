module
public import Theory.GroupTheory.GeneralizedFitting.ThompsonNormalizerLayer
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupAction.InnerSylowNormalizer
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Thompson normalization of a Suzuki Borel along a component orbit

In the component normalizer, odd outer order makes the Sylow action inner.
The Suzuki Sylow center is elementary of order at least eight and centralizes
that action. A maximum elementary subgroup cannot move the component:
elementary replacement would bound the same fixed index both below by eight
and above by two. Thus J(S) lies in the component normalizer. Thompson
heredity and the inner-action normalizer calculation finish the proof.

This treats an actual simple Suzuki component, even when S permutes its
conjugates. Central covers require the separate quotient transport; they
are not identified with the simple model here.
Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {m : ℕ}

/-- The literal Borel normalizes J(S) for a Suzuki component orbit of size at most two. -/
theorem suzuki_component_borel_normalizes_thompson
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hS : IsPGroup 2 S)
    (hi : (normalizer (L : Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    (normalizer (P : Set L)).map L.subtype ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let Q := S ⊓ normalizer (L : Set G)
  have hQ : IsPGroup 2 Q := hS.to_le inf_le_left
  have hQL : Q ≤ normalizer (L : Set G) := inf_le_right
  have hPQ : (P : Subgroup L).map L.subtype ≤ Q :=
    le_inf hPS ((map_subtype_le _).trans L.le_normalizer)
  have hinner (s : Q) : ∃ l : L,
      L.normalizerMonoidHom ⟨s,hQL s.property⟩ = MulAut.conj l := by
    let f : Q →* MulAut (SuzukiMatrixGroup m) := (MulAut.congr e).toMonoidHom.comp
      (L.normalizerMonoidHom.comp (inclusion hQL))
    obtain ⟨k,hk⟩ := hQ s
    have hp : f s ^ (2 ^ k) = 1 := by rw [← map_pow,hk,map_one]
    exact (MulAut.congr_inner_iff e _).mp
      (MulAut.inner_of_two_pow_eq_one_of_odd_index
        (suzuki_odd_outer_index m (by omega)) (f s) hp)
  let E := (omegaOneAmbient (P : Subgroup L)).map L.subtype
  let : IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup L)) :=
    suzukiSylow_omega_elementary hm e P
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map L.subtype
  have hEL : E ≤ L := map_subtype_le _
  have hES : E ≤ S := (map_mono (omegaOneAmbient_le _)).trans hPS
  have hEC : E ≤ centralizer (Q : Set G) := by
    dsimp only [E]
    rw [suzukiSylow_omega_eq_center hm e P]
    exact sylowCenter_le_centralizer_of_inner_action L Q hQ hQL P hPQ hinner
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup L := e.isSimpleGroup
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (hG := hL.2) (subgroupOfEquivOfLe hLH)
  have hz : center L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hh))
  have hd : Disjoint E (centralizer (L : Set G)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz' : (⟨x,hEL hx.1⟩ : L) ∈ center L :=
      mem_center_iff.mpr (fun l => Subtype.ext (hx.2 l l.property))
    have he : (⟨x,hEL hx.1⟩ : L) = 1 := mem_bot.mp (hz ▸ hz')
    exact mem_bot.mpr (congrArg (fun y : L => (y : G)) he)
  have hcard : 2 < Nat.card E := by
    dsimp only [E]
    rw [card_map_of_injective L.subtype_injective, suzukiSylow_omega_card hm e P]
    exact (by decide : 2 < 2 ^ 3).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hJN := IsComponent.maxJ_le_relative_normalizer_of_central_elementary
    H L S E hLH hSH hL hi hEL hES hEC hd hcard
  have hJ : elementaryAbelianMaxJ Q = elementaryAbelianMaxJ S :=
    elementaryAbelianMaxJ_eq_of_intermediate S Q
      (le_inf (sSup_le fun _ hA => hA.1) hJN) inf_le_left
  rw [← hJ]
  exact (sylowNormalizer_le_normalizer_of_inner_action L Q hQ hQL P hPQ hinner).trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ Q)

end BenderSuzuki.MatrixGroups
