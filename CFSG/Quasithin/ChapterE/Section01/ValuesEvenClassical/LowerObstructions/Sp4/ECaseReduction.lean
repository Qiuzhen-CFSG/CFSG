module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection


/-!
# Reducing E-members to a two-core rank bound in the normal model

An E-member cannot have its elementary subgroup inside its two-core: the
odd-prime commutator clause or the nontrivial component clause would fail.
In the component case the radical is two-closed, so its intersection with
an elementary subgroup equals that subgroup's intersection with the two-core.
The quotient ranks in both source alternatives therefore give a bound on
the actual two-core quotient.

For a normal subgroup L, restriction from K to K ∩ L preserves this
quotient rank, since O₂(K ∩ L) = O₂(K) ∩ L. Thus an elementary subgroup
of L of order 2^(3f) cannot belong to E_(f-1), provided the concrete model
has the stated two-core rank gap. The model bound is an explicit remaining
premise, not a conclusion of this module. No outer-automorphism restriction
is used: the argument applies to the literal normal intersection.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2 and E.1.5, printed p.210; the symplectic application is E.1.14(1), p.214.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower
variable {G : Type*} [Group G] [Finite G]

private theorem rank_range_eq {D X Y : Type*} [Group D] [Finite D]
    [Group X] [Group Y] (f : D →* X) (g : D →* Y) (h : f.ker = g.ker) :
    Group.rank f.range = Group.rank g.range :=
  Group.rank_congr ((QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivRange g)))

private theorem two_closed_core {N P : Subgroup G} [N.Normal]
    (hN : IsTwoClosed N) (hP : IsPGroup 2 P) (hPN : P ≤ N) : P ≤ pCore 2 G := by
  obtain ⟨S, hS⟩ := hN
  let _ : (S : Subgroup N).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hle : P.subgroupOf N ≤ (S : Subgroup N) := by
    let _ := hS
    have hpg := hP.comap_of_injective N.subtype N.subtype_injective
    obtain ⟨U, hU⟩ := hpg.exists_le_sylow
    have hSU : S = U := by
      apply Sylow.ext
      exact (S.is_maximal' U.isPGroup' (S.isPGroup'.le_sylow_of_normal U)).symm
    simpa only [hSU, subgroupOf] using hU
  calc
    P = (P.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hPN).symm
    _ ≤ (S : Subgroup N).map N.subtype := map_mono hle
    _ ≤ pCore 2 G := le_sSup ⟨hsn, S.isPGroup'.map N.subtype⟩

private theorem core_le_radical (H : Type*) [Group H] [Finite H] :
    pCore 2 H ≤ solvableRadical H := by
  let _ := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

private theorem rank_core_eq_radical (A : Subgroup G)
    (hA : IsPGroup 2 A) (hR : IsTwoClosed (solvableRadical G)) :
    Group.rank (A.map (QuotientGroup.mk' (pCore 2 G))) =
      Group.rank (A.map (QuotientGroup.mk' (solvableRadical G))) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).comp A.subtype
  let g := (QuotientGroup.mk' (solvableRadical G)).comp A.subtype
  have hker : f.ker = g.ker := by
    ext x
    change (QuotientGroup.mk' (pCore 2 G)) x.val = 1 ↔
      (QuotientGroup.mk' (solvableRadical G)) x.val = 1
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mpr
        (core_le_radical G ((QuotientGroup.eq_one_iff _).mp hx))
    · intro hx
      apply (QuotientGroup.eq_one_iff _).mpr
      exact two_closed_core hR hA.to_inf_left inf_le_right
        ⟨x.property, (QuotientGroup.eq_one_iff _).mp hx⟩
  have hf : f.range = A.map (QuotientGroup.mk' (pCore 2 G)) := by
    change ((QuotientGroup.mk' (pCore 2 G)).comp A.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  have hg : g.range = A.map (QuotientGroup.mk' (solvableRadical G)) := by
    change ((QuotientGroup.mk' (solvableRadical G)).comp A.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  exact (Group.rank_congr (MulEquiv.subgroupCongr hf)).symm.trans
    ((rank_range_eq f g hker).trans (Group.rank_congr (MulEquiv.subgroupCongr hg)))

/-- Both source cases bound the rank modulo the intrinsic two-core. -/
theorem member_core_rank_le {i : ℕ} {T A K : Subgroup G}
    (h : IsEMemberAt i T A K) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ i := by
  let _ := h.1.1
  rcases h.2 with ho | hc
  · exact ho.2
  · have hp : IsPGroup 2 (A.subgroupOf K) :=
      (IsElementaryAbelian.isPGroup 2 A).comap_of_injective K.subtype K.subtype_injective
    exact (rank_core_eq_radical (A.subgroupOf K) hp hc.1.1).le.trans hc.2

/-- The source commutator clauses prevent the elementary subgroup from lying in O₂(K). -/
theorem member_not_le_core {T A K : Subgroup G} (h : IsEMember T A K) :
    ¬ A.subgroupOf K ≤ pCore 2 K := by
  intro hA
  have hz : (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊥ := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hA ha)
  rcases h.2.2.2.2.2 with ho | hc
  · obtain ⟨p, _, _, _, hne, hc, _⟩ := ho
    exact hne (hc.trans (by rw [hz, commutator_bot_right]))
  · have hzR : (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) = ⊥ := by
      apply bot_unique
      rintro x ⟨a, ha, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr (core_le_radical K (hA ha))
    obtain ⟨_, _, _, D, hD, _, hc | hn⟩ := hc
    · rw [hzR, commutator_bot_right] at hc
      have hs := hD.2.simple
      rw [hc] at hs
      let _ := hs
      exact not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton ((⊥ : Subgroup (K ⧸ solvableRadical K)) ⧸
          center (⊥ : Subgroup (K ⧸ solvableRadical K)))) hs.toNontrivial
    · exact hn.1 (hzR ▸ bot_le)

private theorem normal_core_rank (N : Subgroup G) [N.Normal] (A : Subgroup N) :
    Group.rank (A.map (QuotientGroup.mk' (pCore 2 N))) =
      Group.rank ((A.map N.subtype).map (QuotientGroup.mk' (pCore 2 G))) := by
  let f := (QuotientGroup.mk' (pCore 2 N)).comp A.subtype
  let g := (QuotientGroup.mk' (pCore 2 G)).comp (N.subtype.comp A.subtype)
  have he := (inferInstance : N.Normal).isSubnormal.pCore_subgroupOf 2
  have hk : f.ker = g.ker := by
    ext x
    change (QuotientGroup.mk' (pCore 2 N)) x.val = 1 ↔
      (QuotientGroup.mk' (pCore 2 G)) x.val.val = 1
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff _).mpr
      change x.val ∈ (pCore 2 G).subgroupOf N
      rw [he]
      exact (QuotientGroup.eq_one_iff x.val).mp hx
    · intro hx
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [← he]
      exact (QuotientGroup.eq_one_iff x.val.val).mp hx
  have hf : f.range = A.map (QuotientGroup.mk' (pCore 2 N)) := by
    change ((QuotientGroup.mk' (pCore 2 N)).comp A.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  have hg : g.range = (A.map N.subtype).map (QuotientGroup.mk' (pCore 2 G)) := by
    change ((QuotientGroup.mk' (pCore 2 G)).comp (N.subtype.comp A.subtype)).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  exact (Group.rank_congr (MulEquiv.subgroupCongr hf)).symm.trans
    ((rank_range_eq f g hk).trans (Group.rank_congr (MulEquiv.subgroupCongr hg)))

universe u v

/-- Conditional local reduction, with the intrinsic model rank bound still explicit. -/
theorem not_member_of_coreRankGap {G : Type u} [Group G] [Finite G]
    {X : Type v} [Group X] (L : Subgroup G) [L.Normal]
    (e : L ≃* X) {f : ℕ} (hf : 0 < f)
    (hgap : ∀ (H : Type u) [Group H] [Finite H] (j : H →* X),
      Function.Injective j → ∀ (A : Subgroup H), IsElementaryAbelian 2 A →
      Nat.card A = 2 ^ (3 * f) →
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f → A ≤ pCore 2 H)
    {T A K : Subgroup G} (hAL : A ≤ L) (hcard : Nat.card A = 2 ^ (3 * f)) :
    ¬ IsEMemberAt (f - 1) T A K := by
  intro h
  let N : Subgroup K := L.subgroupOf K
  let B : Subgroup N := (A.subgroupOf K).subgroupOf N
  have hAN : A.subgroupOf K ≤ N := fun x hx => hAL hx
  let j : N →* X := e.toMonoidHom.comp {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    have hv := congrArg Subtype.val (e.injective he)
    exact Subtype.ext (Subtype.ext hv)
  let _ := h.1.1
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf h.1.2.2.1
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  have hBc : Nat.card B = 2 ^ (3 * f) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe h.1.2.2.1).toEquiv, hcard]
  have hBm : B.map N.subtype = A.subgroupOf K := map_subgroupOf_eq_of_le hAN
  have hBr : Group.rank (B.map (QuotientGroup.mk' (pCore 2 N))) < f := by
    have hr := normal_core_rank N B
    have heq := Group.rank_congr (MulEquiv.subgroupCongr
      (congrArg (fun C : Subgroup K => C.map (QuotientGroup.mk' (pCore 2 K))) hBm))
    have hbnd := (hr.trans heq).le.trans (member_core_rank_le h)
    omega
  have hcore := hgap N j hj B hB hBc hBr
  apply member_not_le_core h.1
  rw [← hBm]
  exact (map_mono hcore).trans (map_le_iff_le_comap.mpr
    ((inferInstance : N.Normal).isSubnormal.pCore_subgroupOf 2).ge)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower
