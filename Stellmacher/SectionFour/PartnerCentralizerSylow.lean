module

public import Stellmacher.SectionFour.BaumannPartner
public import Stellmacher.SectionThree.NormalClosureCentralizerSylow
public import Theory.GroupTheory.PGroup.NormalCoreSylow

/-!
# Sylow control in critical-partner centralizers

For a critical pair `(P,Pstar)` with `P ≤ C` and solvable `Pstar`, let
`V` be the normal closure of `Ω₁(Z(S))` inside `Pstar`. In every normal
subgroup `N` of `Pstar`, the core `O₂(N)` is Sylow in `C_N(V)`.
The application in Stellmacher (4.6) takes `N = ⟨B₀^{Pstar}⟩`.

The Baumann partner theorem excludes `Pstar ≤ C`, since `C` normalizes
`B₀`. The Section Three centralizer theorem gives `O₂(Pstar)` Sylow in
`C_Pstar(V)`. We transport this ambient-image statement through the
subgroup-image equivalence and apply normal-core Sylow restriction.

Source: `refs/latex/stellmacher-n-group.tex`, second paragraph of (4.6).
-/

namespace Stellmacher.SectionFour

/-- In a normal subgroup of the critical partner, the core is Sylow in
the centralizer of the normal closure of the fixed Sylow's central involutions. -/
public theorem partner_normal_centralizer_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hsolv : Group.IsSolvable Pstar)
    (N : Subgroup Pstar) [N.Normal] :
    let V : Subgroup Pstar := Subgroup.normalClosure
      ((zSubgroup S).subgroupOf Pstar : Set Pstar)
    ∃ T : Sylow 2 ((Subgroup.centralizer (V : Set Pstar)).subgroupOf N),
      (T : Subgroup ((Subgroup.centralizer (V : Set Pstar)).subgroupOf N)).map
        ((Subgroup.centralizer (V : Set Pstar)).subgroupOf N).subtype = pCore 2 N := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Subgroup Pstar := Subgroup.normalClosure
    ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let C0 : Subgroup Pstar := Subgroup.centralizer (V : Set Pstar)
  have hcent : zSubgroup S ≤ (Subgroup.center S).map (S : Subgroup G).subtype := by
    unfold zSubgroup omegaOneCenterAmbient
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hZS : zSubgroup S ≤ (S : Subgroup G) :=
    hcent.trans (Subgroup.map_subtype_le _)
  have hSZ : (S : Subgroup G) ≤ Subgroup.centralizer (zSubgroup S : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zS, hzS, rfl⟩ := hcent hz
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzS) ⟨s, hs⟩).symm
  have hCN : cSubgroup S ≤ Subgroup.normalizer (twoCoreAmbient (cSubgroup S) : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hnot : ¬ Pstar ≤ Subgroup.centralizer (zSubgroup S : Set G) := by
    intro hle
    exact baumann_not_normalized_by_partner S heven P Pstar hpair hPC
      (hle.trans (hCN.trans (normalizer_le_normalizer_baumann _)))
  have hSyl := SectionThree.twoCore_sylow_normalClosure_centralizer
    (S : Subgroup G) ⟨heven, S.ne_bot_of_dvd_card heven.two_dvd, S.isPGroup'⟩
    Pstar (zSubgroup S) hpair.2.1 hsolv hZS hSZ hnot
  obtain ⟨T, hT⟩ := hSyl
  let D : Subgroup G := C0.map Pstar.subtype
  let e : C0 ≃* D := C0.equivMapOfInjective Pstar.subtype Pstar.subtype_injective
  let U : Sylow 2 C0 := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hU : (U : Subgroup C0).map C0.subtype = pCore 2 Pstar := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_map]
    change ((T : Subgroup D).map e.symm.toMonoidHom).map
      (Pstar.subtype.comp C0.subtype) = (pCore 2 Pstar).map Pstar.subtype
    rw [Subgroup.map_map]
    have he : (Pstar.subtype.comp C0.subtype).comp e.symm.toMonoidHom = D.subtype := by
      ext x
      have heq := congrArg (fun y : D ↦ (y : G)) (e.apply_symm_apply x)
      exact heq
    rw [he]
    exact hT
  exact pCore_sylow_restrict_normal 2 N C0 ⟨U, hU⟩

end Stellmacher.SectionFour
