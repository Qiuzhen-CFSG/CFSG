module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFiveUniqueness.Linear
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFiveUniqueness.SourcePlane
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates

/-!
# The original parabolic five-subgroup uniqueness claim

Suppose the original B₅ centralizes A₁ in a genuine first endpoint E, and
B₅ with A₂ generates a five-group. If B₅ also centralizes A₂, both lie in
the original five-core. Otherwise the constructed plane B₅Z(S) is normalized
by A₁,A₂ and self-centralizing. Its literal conjugation action has five-group
kernel, so the endpoint order excludes distinct images generating SL₂(5).
In either case A₁,A₂ generate a five-group in E; E has five-part only five,
forcing their equality. No marked plane or action conclusion is a premise.
Source: the uniqueness claim in J.4.10, printed p.444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFiveUniqueness
open Subgroup Centralizers Centralizers.Choices
open scoped MatrixGroups
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem equality_of_five_join (A B:Subgroup G)
    (hA:Nat.card A=5) (hB:Nat.card B=5)
    (hp:IsPGroup 5 (A⊔B:Subgroup G)) (h25:¬25∣Nat.card (A⊔B:Subgroup G)) : A=B := by
  obtain ⟨n,hn⟩:=IsPGroup.iff_card.mp hp
  have hle:n≤1 := by
    by_contra hh
    apply h25
    rw [hn]
    exact pow_dvd_pow 5 (by omega : 2≤n)
  have hc:Nat.card (A⊔B:Subgroup G)≤5 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hle
  have hAs:A=A⊔B:=eq_of_le_of_card_ge le_sup_left (hA.symm ▸ hc)
  have hBs:B=A⊔B:=eq_of_le_of_card_ge le_sup_right (hB.symm ▸ hc)
  exact hAs.trans hBs.symm

/-- A literal self-centralizing prime plane supplies its conjugation
representation with a five-group kernel, preserving the actual ambient map. -/
theorem plane_action_kernel (H W:Subgroup G) (hW:Nat.card W=25)
    (hWe:IsElementaryAbelian 5 W) (hc:centralizer (W:Set G)=W)
    (hn:H≤normalizer (W:Set G)) :
    ∃ρ:H→*Matrix.GeneralLinearGroup (Fin 2) (ZMod 5), IsPGroup 5 ρ.ker := by
  let : IsElementaryAbelian 5 W:=hWe
  obtain ⟨_,e,_⟩:=Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
    (p:=5) (V:=W) hW
  let α:H→*MulAut W:=W.normalizerMonoidHom.comp (inclusion hn)
  let ρ:=e.toMonoidHom.comp α
  have hker:ρ.ker≤W.subgroupOf H := by
    intro x hx
    have ha:α x=1:=e.injective ((show e (α x)=1 from hx).trans e.map_one.symm)
    have hxC:(x:G)∈centralizer (W:Set G) := by
      intro w hw
      have hh:=congrArg (fun a:MulAut W=>(a ⟨w,hw⟩:G)) ha
      change (x:G)*w*(x:G)⁻¹=w at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact hc ▸ hxC
  exact ⟨ρ,((IsElementaryAbelian.isPGroup 5 W).comap_of_injective H.subtype H.subtype_injective).to_le hker⟩

include c in
/-- The exact original uniqueness claim used to identify the six-gon of
parabolic edges with the six-gon of original five-subgroups. -/
theorem source_five_uniqueness (E:Subgroup G)
    (hE:Nonempty (E≃*Tits.ExceptionalParabolics.FullRee.first))
    (A1 A2:Subgroup G) (h1:A1≤E) (h2:A2≤E)
    (hA1:Nat.card A1=5) (hA2:Nat.card A2=5)
    (hc:B5Image B5≤centralizer (A1:Set G))
    (h5:IsPGroup 5 (B5Image B5⊔A2:Subgroup G)) : A1=A2 := by
  obtain ⟨e⟩:=hE
  obtain ⟨he3,he25⟩:=first_endpoint_order_obstructions e
  let H:Subgroup G:=A1⊔A2
  have hHE:H≤E:=sup_le h1 h2
  have hH3:¬3∣Nat.card H:=fun hh=>he3 (hh.trans (card_dvd_of_le hHE))
  have hH25:¬25∣Nat.card H:=fun hh=>he25 (hh.trans (card_dvd_of_le hHE))
  by_cases hcomm:B5Image B5≤centralizer (A2:Set G)
  · have ha1:A1≤fiveOddPart B5:=five_le_original_core c B5
      (IsPGroup.of_card (n:=1) hA1) (le_centralizer_iff.mp hc)
    have ha2:A2≤fiveOddPart B5:=five_le_original_core c B5
      (IsPGroup.of_card (n:=1) hA2) (le_centralizer_iff.mp hcomm)
    exact equality_of_five_join A1 A2 hA1 hA2
      ((IsPGroup.of_card (p:=5) (n:=3) (SourceCompletion.five_oddPart_card c B5)).to_le
        (sup_le ha1 ha2)) hH25
  obtain ⟨W,_,_,hW,hWe,hCW,hHW⟩:=exists_common_five_plane c B5 A1 A2 hA1 hc h5 hcomm
  obtain ⟨ρ,hρ⟩:=plane_action_kernel H W hW hWe hCW hHW
  have hA1H:A1≤H:=le_sup_left
  have hA2H:A2≤H:=le_sup_right
  have hAc:Nat.card (A1.subgroupOf H)=5:=
    (Nat.card_congr (subgroupOfEquivOfLe hA1H).toEquiv).trans hA1
  have hBc:Nat.card (A2.subgroupOf H)=5:=
    (Nat.card_congr (subgroupOfEquivOfLe hA2H).toEquiv).trans hA2
  have hgen:A1.subgroupOf H⊔A2.subgroupOf H=⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hA1H,map_subgroupOf_eq_of_le hA2H,
      ← MonoidHom.range_eq_map,H.range_subtype]
  have heq:=eq_of_plane_action (A1.subgroupOf H) (A2.subgroupOf H) hAc hBc hgen hH3 hH25 ρ hρ
  have hh:=congrArg (Subgroup.map H.subtype) heq
  rwa [map_subgroupOf_eq_of_le hA1H,map_subgroupOf_eq_of_le hA2H] at hh


include c in
/-- The same original claim applies to every actual conjugate of a recognized
first endpoint; B₅ and both source five-subgroups retain their ambient maps. -/
theorem source_five_uniqueness_conjugate (E:Subgroup G)
    (hE:Nonempty (E≃*Tits.ExceptionalParabolics.FullRee.first)) (g:G)
    (A1 A2:Subgroup G) (h1:A1≤E.conjBy g) (h2:A2≤E.conjBy g)
    (hA1:Nat.card A1=5) (hA2:Nat.card A2=5)
    (hc:B5Image B5≤centralizer (A1:Set G))
    (h5:IsPGroup 5 (B5Image B5⊔A2:Subgroup G)) : A1=A2 := by
  obtain ⟨e⟩:=hE
  let eg:E.conjBy g≃*E:=(E.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm
  exact source_five_uniqueness c B5 (E.conjBy g) ⟨eg.trans e⟩
    A1 A2 h1 h2 hA1 hA2 hc h5

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFiveUniqueness
