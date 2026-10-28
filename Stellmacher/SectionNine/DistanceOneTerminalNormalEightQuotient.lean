module

public import Stellmacher.SectionNine.DistanceOneFirstCoreQuotient
public import Stellmacher.SectionThree.CharacteristicTwoNormalEightQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The actual terminal core quotient from a normal elementary eight

In the critical-length-one configuration, a normal elementary subgroup U of
order8 in the terminal core, containing the terminal center Z of order2,
identifies the terminal quotient with SL2(2), provided the common Sylow has
order128, the terminal core order64, [U,Q]≤Z, and C_Q(U) has order16.
These exact intermediate properties remain explicit. The characteristic-two
condition and actual Sylow come from the original local context.

Restrict U,Z and the centralizer to the literal terminal stabilizer. The
native core is the restriction of the ambient terminal core, and subgroup
embeddings preserve the given orders. The normal-eight characteristic-two
recognition theorem gives its quotient S3. Compose that quotient equivalence
with the projective-line model of SL2(2) to obtain the requested surjection
with exactly the ambient core's restricted kernel.

This is the native group transport for Stellmacher(9.1), Journal of Algebra
190 (1997), p.48. It uses no full local conclusion or prior terminal quotient;
separate producers establish U and its centralizer order.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix

public theorem distance_one_terminal_quotient_of_normal_eight
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (hb : ctx.criticalPath.length=1)
    (hTcard : Nat.card T=128) (hQcard : Nat.card (q ctx.Γ ctx.criticalPath.a')=64)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUQ : U≤q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a'≤U)
    (hUn : stabilizer ctx.Γ ctx.criticalPath.a'≤Subgroup.normalizer (U:Set G))
    (hUcard : Nat.card U=8) (hZcard : Nat.card (z ctx.Γ ctx.criticalPath.a')=2)
    (hcomm : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆≤z ctx.Γ ctx.criticalPath.a')
    (hCcard : Nat.card (q ctx.Γ ctx.criticalPath.a'⊓Subgroup.centralizer (U:Set G):Subgroup G)=16) :
    QuotientIsModel (stabilizer ctx.Γ ctx.criticalPath.a') (q ctx.Γ ctx.criticalPath.a') SL2Two := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a'
  let Q := q ctx.Γ ctx.criticalPath.a'
  let Z := z ctx.Γ ctx.criticalPath.a'
  have hend : ctx.criticalPath.a'=ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end,← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb
  obtain ⟨hTP,R,hR⟩ := by
    have h := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    rw [← hend] at h
    exact h
  change T≤P at hTP
  have hQP : Q≤P := by
    change q ctx.Γ ctx.criticalPath.a'≤stabilizer ctx.Γ ctx.criticalPath.a'
    rw [q,ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hUP : U≤P := hUQ.trans hQP
  have hZP : Z≤P := hZU.trans hUP
  have hQnative : Q.subgroupOf P=pCore 2 P := by
    change (q ctx.Γ ctx.criticalPath.a').subgroupOf P=pCore 2 P
    rw [q,ctx.Γ.twoCoreAt_def]
    change ((pCore 2 P).map P.subtype).comap P.subtype=pCore 2 P
    exact Subgroup.comap_map_eq_self (by simp)
  have hRn : Nat.card R=128 := by
    have h := (Subgroup.card_map_of_injective (K:=(R:Subgroup P)) P.subtype_injective).symm
    rw [hR,hTcard] at h
    exact h
  have hQncard : Nat.card (pCore 2 P)=64 := by
    rw [← hQnative,Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv]
    exact hQcard
  let Un := U.subgroupOf P
  let Zn := Z.subgroupOf P
  let _ : Un.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mpr hUn
  let _ : Zn.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr
    (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a')
  let _ : IsElementaryAbelian 2 Un := IsElementaryAbelian.subgroupOf hUP
  have hUncard : Nat.card Un=8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv).trans hUcard
  have hZncard : Nat.card Zn=2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv).trans hZcard
  have hUnQ : Un≤pCore 2 P := by
    rw [← hQnative]
    exact Subgroup.subgroupOf_mono P hUQ
  have hZnU : Zn≤Un := Subgroup.subgroupOf_mono P hZU
  have hcommn : ⁅Un,pCore 2 P⁆≤Zn := by
    rw [← hQnative]
    apply Subgroup.commutator_le.mpr
    intro u hu q hq
    exact hcomm (Subgroup.commutator_mem_commutator hu hq)
  have hCeq : pCore 2 P⊓Subgroup.centralizer (Un:Set P)=
      (Q⊓Subgroup.centralizer (U:Set G)).subgroupOf P := by
    rw [← hQnative]
    ext p
    constructor
    · intro hp
      refine ⟨hp.1,Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hp.2 (⟨u,hUP hu⟩:P) hu)
    · intro hp
      refine ⟨hp.1,Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hp.2 u hu)
  have hCnative : Nat.card (pCore 2 P⊓Subgroup.centralizer (Un:Set P):Subgroup P)=16 := by
    rw [hCeq,Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hQP)).toEquiv]
    exact hCcard
  have hchar : IsCharacteristicTwoType P := by
    have h := (edge_characteristic_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    rw [← hend] at h
    exact h
  obtain ⟨e⟩ := SectionThree.quotient_s3_of_normal_elementary_eight R hRn hQncard
    Un Zn hZnU hUnQ hUncard hZncard hcommn hCnative hchar
  obtain ⟨m⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f : P→*SL2Two := (e.trans m.symm).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  refine ⟨f,(e.trans m.symm).surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  change f.ker=Q.subgroupOf P
  ext p
  change (e.trans m.symm) ((QuotientGroup.mk' (pCore 2 P)) p)=1 ↔ p∈Q.subgroupOf P
  rw [MulEquiv.map_eq_one_iff, hQnative]
  exact QuotientGroup.eq_one_iff p
end Stellmacher.SectionNine
