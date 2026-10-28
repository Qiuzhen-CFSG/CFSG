module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ComponentClosure
public import Theory.Representation.G2BinaryPlaneKernel
public import Theory.SpecificGroups.SymmetricTwoResidual
/-!
# The original plane residual's cubic image and two-group kernel

The pointwise stabilizer of the marked native plane lies in the binary
unipotent group. Pulling this back through the literal component action,
whose kernel is contained in its two-core, proves that C_L(V₂) is a
two-group. A two-perfect plane actor has image in A₃; its lifted native
cubic acts nontrivially, so its actual plane image has order three.

These are the local action inputs of 13.3.15, now supplied to the literal
13.3.18 component-closure consumer. Source: printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative IsKleinFour
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- A subgroup of the original component centralizing the marked plane is
a two-group, by the literal natural action and its genuine faithful kernel. -/
theorem source_plane_centralizer_isTwo (L B:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane)
    (hLN:L≤normalizer (V:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2) :
    IsPGroup 2 (L⊓centralizer (B:Set G):Subgroup G) := by
  let A:=L⊓centralizer (B:Set G)
  have hAN:A≤normalizer (V:Set G):=inf_le_left.trans hLN
  let f:A→*Atlas.G2.Model F:=rho.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hAN))
  have hk:f.ker≤(L.pCoreIn 2).comap A.subtype := by
    intro a ha
    apply hfaith
    refine ⟨a.prop.1,?_⟩
    intro v hv
    let w:Additive V:=Additive.ofMul ⟨v,hv⟩
    have hh:=he (V.normalizerMonoidHom.rangeRestrict (inclusion hAN a)) w
    have hf:f a=1:=ha
    change E (automizerRepresentation V _ w)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (f a) (E w) at hh
    rw [hf,map_one,Module.End.one_apply] at hh
    have hc:a.val*v*a.val⁻¹=v:=congrArg (fun x:Additive V=>(x.toMul:G)) (E.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hker:IsPGroup 2 f.ker:=((isPGroup_pCoreIn 2 L).comap_subtype).to_le hk
  have him:∀a:A,f a∈Atlas.G2.unipotent := by
    intro a
    apply plane_pointwise_le_unipotent
    intro v hv
    obtain ⟨w,rfl⟩:=E.surjective v
    have hw:w.toMul.val∈B:=(mem_pointCoordinateSubspace E B w).mp (hp.symm ▸ hv)
    change Atlas.G2.Restricted.NaturalCoordinates.action F
      (rho (V.normalizerMonoidHom.rangeRestrict (inclusion hAN a))) (E w)=E w
    rw [←he]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.val*w.toMul.val*a.val⁻¹=w.toMul.val
    rw [←mem_centralizer_iff.mp a.prop.2 _ hw,mul_inv_cancel_right]
  have hu:IsPGroup 2 (Atlas.G2.unipotent (K:=F)):=
    IsPGroup.of_card (n:=6) Atlas.G2.BinaryParabolicPair.card_unipotent_binary
  have htop:Atlas.G2.unipotent.comap f=⊤:=top_unique (fun a _=>him a)
  have hall:=hu.comap_of_ker_isPGroup f hker
  rw [htop] at hall
  exact hall.of_equiv Subgroup.topEquiv

/-- A two-perfect original plane actor with the actual cubic in its module
image has plane image of order three. -/
theorem source_plane_action_card_three (B X:Subgroup G) [IsKleinFour B]
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane)
    (hXB:X≤normalizer (B:Set G)) (hX:IsPPerfect 2 X)
    (hc:Atlas.G2.BinaryParabolicPair.cubicActor∈(inducedAutomizer V X).map rho) :
    Nat.card ((X.subgroupOf (normalizer (B:Set G))).map
      (Chapter13.Section05.AmbientSource.planeAction B))=3 := by
  let N:=normalizer (B:Set G)
  let A:=X.subgroupOf N
  let f:=Chapter13.Section05.AmbientSource.planeAction B
  have hpA:IsPPerfect 2 A:=hX.of_surjective
    (subgroupOfEquivOfLe hXB).symm.toMonoidHom (subgroupOfEquivOfLe hXB).symm.surjective
  have hA:A.map f≤alternatingGroup (Fin 3) := by
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    exact (map_mono (le_pResidual_of_isPPerfect A hpA)).trans (map_pResidual_le 2 f)
  have hdiv:Nat.card (A.map f)∣3 := by
    have hh:=card_dvd_of_le hA
    have hc:Nat.card (alternatingGroup (Fin 3))=3 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      rfl
    rwa [hc] at hh
  have hne:A.map f≠⊥ := by
    intro hbot
    obtain ⟨i,⟨n,hnX,rfl⟩,hnative⟩:=hc
    have hnC:n.val∈centralizer (B:Set G) := by
      apply (Chapter13.Section05.AmbientSource.planeAction_eq_one B ⟨n,hXB hnX⟩).mp
      have hh:f ⟨n,hXB hnX⟩∈A.map f:=⟨⟨n,hXB hnX⟩,hnX,rfl⟩
      rw [hbot] at hh
      exact hh
    obtain ⟨w,hw⟩:=E.surjective (Pi.single 0 1)
    have hwB:w.toMul.val∈B:= (mem_pointCoordinateSubspace E B w).mp (by
      rw [hp,hw,mem_plane];simp)
    have hfix:automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) w=w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change n.val*w.toMul.val*n.val⁻¹=w.toMul.val
      rw [←mem_centralizer_iff.mp hnC _ hwB,mul_inv_cancel_right]
    apply plane_cubic_moves
    rw [←hw,←hnative,←he,hfix]
  have hh:1<Nat.card (A.map f):=(A.map f).one_lt_card_iff_ne_bot.mpr hne
  rcases (Nat.dvd_prime (by decide:Nat.Prime 3)).mp hdiv with h|h
  · omega
  · exact h
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
