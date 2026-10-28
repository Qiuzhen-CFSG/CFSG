module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFrame
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Local

/-!
# The full five automizer inside the original first parabolic

The first parabolic maps onto the normalizer of its marked five-group in
S₅. Its kernel is a two-group, so Sylow normalizer lifting realizes every
automorphism of the literal B₅ inside F₁. In particular its squaring actor
can be chosen in F₁ itself. This supplies the complement action needed
by the F.1.12 binary Ree endpoint recognition.

Source: Aschbacher–Smith J.4.5, printed pp.441–442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

private theorem sylow_normalizer_image {H K:Type*} [Group H] [Finite H] [Group K]
    {q:ℕ} [Fact q.Prime] (P:Sylow q H) (f:H→*K) :
    (normalizer (P:Set H)).map f=normalizer (P.map f:Set K)⊓f.range := by
  let g:=f.rangeRestrict
  have he:f.range.subtype.comp g=f:=rfl
  have h := congrArg (Subgroup.map f.range.subtype)
    (P.normalizer_map_surjective g f.rangeRestrict_surjective)
  rw [map_map,he] at h
  have hma:(P.map g).map f.range.subtype=P.map f := by rw [map_map,he]
  have hb:(P.map f).comap f.range.subtype=P.map g := by
    rw [←hma,comap_map_eq_self_of_injective f.range.subtype_injective]
  have hle:P.map f≤f.range.subtype.range:=by rw [range_subtype];exact map_le_range _ _
  rw [←hb,←comap_normalizer_eq_of_le_range hle,map_comap_eq,range_subtype,inf_comm] at h
  exact h

/-- The original first endpoint realizes all automorphisms of its literal B₅. -/
theorem SourceChoice.F₁_five_full_action (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Function.Surjective ((B5Image B5).normalizerMonoidHom.comp
      ((p.F₁ B5).subgroupOf (normalizer (B5Image B5:Set G))).subtype) := by
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let F:=p.F₁ B5
  let A:Subgroup F:=(B5Image B5).subgroupOf F
  have hBF:B5Image B5≤F:=le_sup_right
  have hcA:Nat.card A=5:=(Nat.card_congr (subgroupOfEquivOfLe hBF).toEquiv).trans
    (B5Image_card d.card_Z B5)
  let P:Sylow 5 F:=Sylow.ofCard A (by
    rw [hcA,s.card_F₁ p B5 hi]
    decide +kernel)
  let f:F→*S5:=d.ru2.quotientMap.comp (inclusion (p.F₁_le_H B5))
  let B:Subgroup S5:=B5.map d.ru2.quotientMap
  have hmap:A.map f=B:=by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨b,hb,he⟩:=ha
      refine ⟨b,hb,?_⟩
      have haeq:b=inclusion (p.F₁_le_H B5) a:=Subtype.ext he
      rw [haeq]
      rfl
    · rintro ⟨b,hb,rfl⟩
      have hbim:(b:G)∈B5Image B5:=mem_map_of_mem d.toTypeRuSetup.H.subtype hb
      exact ⟨⟨b,hBF hbim⟩,hbim,rfl⟩
  have hr:f.range=normalizer (B:Set S5):=by
    rw [MonoidHom.range_comp,inclusion_range]
    exact s.F₁_image p B5 hi
  have hk:f.ker=d.toTypeRuSetup.Q.subgroupOf F:=by
    ext x
    change inclusion (p.F₁_le_H B5) x∈d.ru2.quotientMap.ker ↔ _
    rw [d.ru2.quotient_kernel]
    rfl
  have hkp:IsPGroup 2 f.ker:=by rw [hk];exact (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).comap_subtype
  have hAp:IsPGroup 5 A:=IsPGroup.of_card (n:=1) (by simpa using hcA)
  have hdis:=hAp.disjoint_of_coprime hkp (by decide:Nat.Coprime 5 2)
  have hf:Function.Injective (f.subgroupMap A):=by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    exact hdis.le_bot ⟨a.property,congrArg Subtype.val ha⟩
  let e:A≃*B:=(MulEquiv.ofBijective (f.subgroupMap A)
    ⟨hf,f.subgroupMap_surjective A⟩).trans (MulEquiv.subgroupCongr hmap)
  have hcB:Nat.card B=5:=(Nat.card_congr e.toEquiv).symm.trans hcA
  apply normalizerMonoidHom_restrict_surjective _ _ hBF
  apply normalizerMonoidHom_surjective_of_lift A B f e (fun _=>rfl)
  · have h:=sylow_normalizer_image P f
    change (normalizer (A:Set F)).map f=normalizer (A.map f:Set S5)⊓f.range at h
    rw [hmap,hr,inf_idem] at h
    exact h.ge
  · exact Equiv.Perm.five_subgroup_full_automizer B hcB

/-- Lift the squaring automorphism inside the actual F₁, preserving B₅. -/
theorem SourceChoice.exists_F₁_squaring_element (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃g:G,g∈p.F₁ B5 ∧ g∈normalizer (B5Image B5:Set G) ∧
      ∀a∈B5Image B5,g*a*g⁻¹=a^2 := by
  let A:=B5Image B5
  have hA:Nat.card A=5:=B5Image_card d.card_Z B5
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let : IsCyclic A:=isCyclic_of_prime_card hA
  let : CommGroup A:=IsCyclic.commGroup
  let square:MulAut A:={powCoprime (show (Nat.card A).Coprime 2 by rw [hA];decide) with
    map_mul':=fun x y=>mul_pow x y 2}
  obtain ⟨g,hg⟩:=s.F₁_five_full_action B5 hi square
  refine ⟨g,g.property,g.val.property,?_⟩
  intro a ha
  exact congrArg (fun f:MulAut A=>(f ⟨a,ha⟩:G)) hg

end CFSG.Quasithin.ChapterJ.RuSubgroup
