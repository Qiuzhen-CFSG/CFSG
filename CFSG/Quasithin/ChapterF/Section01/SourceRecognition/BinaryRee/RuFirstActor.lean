module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFiveAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFirstNormalizer
public import Theory.SpecificGroups.ReeTwo.SquaringActionCensus

/-!
# Actual cyclic-four extensions of the first Ree core

The normalized native five-action and the actual F₁ squaring lift put its
core action in the verified forty-element census. Thus the lift's fourth
power centralizes the core and belongs to the original Z. Its square
cannot lie in the core: that would put the nontrivial cube of a five-element
in a two-group. The literal generated quotient is cyclic of order four,
so the generated subgroup has order 4096.

The final source theorem constructs all these data from the original
TypeRu choices, with both the ambient central marking and B₅ action retained.
Source: Aschbacher–Smith J.4.5, printed pp.441–442, and the verified
Shinoda core action census used for the F.1.12 binary Ree branch.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem firstCoreAction_eq_one_iff (B5:Sylow 5 d.toTypeRuSetup.H)
    (e:fiveHyperplane d B5≃*ReeTwo.Core)
    (g:normalizer (fiveHyperplane d B5:Set G)) :
    firstCoreAction B5 e g=1 ↔ (g:G)∈d.toTypeRuSetup.Z := by
  change (MulAut.congr e) ((fiveHyperplane d B5).normalizerMonoidHom g)=1 ↔ _
  rw [←(MulAut.congr e).map_one,(MulAut.congr e).injective.eq_iff]
  change g∈(fiveHyperplane d B5).normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  change (g:G)∈centralizer (fiveHyperplane d B5:Set G) ↔ _
  rw [centralizer_Q₀_sup_Q₅]

theorem firstCore_squaring_actor_four_mem_Z (B5:Sylow 5 d.toTypeRuSetup.H)
    (e:fiveHyperplane d B5≃*ReeTwo.Core)
    (g:normalizer (fiveHyperplane d B5:Set G))
    (hsq:firstCoreAction B5 e g*ReeTwo.Core.c*(firstCoreAction B5 e g)⁻¹=ReeTwo.Core.c^2) :
    (g:G)^4∈d.toTypeRuSetup.Z := by
  have h := (firstCoreAction_eq_one_iff B5 e (g^4)).mp (by
      rw [map_pow]
      exact ReeTwo.Core.squaring_action_four _ hsq)
  simpa only [coe_pow] using h

private theorem mem_two_zpowers {H:Type*} [Group H] [Finite H]
    (z x:H) (hz:orderOf z=2) (hx:x∈zpowers z) : x=1 ∨ x=z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,hz] at hx
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hx
  have hn2:=Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem square_conjugates_fourth {H:Type*} [Group H] (g c:H)
    (h:g*c*g⁻¹=c^2) : g^2*c*(g^2)⁻¹=c^4 := by
  calc
    g^2*c*(g^2)⁻¹ = g*(g*c*g⁻¹)*g⁻¹ := by simp only [pow_two]; group
    _ = g*c^2*g⁻¹ := by rw [h]
    _ = (g*c*g⁻¹)^2 := by simp only [pow_two]; group
    _ = c^4 := by rw [h,←pow_mul]

/-- The square of a genuine squaring lift does not lie in the first core. -/
theorem SourceChoice.firstCore_squaring_square_not_mem (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (c:B5Image B5) (hc:orderOf c=5) (g:G)
    (hsq:g*(c:G)*g⁻¹=(c:G)^2) : g^2∉fiveHyperplane d B5 := by
  intro hg2
  have hdis:Disjoint (fiveHyperplane d B5) (B5Image B5):=disjoint_of_coprime_natCard
    (by rw [fiveHyperplane_card,B5Image_card d.card_Z];decide)
  have hcN:(c:G)∈normalizer (fiveHyperplane d B5:Set G):=
    s.F₁_normalizes_fiveHyperplane p B5 hi
      ((show B5Image B5≤p.F₁ B5 from le_sup_right) c.property)
  have hcm:⁅g^2,(c:G)⁆∈fiveHyperplane d B5 := by
    rw [commutatorElement_def]
    have hcon:(c:G)*(g^2)⁻¹*(c:G)⁻¹∈fiveHyperplane d B5:=
      (mem_normalizer_iff.mp hcN _).mp (inv_mem hg2)
    simpa only [mul_assoc] using mul_mem hg2 hcon
  have he:⁅g^2,(c:G)⁆=(c:G)^3:=by
    rw [commutatorElement_def,square_conjugates_fourth g c hsq]
    group
  rw [he] at hcm
  have hone:(c:G)^3=1:=hdis.le_bot ⟨hcm,pow_mem c.property 3⟩
  have hd:=orderOf_dvd_of_pow_eq_one hone
  rw [orderOf_coe,hc] at hd
  norm_num at hd

/-- The original core and a squaring actor generate a two-group of order 4096. -/
theorem firstCoreExtension_card (B5:Sylow 5 d.toTypeRuSetup.H) (g:G)
    (hn:g∈normalizer (fiveHyperplane d B5:Set G))
    (hfour:g^4∈fiveHyperplane d B5) (hnot:g^2∉fiveHyperplane d B5) :
    Nat.card (fiveHyperplane d B5⊔zpowers g:Subgroup G)=4096 := by
  let R:=fiveHyperplane d B5
  let S:=R⊔zpowers g
  let K:=R.subgroupOf S
  have hRS:R≤S:=le_sup_left
  let : K.Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le R.le_normalizer (zpowers_le.mpr hn))
  let a:S:=⟨g,(show zpowers g≤S from le_sup_right) (mem_zpowers g)⟩
  let q:S→*S⧸K:=QuotientGroup.mk' K
  have hg:K⊔zpowers a=⊤:=by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRS,MonoidHom.map_zpowers,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hq:zpowers (q a)=⊤:=by
    have hh:=congrArg (Subgroup.map q) hg
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,MonoidHom.map_zpowers,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)] at hh
    exact hh
  have hqo:orderOf (q a)=4:=by
    apply @orderOf_eq_prime_pow _ _ (q a) 1 2 ⟨Nat.prime_two⟩
    · intro h
      apply hnot
      have hh: a^2∈K:=by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (a^2)=1
        rw [map_pow]
        simpa only [pow_one] using h
      change ((a^2:S):G)∈R at hh
      simpa only [coe_pow] using hh
    · apply (map_pow q a 4).symm.trans
      apply (QuotientGroup.eq_one_iff _).mpr
      change ((a^4:S):G)∈R
      simpa only [coe_pow] using hfour
  have hqcard:Nat.card (S⧸K)=4:=(orderOf_eq_card_of_zpowers_eq_top hq).symm.trans hqo
  have hkcard:Nat.card K=1024:=(Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv).trans
    (fiveHyperplane_card d B5)
  have hc:=card_eq_card_quotient_mul_card_subgroup K
  rw [hqcard,hkcard] at hc
  exact hc

/-- The source lift is an actual squaring actor on the marked core; its fourth
power is either trivial or the original central involution. -/
theorem SourceChoice.exists_firstCore_extension_actor (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(e:fiveHyperplane d B5≃*ReeTwo.Core)(c:B5Image B5)
      (g:normalizer (fiveHyperplane d B5:Set G)),
      zpowers (e.symm (ReeTwo.Core.root 9):G)=d.toTypeRuSetup.Z ∧
      (e.symm (ReeTwo.Core.root 2):G)∈centralizer (B5Image B5:Set G) ∧
      zpowers (c:G)=B5Image B5 ∧ orderOf c=5 ∧
      (∀x:ReeTwo.Core,(e.symm (ReeTwo.Core.c x):G)=(c:G)*(e.symm x:G)*(c:G)⁻¹) ∧
      (g:G)∈p.F₁ B5 ∧ (g:G)∈normalizer (B5Image B5:Set G) ∧
      (∀a∈B5Image B5,(g:G)*a*(g:G)⁻¹=a^2) ∧
      firstCoreAction B5 e g*ReeTwo.Core.c*(firstCoreAction B5 e g)⁻¹=ReeTwo.Core.c^2 ∧
      (firstCoreAction B5 e g)^4=1 ∧
      ((g:G)^4=1 ∨ (g:G)^4=(e.symm (ReeTwo.Core.root 9):G)) ∧
      (g:G)^2∉fiveHyperplane d B5 ∧
      Nat.card (fiveHyperplane d B5⊔zpowers (g:G):Subgroup G)=4096 := by
  obtain ⟨e,c,hz,ht,hc,hco,ha⟩:=s.exists_firstCore_five_marking B5 hi
  obtain ⟨g,hgF,hgN,hgsq⟩:=s.exists_F₁_squaring_element B5 hi
  have hFN:=s.F₁_normalizes_fiveHyperplane p B5 hi
  let gN:normalizer (fiveHyperplane d B5:Set G):=⟨g,hFN hgF⟩
  let cN:normalizer (fiveHyperplane d B5:Set G):=⟨c,hFN ((show B5Image B5≤p.F₁ B5 from le_sup_right) c.property)⟩
  let f:=firstCoreAction B5 e
  have hfc:f cN=ReeTwo.Core.c:=by
    apply MulEquiv.ext
    intro x
    apply e.symm.injective
    apply Subtype.ext
    have hh:=firstCoreAction_apply B5 e cN (e.symm x)
    rw [e.apply_symm_apply] at hh
    exact hh.trans (ha x).symm
  have hconj:gN*cN*gN⁻¹=cN^2:=Subtype.ext (hgsq c c.property)
  have hsq:f gN*ReeTwo.Core.c*(f gN)⁻¹=ReeTwo.Core.c^2:=by
    have hh:=congrArg f hconj
    simpa only [map_mul,map_inv,map_pow,hfc] using hh
  have hfour: (f gN)^4=1:=ReeTwo.Core.squaring_action_four _ hsq
  have hgZ:=firstCore_squaring_actor_four_mem_Z B5 e gN hsq
  have hzorder:orderOf (e.symm (ReeTwo.Core.root 9):G)=2:=by
    rw [←Nat.card_zpowers,hz]
    exact d.card_Z
  have hnot:=s.firstCore_squaring_square_not_mem B5 hi c hco g (hgsq c c.property)
  have hZR:d.toTypeRuSetup.Z≤fiveHyperplane d B5:=
    d.ru2.natural.kernel_le.trans (U_le_fiveHyperplane d B5)
  refine ⟨e,c,gN,hz,ht,hc,hco,ha,hgF,hgN,hgsq,hsq,hfour,
    mem_two_zpowers _ _ hzorder (by rwa [hz]),hnot,?_⟩
  exact firstCoreExtension_card B5 g (hFN hgF) (hZR hgZ) hnot

end CFSG.Quasithin.ChapterJ.RuSubgroup
