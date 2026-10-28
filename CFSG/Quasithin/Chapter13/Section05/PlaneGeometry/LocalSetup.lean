module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.BlockFromEscape
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.CentralizerImage
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
/-!
# The original LT application of C.1.24(c)

The marked natural action supplies its actual A₆ image, moved normal binary
module and Sylow factorization. Even characteristic gives F*(LT)=O₂(LT).
B.2.10 applied to the actual action range identifies C_T(V)=O₂(LT), retaining
both the ordinary and centrally covered local cases. The escaping normalizer
of C_T(W), together with the unique maximal two-local over LT, therefore
forces a transposition image. C.1.24(c) now gives the actual A₆ block.

Source: Aschbacher--Smith 13.5.6, printed p.917. The genuine earlier
quasisimplicity of L/O₂(L), unique maximal two-local overgroup, and the
normalizer escape are retained explicitly; no block or plane-fusion result
is an input.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

local notation "H" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LH" => L.subgroupOf H
local notation "VH" => V.subgroupOf H

theorem local_module_normal : (VH).Normal := normal_subgroupOf_of_le_normalizer d.normalizes_V
theorem local_module_elementary : IsElementaryAbelian 2 VH := by
  let := elementary d
  let e : VH≃*V := subgroupOfEquivOfLe (d.chosen.le_sylow.trans le_sup_right)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

noncomputable def localCoordinate : VH≃*Multiplicative (natural (Fin 6)) :=
  (subgroupOfEquivOfLe (d.chosen.le_sylow.trans le_sup_right)).trans d.coordinate

theorem localCoordinate_conjugation :
    letI := local_module_normal d
    ∀(g:H)(v:VH), (localCoordinate d (MulAut.conjNormal g v)).toAdd=
      naturalRepresentation (Fin 6) (permutation d g) (localCoordinate d v).toAdd := by
  intro g v
  exact conjugation d g ⟨v.val.val,v.property⟩

theorem permutation_local_image : (LH).map (permutation d)=alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rintro _ ⟨l,hl,rfl⟩
    have hh:=permutation_L d ⟨l,hl⟩
    exact hh ▸ (d.local_quotient (QuotientGroup.mk' _ ⟨l,hl⟩)).property
  · intro a ha
    obtain ⟨b,hb⟩:=d.local_quotient.surjective ⟨a,ha⟩
    obtain ⟨l,hl⟩:=QuotientGroup.mk'_surjective _ b
    refine ⟨inclusion le_sup_left l,l.property,?_⟩
    rw [permutation_L,hl,hb]

theorem local_sylow_product : ∀g:H,∃l∈LH,∃t∈(T.subtype (show (T:Subgroup G)≤H from le_sup_right):Subgroup H),l*t=g := by
  let : (LH).Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  intro g
  apply mem_sup_of_normal_left.mp
  rw [Sylow.coe_subtype,←subgroupOf_sup le_sup_left le_sup_right]
  exact g.property

theorem local_module_commutator_ne_bot : ⁅VH,LH⁆≠⊥ := by
  let := local_module_normal d
  intro hz
  have hk:LH≤(permutation d).ker := by
    rw [ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer
      VH (permutation d) (localCoordinate d) (localCoordinate_conjugation d)]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have ha:alternatingGroup (Fin 6)=⊥ := (permutation_local_image d).symm.trans
    ((Subgroup.map_eq_bot_iff _).mpr hk)
  have hh : (360:ℕ)=1 := by
    have hc : Nat.card (alternatingGroup (Fin 6))=360 := by
      rw [nat_card_alternatingGroup,Nat.card_fin];decide
    rw [←hc,ha,Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance,inferInstance⟩
  omega

theorem local_characteristic_two : generalizedFitting H=pCore 2 H := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply Chapter1.mem_He_iff.mp
  apply Chapter1.lemma_1_1_4_6 T (d.counterexample.qtke.evenCharacteristic T)
  refine ⟨?_,show (T:Subgroup G)≤H from le_sup_right⟩
  intro he
  exact d.counterexample.local_component.1.2
    ((pCore 2 H).map_eq_bot_iff_of_injective (H).subtype_injective |>.mp he)

theorem local_component_characteristic_two : generalizedFitting LH=pCore 2 LH := by
  have he:=subgroupOfEquivOfLe (show L≤H from le_sup_left)
  apply (Subgroup.map_injective (f:=he.toMonoidHom) he.injective)
  rw [map_generalizedFitting_equiv,pCore_map_iso]
  exact d.counterexample.local_component.2.1.2.2

theorem permutation_range_twoCore : pCore 2 (permutation d).range=⊥ := by
  have hi:(permutation d).range.index∣2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le (alternating_le_range d)
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi|hi
  · have hr:=index_eq_one.mp hi
    have he:pCore 2 (⊤:Subgroup (Equiv.Perm (Fin 6)))=⊥ := by
      apply (Subgroup.map_injective (f:=(Subgroup.topEquiv : (⊤:Subgroup (Equiv.Perm (Fin 6)))≃*Equiv.Perm (Fin 6)).toMonoidHom) Subgroup.topEquiv.injective)
      rw [pCore_map_iso,Subgroup.map_bot]
      exact Theory.SpecificGroups.SymmetricSix.s6_twoCore_eq_bot
    rw [hr]
    exact he
  · have hr:=Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    rw [hr]
    exact Theory.SpecificGroups.SymmetricSix.a6_twoCore_eq_bot


omit [Finite G] d in
theorem local_quotient_quasisimple (hq:IsQuasisimple (L⧸pCore 2 L)) :
    IsQuasisimple ((LH)⧸pCore 2 (LH)) := by
  let := hq
  let e : LH≃*L := subgroupOfEquivOfLe le_sup_left
  exact IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

theorem local_sylow_centralizer (hq:IsQuasisimple (L⧸pCore 2 L)) :
    (L⊔(T:Subgroup G)).pCoreIn 2=(T:Subgroup G)⊓centralizer (V:Set G) := by
  let := local_module_normal d
  let := local_module_elementary d
  let q := (permutation d).rangeRestrict
  have hk:q.ker=centralizer (VH:Set H) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer
      VH (permutation d) (localCoordinate d) (localCoordinate_conjugation d)
  have hh := internalModule_residual_structure VH q (permutation d).rangeRestrict_surjective
    hk (permutation_range_twoCore d) (T.subtype le_sup_right) LH
    (Or.inl ⟨d.counterexample.local_component.1.1,local_quotient_quasisimple hq⟩)
    (local_module_commutator_ne_bot d) (local_sylow_product d)
  change (pCore 2 H).map (H).subtype=_
  rw [hh.1]
  ext x
  constructor
  · rintro ⟨a,⟨ha,hc⟩,rfl⟩
    refine ⟨ha,?_⟩
    intro v hv
    exact congrArg Subtype.val (hc ⟨v,d.chosen.le_sylow.trans le_sup_right hv⟩ hv)
  · rintro ⟨ht,hc⟩
    refine ⟨⟨x,mem_sup_right ht⟩,⟨ht,?_⟩,rfl⟩
    intro v hv
    exact Subtype.ext (hc v.val hv)

theorem transposition_of_escaping_normalizer
    (hq:IsQuasisimple (L⧸pCore 2 L))
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M)
    (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0)
    (he:¬normalizer (planeCentralizer (T:=T) W:Set G)≤M) :
    ∃r:Equiv.Perm (Fin 6),r.IsSwap∧planeCentralizerImage d W=zpowers r := by
  apply planeCentralizer_transposition_of_nontrivial_action d W hWV hcard hn
  intro hc
  have hQ:planeCentralizer (T:=T) W=(H).pCoreIn 2 := by
    rw [local_sylow_centralizer d hq]
    exact le_antisymm (le_inf inf_le_left hc)
      (inf_le_inf_left _ (centralizer_le hWV))
  apply he
  rw [hQ]
  apply normalizer_le_of_unique_maximalTwoLocal hu
    (pCore_isPGroup.map (H).subtype) ?_ ?_
  · exact fun hz=>d.chosen.ne_bot (le_bot_iff.mp (hz ▸ d.chosen.le_core))
  · exact (H).le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))


/-- The literal 13.5.6 block consequence, with all C.1.24 local action,
module, kernel, component and characteristic-two hypotheses constructed. -/
theorem source_alternatingBlock_of_escape
    (hq:IsQuasisimple (L⧸pCore 2 L))
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M)
    (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0)
    (he:¬normalizer (planeCentralizer (T:=T) W:Set G)≤M) :
    ChapterC.IsAlternatingBlock (L.subgroupOf H) 6 := by
  let := local_module_normal d
  let := local_module_elementary d
  let := local_quotient_quasisimple (T:=T) hq
  obtain ⟨r,hr,hR⟩:=transposition_of_escaping_normalizer d hq hu W hWV hcard hn he
  let R := (planeCentralizer (T:=T) W).subgroupOf H
  apply alternatingBlock_of_natural_six_and_unique H M LH VH R
    d.counterexample.local_component.1.1 (local_characteristic_two d)
    (local_component_characteristic_two d) (T.subtype le_sup_right) ?_ ?_
    (local_sylow_product d) (permutation d) (permutation_local_image d)
    (localCoordinate d) (localCoordinate_conjugation d)
    (local_module_commutator_ne_bot d) r hr hR hu ?_
  · intro a ha
    have haG : a.val∈(H).pCoreIn 2:=mem_map_of_mem (H).subtype ha
    have hc:=d.chosen.core_centralizes haG
    have ht:(a:G)∈(T:Subgroup G) := by
      exact pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right) ha
    exact ⟨ht,centralizer_le hWV hc⟩
  · exact fun _ ha=>ha.1
  · simpa only [R,map_subgroupOf_eq_of_le
      (show planeCentralizer (T:=T) W≤H from inf_le_left.trans le_sup_right)] using he

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
