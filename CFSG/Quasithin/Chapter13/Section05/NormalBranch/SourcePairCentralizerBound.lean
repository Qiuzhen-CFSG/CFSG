module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer.GeneratedCore
public import Theory.Representation.FirstCohomologyAutomorphism.Cocycle
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Normalized

/-!
# The original centralizer-factor dichotomy

After C_T(L)=1, conjugation embeds C_T(K) in the normalized one-cocycles
of the natural A₆ module that vanish on the actual A₅ point stabilizer.
The proved coordinate-cocycle classification identifies that space with F₂,
so C_T(K) has order at most two. The original core splitting then gives
Q=V×C_T(K) and |Q:V|=|C_T(K)|, including the trivial-or-order-two dichotomy
used by the exceptional quotient argument toward Conclusions.seven.

This proves the literal C.1.13(b)/I.1.6(5) application in the proof of
Aschbacher–Smith13.5.15(7), printed p.920. The source endpoints obtain
C_T(L)=1 from the original generated-core hypothesis, so no earlier
maximality input remains. The previous public interfaces are retained.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizerBound
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open ChapterC
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

omit h e hseed hn hU in
private theorem local_core_commutator : ⁅D.L,D.LT.pCoreIn 2⁆≤D.L.pCoreIn 2 := by
  have hLQ : D.L≤normalizer (D.LT.pCoreIn 2:Set G) :=
    le_sup_left.trans (D.LT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT)))
  have hQL : D.LT.pCoreIn 2≤normalizer (D.L:Set G) :=
    (pCoreIn_le_sylow D.LT (D.T.subtype le_sup_right)).trans
      ((map_subgroupOf_eq_of_le le_sup_right).le.trans d.normalizes_L)
  exact le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 D.LT).to_le (le_normalizer_iff_commutator_le_right.mp hLQ))
    (le_normalizer_iff_commutator_le_left.mp hQL) (normalizer_commutator_ge_left _ _)

omit h e hseed hn hU in
private theorem layer_equivariant
    (hB : (blockU D.L).map D.L.subtype=D.V) (g : D.L) (v : natural (Fin 6)) :
    ((SourceSixBlock.layerEquiv d hB).symm
        (Multiplicative.ofAdd (alternatingNaturalRepresentation (Fin 6) (SourceSixBlock.actor d g) v)) : D.L)=
      g*((SourceSixBlock.layerEquiv d hB).symm (Multiplicative.ofAdd v):D.L)*g⁻¹ := by
  let eV:=SourceSixBlock.layerEquiv d hB
  have he : eV.symm (Multiplicative.ofAdd
      (alternatingNaturalRepresentation (Fin 6) (SourceSixBlock.actor d g) v))=
      blockConjugate D.L g (eV.symm (Multiplicative.ofAdd v)) := by
    apply eV.injective
    apply Multiplicative.toAdd.injective
    rw [eV.apply_symm_apply]
    have hh := SourceSixBlock.layerEquiv_equivariant d hB g (eV.symm (Multiplicative.ofAdd v))
    change (eV (blockConjugate D.L g (eV.symm (Multiplicative.ofAdd v)))).toAdd =
      alternatingNaturalRepresentation (Fin 6) (SourceSixBlock.actor d g)
        (eV (eV.symm (Multiplicative.ofAdd v))).toAdd at hh
    rw [eV.apply_symm_apply] at hh
    exact hh.symm
  exact congrArg Subtype.val he

/-- The original centralizer factor has at most two elements. -/
theorem pair_centralizer_card_le_two_of_centralizer_eq_bot
    (g : D.L) (_hK : NormalBranch.K D g.val≤D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hcentral : (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥) :
    Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)≤2 := by
  classical
  let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
  let K:=NormalBranch.K D g.val
  obtain ⟨hblock,hB,hF⟩:=SourceSixBlock.source13_5_15_four d h e hseed hn hU
  let := hblock.2.1.elementary
  let eV:=SourceSixBlock.layerEquiv d hB
  let f:=SourceSixBlock.actor d
  let ρ:=alternatingNaturalRepresentation (Fin 6)
  let α:C→*MulAut D.L:=D.L.normalizerMonoidHom.comp
    (inclusion (inf_le_left.trans d.normalizes_L))
  have hCQ : C≤D.LT.pCoreIn 2 := by
    intro c hc
    exact h.sylow_centralizer.le ⟨hc.1,centralizer_le (hS ▸ pCoreIn_le 2 K) hc.2⟩
  have hdcore (c:C) (x:D.L) : α c x*x⁻¹∈pCore 2 D.L := by
    have hh:⁅(c:G),(x:G)⁆∈D.L.pCoreIn 2 := by
      rw [←commutatorElement_inv]
      exact (D.L.pCoreIn 2).inv_mem (local_core_commutator d
        (commutator_mem_commutator x.property (hCQ c.property)))
    obtain ⟨z,hz,he⟩:=hh
    exact (Subtype.ext he : z=α c x*x⁻¹) ▸ hz
  have hd (c:C) (x:D.L) : α c x*x⁻¹∈blockU D.L := by
    have he:=DFunLike.congr_fun (hblock.2.1.quotient_blockU_aut_eq_one (α c) (hdcore c))
      (QuotientGroup.mk' (blockU D.L) x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  have hfix (c:C) (u:D.L) (hu:u∈blockU D.L) : α c u=u := by
    apply Subtype.ext
    change (c:G)*(u:G)*(c:G)⁻¹=(u:G)
    have huV : (u:G)∈D.V := hB ▸ mem_map_of_mem D.L.subtype hu
    have hc := c.property.2 (u:G) ((hS ▸ pCoreIn_le 2 K) huV)
    rw [←hc,mul_inv_cancel_right]
  have hz : blockU D.L⊓center D.L=⊥ := by
    rw [←blockFixed_map,hF,Subgroup.map_bot]
  have hcorefix (c:C) (u:D.L) (hu:u∈f.ker) : α c u=u := by
    have hh:=Representation.OneCohomology.automorphism_fixes_centralizing_layer
      (blockU D.L) (pCore 2 D.L) hblock.2.1.core_centralizes_blockU le_rfl hz
      (α c) (hd c) (hfix c)
    apply hh u
    simpa only [f,SourceSixBlock.actor_ker d e] using hu
  have hco (c:C) : ∃z:Representation.OneCohomology.cocycles ρ,
      ∀x:D.L,z.val (f x)=(eV ⟨α c x*x⁻¹,hd c x⟩).toAdd :=
    Representation.OneCohomology.exists_automorphism_cocycle_of_subkernel
      (blockU D.L) f (SourceSixBlock.actor_surjective d) eV ρ
      (layer_equivariant d hB) (α c) (hd c) (hcorefix c)
  choose z hzeval using hco
  have hz0 (c:C) (s:alternatingGroup (Fin 6)) (hs:s.val (a.val 5)=a.val 5) : (z c).val s=0 := by
    have him : s.val∈FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
      refine ⟨(a⁻¹*s*a).val,⟨?_,(a⁻¹*s*a).property⟩,?_⟩
      · change a.val.symm (s.val (a.val 5))=5
        rw [hs,a.val.symm_apply_apply]
      · change a.val*(a.val⁻¹*s.val*a.val)*a.val⁻¹=s.val
        group
    rw [←hi] at him
    obtain ⟨k,hk,hke⟩:=him
    have hfk : f k=s := Subtype.ext hke
    rw [←hfk,hzeval]
    have hαk : α c k=k := by
      apply Subtype.ext
      change (c:G)*(k:G)*(c:G)⁻¹=(k:G)
      rw [←c.property.2 (k:G) hk,mul_inv_cancel_right]
    have hn1 : (⟨α c k*k⁻¹,hd c k⟩:blockU D.L)=1 :=
      Subtype.ext (show α c k*k⁻¹=(1:D.L) by rw [hαk,mul_inv_cancel])
    rw [hn1,map_one]
    rfl
  have hc (c:C) : ∃b:ZMod 2,z c=b • naturalCoordinateCocycle (Fin 6) (a.val 5) :=
    alternatingNatural_normalized_eq_coordinate 6 (Or.inl rfl) (a.val 5) (z c) (hz0 c)
  choose b hb using hc
  have hαinj : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply bot_unique
    intro c hc
    have hm : inclusion (inf_le_left.trans d.normalizes_L) c∈D.L.normalizerMonoidHom.ker:=hc
    rw [normalizerMonoidHom_ker] at hm
    have hh : (c:G)∈(D.T:Subgroup G)⊓centralizer (D.L:Set G):=⟨c.property.1,hm⟩
    rw [hcentral] at hh
    exact Subtype.ext hh
  have hinj : Function.Injective b := by
    intro c t hct
    apply hαinj
    apply MulEquiv.ext
    intro x
    have he : z c=z t := by rw [hb,hb,hct]
    have hh:=congrArg (fun w:Representation.OneCohomology.cocycles ρ=>w.val (f x)) he
    rw [hzeval,hzeval] at hh
    exact mul_right_cancel (congrArg Subtype.val (eV.injective (Multiplicative.toAdd.injective hh)))
  have hcard:=Nat.card_le_card_of_injective b hinj
  simpa only [Nat.card_zmod] using hcard

/-- The original public interface, using the earlier maximality theorem. -/
theorem pair_centralizer_card_le_two (g : D.L) (_hK : NormalBranch.K D g.val≤D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)≤2 :=
  pair_centralizer_card_le_two_of_centralizer_eq_bot d h e hseed hn hU g _hK a hi hS
    (SourcePairCentralizer.sylow_local_centralizer_eq_bot d h e hseed hn hU hmax)

/-- The literal pair bound from the original F.9 hypotheses alone. -/
theorem pair_centralizer_card_le_two_source (g : D.L) (hK : NormalBranch.K D g.val≤D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)≤2 :=
  pair_centralizer_card_le_two_of_centralizer_eq_bot d h e hseed hn hU g hK a hi hS
    (SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU)

/-- The original pair splits the actual core, whose remaining factor is
trivial or has order two and accounts for its full relative index. -/
theorem exists_original_core_dichotomy_of_centralizer_eq_bot
    (hcentral : (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥) :
    ∃g:D.L,g.val∉D.Gz ∧
      NormalBranch.K D g.val≤D.L ∧ D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
      D.LT.pCoreIn 2=D.V⊔C ∧ Disjoint D.V C ∧
      D.V.relIndex (D.LT.pCoreIn 2)=Nat.card C ∧
      (C=⊥ ∨ Nat.card C=2) := by
  obtain ⟨a,g,hg,_,hK,hL,hp,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
  have he := SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hz := SourceCoreSplit.module_inf_pair_centralizer d h g hK a hi hc
  have hdis : Disjoint D.V C := by
    apply disjoint_iff.mpr
    apply bot_unique
    exact (inf_le_inf_left _ inf_le_right).trans hz.le
  have hcard := pair_centralizer_card_le_two_of_centralizer_eq_bot
    d h e hseed hn hU g hK a hi hS hcentral
  change Nat.card C≤2 at hcard
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint D.V C
    (inf_le_left.trans h.T_normalizes_V : C≤normalizer (D.V:Set G)) hdis
  have hVQ : D.V≤D.LT.pCoreIn 2 := he ▸ le_sup_left
  have hiQ := relIndex_mul_card_of_le hVQ
  have hV : Nat.card D.V=16 := ReturningPlane.module_card d
  have hQ : Nat.card (D.LT.pCoreIn 2)=16*Nat.card C := by
    calc
      Nat.card (D.LT.pCoreIn 2)=Nat.card (D.V⊔C:Subgroup G) := by rw [he]
      _=Nat.card D.V*Nat.card C := hprod
      _=16*Nat.card C := by rw [hV]
  have hidx : D.V.relIndex (D.LT.pCoreIn 2)=Nat.card C := by
    rw [hQ,hV] at hiQ
    omega
  refine ⟨g,hg,hK,hL,hB,he,hdis,hidx,?_⟩
  have hpos : 0<Nat.card C := Nat.card_pos
  rcases (show Nat.card C=1 ∨ Nat.card C=2 by omega) with h1|h2
  · exact Or.inl (card_eq_one.mp h1)
  · exact Or.inr h2

/-- The previous public dichotomy interface, with its original hypothesis. -/
theorem exists_original_core_dichotomy
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    ∃g:D.L,g.val∉D.Gz ∧
      NormalBranch.K D g.val≤D.L ∧ D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
      D.LT.pCoreIn 2=D.V⊔C ∧ Disjoint D.V C ∧
      D.V.relIndex (D.LT.pCoreIn 2)=Nat.card C ∧
      (C=⊥ ∨ Nat.card C=2) :=
  exists_original_core_dichotomy_of_centralizer_eq_bot d h e hseed hn hU
    (SourcePairCentralizer.sylow_local_centralizer_eq_bot d h e hseed hn hU hmax)

/-- The actual original core dichotomy, without an extra maximality premise. -/
theorem exists_original_core_dichotomy_source :
    ∃g:D.L,g.val∉D.Gz ∧
      NormalBranch.K D g.val≤D.L ∧ D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
      D.LT.pCoreIn 2=D.V⊔C ∧ Disjoint D.V C ∧
      D.V.relIndex (D.LT.pCoreIn 2)=Nat.card C ∧
      (C=⊥ ∨ Nat.card C=2) :=
  exists_original_core_dichotomy_of_centralizer_eq_bot d h e hseed hn hU
    (SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizerBound
end

