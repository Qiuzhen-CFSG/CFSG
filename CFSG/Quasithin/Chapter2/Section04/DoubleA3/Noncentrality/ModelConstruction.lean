module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.MarkedModel
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.Generators
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.ActionNormalForms
public import Theory.SpecificGroups.PSL3Two.PairedActionRecognition.Marking

/-!
# Constructing the marked paired model from the source components

The faithful action of the original component pair identifies its generated
extension with the paired PSL₃(2) model. A first-component Sylow is sent to the
Borel while retaining its central involution; conjugation by the original
exchange element retains the second mark. The Borel product then determines
the actual ambient Sylow, giving the embedding required by the source transfer
argument. The original outer and exchange generators need not be involutions.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.PairedInvolutiveExtension
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.PairedGraphInputs Matrix.PSL3Two.PairedSylowRecognition
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The actual source components and Sylow admit the standard paired model,
with both original central involutions preserved. -/
theorem source_paired_embedding
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hE : K=componentLayer (involutionCentralizer g.z₂))
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂)=⊥)
    (hfirst : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K≃*alternatingGroup (Fin 6)) ∨ Nonempty (K≃*PSL))
    (hcomm : c.U₂ ≤ centralizer (K.map (involutionCentralizer g.z₂).subtype : Set G)) :
    Nonempty (SourcePairedEmbedding g K) := by
  let A := K.map (involutionCentralizer g.z₂).subtype
  let eA : K≃*A := K.equivMapOfInjective (involutionCentralizer g.z₂).subtype Subtype.val_injective
  have hA : IsComponentIn A (involutionCentralizer g.z₂) := by
    refine ⟨map_subtype_le K,?_⟩
    have he : A.subgroupOf (involutionCentralizer g.z₂)=K :=
      comap_map_eq_self (by rw [(involutionCentralizer g.z₂).ker_subtype]; exact bot_le)
    rw [he]
    exact hK
  have hAE : A=(componentLayer (involutionCentralizer g.z₂)).map (involutionCentralizer g.z₂).subtype := by
    change K.map _ = _
    rw [hE]
  have hmodels : Nonempty (A≃*alternatingGroup (Fin 6)) ∨ Nonempty (A≃*PSL) := by
    rcases hmodel with h | h
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨eA.symm.trans e⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨eA.symm.trans e⟩
  obtain ⟨_,⟨e₀⟩,_,_⟩ := source_pair_two_rank hG hu c g A hA hAE ho hfirst hmodels hcomm
  obtain ⟨S,_,hST,z,hz,hzc,hzord⟩ :=
    source_first_sylow_mark hG hu c g A hA hAE ho hfirst hmodels hcomm
  have hzne : z≠1 := by intro he; rw [he,orderOf_one] at hzord; contradiction
  obtain ⟨eK,hSK,hzk⟩ := PairedActionRecognition.exists_sylow_center_marking e₀ S z hzc hzne
  let As := A.map (MulAut.conj c.s⁻¹).toMonoidHom
  let J := A⊔As
  let I := J⊔(T:Subgroup G)
  let eS : A≃*As := A.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom (MulAut.conj c.s⁻¹).injective
  obtain ⟨eJ,hleft,hright,hn,hρ,honJ⟩ :=
    source_pair_action_of_equiv hu c g A hA hAE ho hfirst hcomm eK
  let ρ := (MulAut.congr eJ).toMonoidHom.comp (J.normalizerMonoidHom.comp (inclusion hn))
  let xI : I := ⟨c.x,mem_sup_right c.x_mem⟩
  let sI : I := ⟨c.s,mem_sup_right (c.original.T_le c.s_mem)⟩
  let N := J.subgroupOf I
  have hNρ : N.map ρ=(MulAut.conj : SL×SL →* MulAut (SL×SL)).range := by
    apply le_antisymm
    · rintro a ⟨v,hv,rfl⟩
      let j:J := ⟨v.val,hv⟩
      exact ⟨eJ j,(honJ j).symm⟩
    · rintro a ⟨w,rfl⟩
      let j := eJ.symm w
      refine ⟨inclusion le_sup_left j,j.property,?_⟩
      rw [honJ,eJ.apply_symm_apply]
  obtain ⟨_,hsq,hspan,_,_⟩ := source_pair_generators hG hu c g A hA hAE ho hfirst hmodels hcomm
  have hgen : N⊔zpowers xI⊔zpowers sI=⊤ := by
    apply Subgroup.map_injective (show Function.Injective I.subtype from Subtype.val_injective)
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le (show J≤I from le_sup_left),
      I.subtype.map_zpowers,I.subtype.map_zpowers,←I.subtype.range_eq_map,range_subtype]
    exact hspan.symm
  have hx := source_x_action_normal_form hG hu c g A hA hAE ho hfirst hcomm eK eJ hleft hright hn
  have hs := source_s_action_swapped c g A hA eK eJ hleft hright hn
  let eI := PairedActionRecognition.equiv ρ N hNρ xI sI hgen hx hs hsq hρ
  have heJ (j:J) : eI (inclusion le_sup_left j)=base diagram diagram_involutive (eJ j).1 (eJ j).2 := by
    exact PairedActionRecognition.equiv_eq_base ρ N hNρ xI sI hgen hx hs hsq hρ
      (inclusion le_sup_left j) (eJ j).1 (eJ j).2 (honJ j)
  have hleftI (a:A) : eI (⟨a.val,mem_sup_left (mem_sup_left a.property)⟩:I)=
      base diagram diagram_involutive (eK a) 1 := by
    calc
      _ = eI (inclusion le_sup_left (inclusion le_sup_left a)) :=
        congrArg eI (Subtype.ext rfl)
      _ = _ := heJ (inclusion le_sup_left a)
      _ = _ := by rw [hleft]
  have hrightI (a:A) : eI (⟨(eS a).val,mem_sup_left (mem_sup_right (eS a).property)⟩:I)=
      base diagram diagram_involutive 1 (eK a) := by
    have hh : eJ (inclusion le_sup_right (eS a)) = (1,eK a) := hright a
    calc
      _ = eI (inclusion le_sup_left (inclusion le_sup_right (eS a))) :=
        congrArg eI (Subtype.ext rfl)
      _ = _ := heJ (inclusion le_sup_right (eS a))
      _ = _ := by rw [hh]
  have hinvleft (a:SL) : ((eI.symm (base diagram diagram_involutive a 1):I):G)=(eK.symm a:G) := by
    have he := congrArg eI.symm (hleftI (eK.symm a))
    rw [eI.symm_apply_apply,eK.apply_symm_apply] at he
    exact congrArg Subtype.val he.symm
  have hinvright (a:SL) : ((eI.symm (base diagram diagram_involutive 1 a):I):G)=(eS (eK.symm a):G) := by
    have he := congrArg eI.symm (hrightI (eK.symm a))
    rw [eI.symm_apply_apply,eK.apply_symm_apply] at he
    exact congrArg Subtype.val he.symm
  have hTI : (T:Subgroup G)≤I := le_sup_right
  let TI := T.subtype hTI
  have hbase : standardBase ≤ (TI:Subgroup I).map eI.toMonoidHom := by
    rintro w ⟨⟨a,b⟩,hab,rfl⟩
    obtain ⟨a',ha',rfl⟩ := (hSK.symm ▸ hab.1 : a∈(S:Subgroup A).map eK.toMonoidHom)
    obtain ⟨b',hb',rfl⟩ := (hSK.symm ▸ hab.2 : b∈(S:Subgroup A).map eK.toMonoidHom)
    let u:I := ⟨a'.val,mem_sup_left (mem_sup_left a'.property)⟩
    let v:I := ⟨(eS b').val,mem_sup_left (mem_sup_right (eS b').property)⟩
    have huT : u∈(TI:Subgroup I) := hST (mem_map_of_mem A.subtype ha')
    have hvT : v∈(TI:Subgroup I) := by
      change c.s⁻¹*(b':G)*(c.s⁻¹)⁻¹∈(T:Subgroup G)
      exact (T:Subgroup G).mul_mem ((T:Subgroup G).mul_mem
        ((T:Subgroup G).inv_mem (c.original.T_le c.s_mem)) (hST (mem_map_of_mem A.subtype hb')))
        ((T:Subgroup G).inv_mem ((T:Subgroup G).inv_mem (c.original.T_le c.s_mem)))
    refine ⟨u*v,(TI:Subgroup I).mul_mem huT hvT,?_⟩
    change eI (u*v)=base diagram diagram_involutive (eK a') (eK b')
    rw [map_mul,hleftI,hrightI]
    simp [base]
  let eT : standardPaired≃*T := (PairedActionRecognition.sylowEquiv eI TI hbase).trans
    (subgroupOfEquivOfLe hTI)
  let f : StandardModel→*G := I.subtype.comp eI.symm.toMonoidHom
  refine ⟨{
    f := f
    injective := Subtype.val_injective.comp eI.symm.injective
    sylowEquiv := eT
    sylow_spec := ?_
    componentEquiv := eA.trans eK
    first_eval := ?_
    first_mark := ?_
    second_mark := ?_ }⟩
  · intro u
    exact congrArg Subtype.val (PairedActionRecognition.sylowEquiv_apply eI TI hbase u).symm
  · intro a
    change ((eI.symm (base diagram diagram_involutive a 1):I):G)=_
    rw [hinvleft]
    exact (congrArg Subtype.val (eA.apply_symm_apply (eK.symm a))).symm
  · change ((eI.symm (base diagram diagram_involutive highestRoot 1):I):G)=g.z₁
    rw [hinvleft,←hzk,eK.symm_apply_apply]
    exact hz
  · change ((eI.symm (base diagram diagram_involutive 1 highestRoot):I):G)=g.z₂
    rw [hinvright,←hzk,eK.symm_apply_apply]
    change c.s⁻¹*((z:A):G)*(c.s⁻¹)⁻¹=g.z₂
    rw [hz,←g.exchange_second]
    group
end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
