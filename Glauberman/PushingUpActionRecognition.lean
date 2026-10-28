module
public import Glauberman.PushingUpActionKernel
public import Theory.Representation.AlternatingFiveOffenderRecognition
public import Glauberman.PushingUpActionOffender
public import Theory.Representation.SL2FourQuadraticRecognition.QuotientMap
public import Theory.SpecificGroups.PSL2.AutomorphismModel
/-!
# Original Niles action-quotient recognition

Apply the offender recognition theorem to the faithful image of the original
conjugation action on V=Ω1(Z(O2(H))). The minimal-parabolic kernel reduction
proves that this image is perfect and has an odd nilpotent Frattini kernel
above the original PSL2(4) quotient. Recognition removes that kernel, identifies
the original centralizer with K, and makes the selected maximum abelian
actor's image the full original Sylow image. The existing SL2(4) quadratic
recognition then gives natural coordinates on the literal V/C_V(H).

No perfection of H or irreducibility of V is assumed; central fixed vectors
are retained until taking the specified quotient. Source: Niles, Pushing-up
in finite groups (1979), Lemmas2.8–2.9, printed pp.32–33.
-/
set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Glauberman
variable {H:Type*} [Group H] [Finite H] {F:Type*} [Field F] [Finite F]
local instance omega_centralizer_normal :
    (centralizer (omegaCenterIn (pCore 2 H):Set H)).Normal := by
  rw [←omegaAction_kernel]
  infer_instance

theorem original_psl2_four_omegaAction_kernel_eq
    (hF:Nat.card F=4) (S:Sylow 2 H)
    (hu:Order.HasUniqueMaximalOver (S:Subgroup H) ⊤)
    (K:Subgroup H) [K.Normal]
    (e:(H⧸K)≃*Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf:generalizedFitting H=pCore 2 H)
    (hno:NoCharacteristicNormal (S:Subgroup H)) :
    (omegaAction H).ker=K ∧
      ∃A:Subgroup H,A∈thompsonAbelianSubgroups (S:Subgroup H) ∧ ¬A≤K ∧
        ⁅⁅omegaCenterIn (pCore 2 H),A⁆,A⁆=⊥ ∧
        Nat.card (A.map (QuotientGroup.mk' K))=4 ∧ fixedCodim (omegaAction H) A≤2 := by
  obtain ⟨hQ,hk,hperfect,q,hs,hcomp,hker,hnil,hodd,hfr⟩ :=
    original_psl2_four_omegaAction_image_structure hF S hu K e hf hno
  let _ := hperfect
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans f
  let q5 := b.toMonoidHom.comp q
  have hq5:Function.Surjective q5 := b.surjective.comp hs
  have hqker:q5.ker=q.ker := MonoidHom.ker_comp_of_injective q b.toMonoidHom b.injective
  let _ : Group.IsNilpotent q5.ker := hqker.symm ▸ hnil
  obtain ⟨A,hA,hAK,hquad,hp,hc,hcard,hd⟩ :=
    original_psl2_four_action_offender hF S hu K e hf hno hQ hk
  have hmap : (actionSubgroup (omegaAction H) A).map q5 =
      (A.map (QuotientGroup.mk' K)).map b.toMonoidHom := by
    rw [actionSubgroup,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change b (q (actionHom (omegaAction H) a))=b (QuotientGroup.mk' K a)
    rw [hcomp]
  have hm : Nat.card ((actionSubgroup (omegaAction H) A).map q5)=
      Nat.card (actionSubgroup (omegaAction H) A) := by
    rw [hmap,card_map_of_injective b.injective]
    exact hcard.symm
  obtain ⟨hinj,hfour,hdegree⟩ := AlternatingFiveOffenderRecognition.recognize
    (imageRepresentation (omegaAction H)) (imageRepresentation_injective _)
    q5 hq5 (hqker.symm ▸ hodd) (hqker.symm ▸ hfr)
    (actionSubgroup (omegaAction H) A) hp hc hm hd
  have hK:K≤(omegaAction H).ker := by
    rw [←actionHom_ker_eq]
    apply (map_eq_bot_iff K).mp
    rw [←hker,←hqker]
    exact q5.ker_eq_bot hinj
  refine ⟨le_antisymm hk hK,A,hA,hAK,hquad,?_,?_⟩
  · exact hcard.symm.trans hfour
  · rw [fixedCodim_actionSubgroup] at hd
    simpa only [hfour,show Nat.log 2 4=2 by decide] using hd

/-- The original maximum abelian offender has the full Sylow action image. -/
theorem original_psl2_four_omegaAction_sylow
    (hF:Nat.card F=4) (S:Sylow 2 H)
    (hu:Order.HasUniqueMaximalOver (S:Subgroup H) ⊤)
    (K:Subgroup H) [K.Normal]
    (e:(H⧸K)≃*Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf:generalizedFitting H=pCore 2 H)
    (hno:NoCharacteristicNormal (S:Subgroup H)) :
    (omegaAction H).ker=K ∧ IsQuadratic (omegaAction H) (S:Subgroup H) ∧
      fixedCodim (omegaAction H) (S:Subgroup H)≤2 ∧
      ∃A:Subgroup H,A∈thompsonAbelianSubgroups (S:Subgroup H) ∧ ¬A≤K ∧
        A.map (QuotientGroup.mk' K)=(S:Subgroup H).map (QuotientGroup.mk' K) := by
  obtain ⟨hk,A,hA,hAK,hquad,hcard,hd⟩ :=
    original_psl2_four_omegaAction_kernel_eq hF S hu K e hf hno
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans f
  let q := b.toMonoidHom.comp (QuotientGroup.mk' K)
  have hs:Function.Surjective q := b.surjective.comp (QuotientGroup.mk'_surjective K)
  have hS4:Nat.card ((S:Subgroup H).map (QuotientGroup.mk' K))=4 := by
    have hh := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card (S.mapSurjective hs)
    change Nat.card ((S:Subgroup H).map q)=4 at hh
    rw [show (S:Subgroup H).map q=((S:Subgroup H).map (QuotientGroup.mk' K)).map b.toMonoidHom by
      rw [map_map]] at hh
    rw [card_map_of_injective (f:=b.toMonoidHom) b.injective] at hh
    exact hh
  have he:A.map (QuotientGroup.mk' K)=(S:Subgroup H).map (QuotientGroup.mk' K) :=
    eq_of_le_of_card_ge (map_mono hA.1) (by rw [hcard,hS4])
  have himage:actionSubgroup (omegaAction H) A=actionSubgroup (omegaAction H) (S:Subgroup H) := by
    let a := actionHom (omegaAction H)
    let c := QuotientGroup.lift K a (by rw [actionHom_ker_eq,hk])
    have hc:c.comp (QuotientGroup.mk' K)=a := by ext x; rfl
    change A.map a=(S:Subgroup H).map a
    rw [←hc,←map_map,←map_map,he]
  have hquadA := omegaAction_quadratic_of_double_commutator A hquad
  have hquadS:IsQuadratic (omegaAction H) (S:Subgroup H) := by
    have hh := quadratic_actionSubgroup (omegaAction H) hquadA
    rw [himage] at hh
    intro s hs t ht v
    exact hh (actionHom (omegaAction H) s) (mem_map_of_mem _ hs)
      (actionHom (omegaAction H) t) (mem_map_of_mem _ ht) v
  have hdim:fixedCodim (omegaAction H) (S:Subgroup H)≤2 := by
    have hh := congrArg (fixedCodim (imageRepresentation (omegaAction H))) himage
    rw [fixedCodim_actionSubgroup,fixedCodim_actionSubgroup] at hh
    exact hh ▸ hd
  exact ⟨hk,hquadS,hdim,A,hA,hAK,he⟩

/-- Source Niles2.8–2.9: the original omega-action quotient is SL2(4), and
its literal global-fixed quotient is the natural module. -/
theorem original_psl2_four_omegaAction_recognition
    (hF:Nat.card F=4) (S:Sylow 2 H)
    (hu:Order.HasUniqueMaximalOver (S:Subgroup H) ⊤)
    (K:Subgroup H) [K.Normal]
    (e:(H⧸K)≃*Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf:generalizedFitting H=pCore 2 H)
    (hno:NoCharacteristicNormal (S:Subgroup H)) :
    ∃q:H→*SL2FourNatural.SL,Function.Surjective q ∧
      q.ker=centralizer (omegaCenterIn (pCore 2 H):Set H) ∧
      (∃A:Subgroup H,A∈thompsonAbelianSubgroups (S:Subgroup H) ∧ ¬A≤K ∧
        A.map q=(S:Subgroup H).map q) ∧
      Nonempty ((H⧸centralizer (omegaCenterIn (pCore 2 H):Set H))≃*SL2FourNatural.SL) ∧
      Nat.card (Additive (omegaCenterIn (pCore 2 H))⧸fixedSpace (omegaAction H) ⊤)=16 ∧
      ∃E:(Additive (omegaCenterIn (pCore 2 H))⧸fixedSpace (omegaAction H) ⊤)≃ₗ[ZMod 2]SL2FourNatural.V,
        ∀h v,E (fixedQuotient (omegaAction H) ⊤ h v)=specialLinearNatural 2 (q h) (E v) := by
  obtain ⟨hk,hquad,hd,hA⟩ := original_psl2_four_omegaAction_sylow hF S hu K e hf hno
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨g⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K:=SL2FourNatural.F) (by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field])
  let a : (H⧸K)≃*SL2FourNatural.SL :=
    ((e.trans f).trans g.symm).trans (Theory.PSL2.sl2QuotientEquiv SL2FourNatural.F).symm
  let q := a.toMonoidHom.comp (QuotientGroup.mk' K)
  have hs:Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective K)
  have hqker:q.ker=K := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  have hn:omegaAction H≠1 := by
    intro he
    apply original_psl2_four_omegaAction_kernel_ne_top hF S hu K e hf hno
    rw [he]
    exact MonoidHom.ker_one
  obtain ⟨hker,heq,hcard,E,hE⟩ := SL2FourQuadraticRecognition.recognition_of_sylow
    (omegaAction H) q hs (by rw [hqker,←hk]) hn S hquad hd
  refine ⟨q,hs,?_,?_,?_,hcard,E,hE⟩
  · rw [←hker,omegaAction_kernel]
  · obtain ⟨A,hA,hAK,he⟩ := hA
    refine ⟨A,hA,hAK,?_⟩
    change A.map (a.toMonoidHom.comp (QuotientGroup.mk' K))=
      (S:Subgroup H).map (a.toMonoidHom.comp (QuotientGroup.mk' K))
    rw [←map_map,←map_map,he]
  · obtain ⟨z⟩ := heq
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (omegaAction_kernel H).symm).trans z⟩
end Glauberman
