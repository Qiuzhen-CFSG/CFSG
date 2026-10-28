module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.HigherMultiplicity
public import CFSG.Quasithin.ChapterG.Section10.Components.ActionImage
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry

/-!
# The original fixed-line constituent quotient has one component

Pass the original actor to its action on the marked irreducible constituent.
Its kernel is exactly the centralizer of the normal component orbit. The
proved two-copy multiplicity makes the nontrivial kernel have order two;
with a trivial kernel the degree bound is stronger. Thus the constituent
has degree at most the quotient actor rank plus two in both cases.

The actual one- or two-component orbit, its homogeneous constituent action
and the original SQTK cover descend through this same quotient. The sharp
G.9 theorem excludes two distinct components, and faithfulness lifts the
resulting equality back to the original terminal group. The last consumer
retains the fixed line and self-duality on this single-component quotient.
No recognition or catalogue assumption is introduced.

Source: Aschbacher--Smith G.11.6--8 and 14.4.2, printed pp.365--369,1006--1007;
refs/quasithin.pdf. The quotient adapters specialize the constructions in
ChapterG/Section09/ActionQuotient and ConstituentAction to a nonfaithful actor.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open ChapterG.Section09
universe u v
section Quotient
variable {G Q : Type u} [Group G] [Group Q] [Finite G] [Finite Q]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem faithful_le {ρ : Representation (ZMod 2) G V} {L H : Subgroup G}
    (hH : Function.Injective (ρ.comp H.subtype)) (hLH : L ≤ H) :
    Function.Injective (ρ.comp L.subtype) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : H => (z : G)) (hH (a₁ :=  ⟨a,hLH a.2⟩) (a₂ :=  ⟨b,hLH b.2⟩) hab))

omit [Finite G] in
private theorem componentHypothesis_image {K : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) Q V)
    (f : G →* Q) (hf : Function.Surjective f) (he : σ.comp f = ρ)
    (hs : Function.Injective σ) (cover : Nonempty (SQTKCover K G))
    (A L H : Subgroup G) (m : ℕ) [IsElementaryAbelian 2 A]
    (hH : Function.Injective (ρ.comp H.subtype))
    (ha : Nat.card (A.map f) = 2^m) (hd : Module.finrank (ZMod 2) V ≤ 2*(m+1))
    (hL : IsComponent G L) (hm : ⁅L,A⁆ ≠ ⊥) [H.Normal]
    (hi : IsIrreducible (ρ.comp H.subtype))
    (hc : H = L ∨ ∃ L₂ : Subgroup G, IsComponent G L₂ ∧ H = L ⊔ L₂ ∧
      Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype)) :
    ComponentHypothesis K σ (A.map f) (L.map f) (H.map f) m := by
  have hLH : L ≤ H := by
    rcases hc with h | ⟨L₂,_,h,_⟩
    · exact h.symm.le
    · rw [h]; exact le_sup_left
  have hLf := faithful_le hH hLH
  let eL := actionImageEquiv ρ σ f he L hLf
  have hL0 : L.map f ≠ ⊥ := by
    intro hz
    have hone : ∀ l : L, l = 1 := by
      intro l
      apply eL.injective
      apply Subtype.ext
      have hh := (eL l).2
      have hh0 := hz.le hh
      simpa using hh0
    have hbot : L = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro l hl
      exact congrArg Subtype.val (hone ⟨l,hl⟩)
    exact hm (by simp [hbot])
  refine { faithful := hs
           elementary := IsElementaryAbelian.map f
           card_actor := ?_
           degree_le := hd
           quotient := ?_
           component := (hL.map_surjective f hf).resolve_left hL0
           noncentral := ?_
           normal_H := Subgroup.Normal.map inferInstance f hf
           irreducible := ?_
           components := ?_ }
  · exact ha
  · exact cover.map (fun c => c.map f hf)
  · intro hz
    apply hm
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hxH : x ∈ H := ((commutator_mono hLH le_rfl).trans (commutator_le_left H A)) hx
    have hfx : f x = 1 := by
      have : f x ∈ (⁅L,A⁆).map f := mem_map.mpr ⟨x,hx,rfl⟩
      rw [map_commutator,hz] at this
      exact this
    have hinj := (actionImageEquiv ρ σ f he H hH).injective
    exact congrArg Subtype.val (hinj (a₁ :=  ⟨x,hxH⟩) (a₂ :=  1) (Subtype.ext (by simpa using hfx)))
  · apply (irreducible_comp_surjective_iff (f.subgroupMap H) (f.subgroupMap_surjective H)
      (σ.comp (H.map f).subtype)).mp
    convert hi using 1
    apply MonoidHom.ext
    intro h
    exact congrArg (fun r : Representation (ZMod 2) G V => r (h : G)) he
  · rcases hc with h | ⟨L₂,h₂,h,q⟩
    · exact Or.inl (congrArg (map f) h)
    have h₂H : L₂ ≤ H := by rw [h]; exact le_sup_right
    have h₂f := faithful_le hH h₂H
    let e₂ := actionImageEquiv ρ σ f he L₂ h₂f
    have h₂0 : L₂.map f ≠ ⊥ := by
      intro hz
      have hbot : L₂ = ⊥ := by
        apply _root_.eq_bot_iff.mpr
        intro l hl
        exact congrArg Subtype.val (e₂.injective (a₁ :=  ⟨l,hl⟩) (a₂ :=  1)
          (Subtype.ext (by
            have hh := (e₂ ⟨l,hl⟩).2
            have hh0 := hz.le hh
            simpa using hh0)))
      let := h₂.2
      let : IsSimpleGroup (L₂ ⧸ center L₂) := IsQuasisimple.simple
      let : Nontrivial L₂ := (QuotientGroup.mk'_surjective (center L₂)).nontrivial
      exact (nontrivial_iff_ne_bot L₂).mp inferInstance hbot
    refine Or.inr ⟨_,(h₂.map_surjective f hf).resolve_left h₂0,?_,Or.inl ?_⟩
    · rw [h,Subgroup.map_sup]
    obtain ⟨e,t,ht⟩ := q
    refine ⟨eL.symm.trans (e.trans e₂),t,?_⟩
    intro l w
    obtain ⟨a,rfl⟩ := eL.surjective l
    simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    change t (σ (f (a : G)) w) = σ (f (e a : G)) (t w)
    have hx (x : G) : σ (f x) = ρ x := congrArg (fun r : Representation (ZMod 2) G V => r x) he
    rw [hx,hx]
    exact ht a w

end Quotient
section Constituent
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem componentHypothesis_constituent_image {K : GroupClass.{u}}
 (ρ : Representation (ZMod 2) G V) (cover : Nonempty (SQTKCover K G))
 (A L H : Subgroup G) [H.Normal] [IsElementaryAbelian 2 A]
 (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
 (hA : A ≤ subspaceStabilizer ρ I)
 (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
 (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
 (m : ℕ) (ha : Nat.card ((A.subgroupOf (H ⊔ A)).map
   (QuotientGroup.mk' (constituentAction ρ H A I hH hA).ker)) = 2^m) (hd : Module.finrank (ZMod 2) I ≤ 2*(m+1))
 (hL : IsComponent G L) (hm : ⁅L,A⁆ ≠ ⊥) (hLH : L ≤ H)
 (hc : H = L ∨ ∃ L₂ : Subgroup G, ∃ h₂H : L₂ ≤ H,
   IsComponent G L₂ ∧ H = L ⊔ L₂ ∧
   Quasiequivalent (invariantSubspace ρ L I (hLH.trans hH)).toRepresentation
     (invariantSubspace ρ L₂ I (h₂H.trans hH)).toRepresentation) :
 let P := H ⊔ A
 let σ := constituentAction ρ H A I hH hA
 let q := QuotientGroup.mk' σ.ker
 ComponentHypothesis K (kerRepresentation σ) ((A.subgroupOf P).map q)
   ((L.subgroupOf P).map q) ((H.subgroupOf P).map q) m := by
  let P := H ⊔ A
  let σ := constituentAction ρ H A I hH hA
  let q := QuotientGroup.mk' σ.ker
  let eH := subgroupOfEquivOfLe (show H ≤ P from le_sup_left)
  let eA := subgroupOfEquivOfLe (show A ≤ P from le_sup_right)
  have hHP : H ≤ P := le_sup_left
  have hAP : A ≤ P := le_sup_right
  have hLP : L ≤ P := hLH.trans hHP
  have hh : σ.comp (H.subgroupOf P).subtype =
      (invariantSubspace ρ H I hH).toRepresentation.comp eH.toMonoidHom := rfl
  have ha' : σ.comp (A.subgroupOf P).subtype =
      (invariantSubspace ρ A I hA).toRepresentation.comp eA.toMonoidHom := rfl
  have hσH : Function.Injective (σ.comp (H.subgroupOf P).subtype) := by
    rw [hh]; exact hfH.comp eH.injective
  have hi' : IsIrreducible (σ.comp (H.subgroupOf P).subtype) := by
    rw [hh]
    exact (irreducible_comp_surjective_iff eH.toMonoidHom eH.surjective _).mpr hi
  have hm' : ⁅L.subgroupOf P,A.subgroupOf P⁆ ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map P.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hLP,map_subgroupOf_eq_of_le hAP,Subgroup.map_bot] at he
    exact hm he
  have hc' : H.subgroupOf P = L.subgroupOf P ∨ ∃ L₂ : Subgroup P,
      IsComponent P L₂ ∧ H.subgroupOf P = L.subgroupOf P ⊔ L₂ ∧
      Quasiequivalent (σ.comp (L.subgroupOf P).subtype) (σ.comp L₂.subtype) := by
    rcases hc with h | ⟨L₂,h₂H,h₂,h,qv⟩
    · exact Or.inl (congrArg (fun J : Subgroup G => J.subgroupOf P) h)
    have h₂P := h₂H.trans hHP
    refine Or.inr ⟨L₂.subgroupOf P,h₂.subgroupOf h₂P,?_,?_⟩
    · rw [h,subgroupOf_sup hLP h₂P]
    obtain ⟨e,t,ht⟩ := qv
    let eL := subgroupOfEquivOfLe hLP
    let e₂ := subgroupOfEquivOfLe h₂P
    refine ⟨eL.trans (e.trans e₂.symm),t,?_⟩
    intro l w
    exact ht (eL l) w
  let : IsElementaryAbelian 2 (A.subgroupOf P) := IsElementaryAbelian.subgroupOf hAP
  exact componentHypothesis_image σ (kerRepresentation σ) q
    (QuotientGroup.mk'_surjective _) rfl (kerRepresentation_faithful σ)
    (cover.map (fun c => c.subgroup P)) (A.subgroupOf P) (L.subgroupOf P) (H.subgroupOf P) m
    hσH ha hd (hL.subgroupOf hLP) hm' hi' hc'
end Constituent
section Orbit
variable {G : Type*} [Group G] [Finite G]
private theorem orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
    componentOrbit L ⊤ = L ∨ ∃ g : G,
      componentOrbit L ⊤ = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hn : L.Normal
  · let := hn
    left
    apply le_antisymm ?_ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top_iff.mpr hn])
  have hidx : (normalizer (L : Set G)).index = 2 := by
    have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set G)).index ≠ 1 := by
      intro he
      exact hn (normalizer_eq_top_iff.mp (index_eq_one.mp he))
    omega
  have hN : normalizer (L : Set G) ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hex : ∃ g : G, g ∉ normalizer (L : Set G) := by
    by_contra! hall
    exact hN (eq_top_iff.mpr (fun g _ => hall g))
  obtain ⟨g,hg⟩ := hex
  right
  refine ⟨g,le_antisymm ?_ (sup_le (le_componentOrbit L ⊤) ?_)⟩
  · refine iSup_le fun a => ?_
    by_cases ha : (a : G) ∈ normalizer (L : Set G)
    · have he : L.map (MulAut.conj (a : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp ha
      rw [he]
      exact le_sup_left
    have hga : g⁻¹ * (a : G) ∈ normalizer (L : Set G) :=
      (mul_mem_iff_of_index_two hidx).mpr (iff_of_false (by simpa using hg) ha)
    have he : L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      calc
        _ = (L.map (MulAut.conj (g⁻¹ * (a : G))).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (map (MulAut.conj g).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hga)
    rw [he]
    exact le_sup_right
  · exact le_iSup (fun a : (⊤ : Subgroup G) => L.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨g,mem_top g⟩

end Orbit
private theorem single_input_of_image_eq
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {A C H : Subgroup D} {m : ℕ} {v : W}
    (h : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ A C H m)
    (he : H = C) (hd : finrank (ZMod 2) W ≤ m + 2)
    (hs : Nonempty (Representation.Equiv (ρ.comp H.subtype) (Representation.dual (ρ.comp H.subtype))))
    (hf : fixedSpace ρ A = Submodule.span (ZMod 2) {v}) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ A C C m ∧
      finrank (ZMod 2) W ≤ m + 2 ∧
      Nonempty (Representation.Equiv (ρ.comp C.subtype) (Representation.dual (ρ.comp C.subtype))) ∧
      fixedSpace ρ A = Submodule.span (ZMod 2) {v} := by
  subst H
  exact ⟨h,hd,hs,hf⟩

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.LocalAction.Components
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem fixed_constituent_data :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

variable (hXI : F.terminalDot (F.X g) ≤ subspaceStabilizer F.terminalRepresentation I)

private noncomputable def fixed_constituent_actor_equiv :
    ((F.terminalDot (F.X g)) ⧸
      (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) ≃*
      MarkedAction.image F.terminalRepresentation (componentOrbit C ⊤)
        (F.terminalDot (F.X g)) I hI.choose hXI (F.terminalDot (F.X g)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  let P := H ⊔ X
  let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
  let q := QuotientGroup.mk' σ.ker
  let eX : X.subgroupOf P ≃* X := subgroupOfEquivOfLe (show X ≤ P from le_sup_right)
  let f := (q.subgroupMap (X.subgroupOf P)).comp eX.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp eX.symm.surjective
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hI.irreducible_of_normal_restriction _ (hyp.irreducible_of_not_solvable hn) H
  have hfaith := (fixed_constituent_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  have hker : f.ker = (centralizer (H : Set F.TerminalHdot)).subgroupOf X := by
    ext a
    change f a = 1 ↔ (a : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot)
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk ⟨a,(show X ≤ P from le_sup_right) a.property⟩ : P ⧸ σ.ker) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change σ ⟨a,(show X ≤ P from le_sup_right) a.property⟩ = 1 ↔ _
    rw [← MarkedAction.fixes_iff_centralizes F.terminalRepresentation H X I hI.choose hXI
      hfaith hi ⟨v,hv⟩ (fun he => hyp.point_ne_zero (congrArg Subtype.val he))
      a (hyp.fixes_point a.property)]
    constructor
    · intro he w
      exact congrArg Subtype.val (LinearMap.congr_fun he w)
    · intro he
      ext w
      exact he w
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

include classification

/-- In the original fixed-line branch, the literal actor quotient has
rank at least dim(I)-2. This includes both a trivial kernel and the proved
order-two kernel, with the two-copy multiplicity discharged. -/
theorem source_large_fixed_line_constituent_degree
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    finrank (ZMod 2) I ≤
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
          (F.terminalDot (F.X g)))) + 2 := by
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf X
  by_cases hk : Y = ⊥
  · let e : X ⧸ Y ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hk).trans QuotientGroup.quotientBot
    have hc : Nat.card (X ⧸ Y) = Nat.card X := Nat.card_congr e.toEquiv
    change Nat.card (Additive (X ⧸ Y)) = Nat.card (Additive X) at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ Y)),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X),Nat.card_zmod] at hc
    have hr := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
    have hs := source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
    have hb := hyp.isotropic_degree_le_actor_rank_add_one hs
    change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive X) + 1 at hb
    change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2
    omega
  · exact (source_large_marked_nontrivial_kernel d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn hk).2.le

/-- All G.9 hypotheses hold on the actual constituent action quotient,
with actor rank computed after its literal centralizer kernel. The sharper
bound is retained for the component-pair exclusion. -/
theorem source_large_fixed_line_constituent_input
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI C)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI H)
      (finrank (ZMod 2) (Additive (X ⧸ Y))) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hI.irreducible_of_normal_restriction _ (hyp.irreducible_of_not_solvable hns) H
  obtain ⟨hh,hfaith,hsame⟩ := fixed_constituent_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hd := source_large_fixed_line_constituent_degree d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 at hd
  refine componentHypothesis_constituent_image F.terminalRepresentation (source_terminal_cover F d chosen)
    X C H I hI.choose hXI hfaith hi (finrank (ZMod 2) (Additive (X ⧸ Y)))
    ?_ (by omega) hC hm (le_componentOrbit C ⊤) ?_
  · change Nat.card (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X) = _
    rw [← Nat.card_congr (fixed_constituent_actor_equiv d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI).toEquiv]
    change Nat.card (Additive (X ⧸ Y)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  · let := chosen.elementary
    have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
    rcases orbit_pair C hind with he | ⟨a,he⟩
    · exact Or.inl he
    have h₂H : C.map (MulAut.conj a).toMonoidHom ≤ H := by
      rw [show H = C ⊔ C.map (MulAut.conj a).toMonoidHom from he]
      exact le_sup_right
    exact Or.inr ⟨_,h₂H,hC.map_equiv (MulAut.conj a),he,
      ChapterG.Section09.constituent_quasiequivalent_conjugate F.terminalRepresentation H I
        hI.choose hi hsame C (le_componentOrbit C ⊤) a _ _⟩

/-- The fixed-line branch has one actual normal component in the orbit of
every moved component possessing the marked constituent. Equality is lifted
from the faithful constituent quotient, not inferred from group orders. -/
theorem source_large_fixed_line_component_normal
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    componentOrbit C ⊤ = C ∧ C.Normal := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hc := source_large_fixed_line_constituent_input d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hd := source_large_fixed_line_constituent_degree d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hc hd
  have hf := (fixed_constituent_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  have hHC := (MarkedAction.image_eq_iff F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI hf C (le_componentOrbit C ⊤)).mp he
  exact ⟨hHC,hHC ▸ (inferInstance : H.Normal)⟩

omit classification in
private theorem fixed_constituent_selfDual_image :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    let Hbar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI H
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hns
  have hsame := (fixed_constituent_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.2
  exact MarkedAction.selfDual_image F.terminalRepresentation H (F.terminalDot (F.X g)) I hI.choose hXI
    (constituent_selfDual_of_sameModule F.terminalRepresentation H hi B hyp.preserves
      hyp.nondegenerate hI hsame)

/-- The original marked quotient satisfies the single-component G.9 input,
self-duality and the fixed-line condition in the same coordinates. -/
theorem source_large_fixed_line_single_input
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    let Cbar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI C
    let Abar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      Abar Cbar Cbar (finrank (ZMod 2) (Additive (X ⧸ Y))) ∧
      finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 ∧
      Nonempty (Representation.Equiv ((kerRepresentation σ).comp Cbar.subtype)
        (Representation.dual ((kerRepresentation σ).comp Cbar.subtype))) ∧
      fixedSpace (kerRepresentation σ) Abar = Submodule.span (ZMod 2) {(⟨v,hv⟩ : I)} := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  refine single_input_of_image_eq
    (source_large_fixed_line_constituent_input d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn)
    (congrArg (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI)
      (source_large_fixed_line_component_normal d earlier hq chosen structural alternatives
        classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1)
    (source_large_fixed_line_constituent_degree d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn)
    (fixed_constituent_selfDual_image d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI) ?_
  have hf := (source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH v hline hn).1
  rw [← hline] at hf
  exact MarkedAction.fixedSpace_image_eq_line F.terminalRepresentation H X I hI.choose hXI ⟨v,hv⟩ hf

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
