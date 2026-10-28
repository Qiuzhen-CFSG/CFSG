module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianMultiplicity
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic

/-!
# The original constituent quotient and its single component

The marked constituent's actor kernel is its centralizer of the normal
component orbit. Identify the actual quotient actor with the literal image
inside the constituent action quotient, preserving the projection. The
proved kernel size and multiplicity give the sharp G.9 degree bound even
when the original actor is not faithful. Descending the original cover and
component orbit then excludes a two-component image; faithful restriction
lifts this equality to the original terminal group.

The quotient adapters adapt ChapterG/Section09/ActionQuotient and the
independent adapters in Chapter14/Section04/CaseOneLarge/FixedLineConstituent.
Source: Aschbacher--Smith G.11.7--8, printed pp.366--369, and 12.9.4,
printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
namespace FixedLineConstituent
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
/-- The actual quotient actor is X/C_X(H). Its equivalence to the image
preserves every original actor projection into the constituent quotient. -/
theorem actor_quotient_marking
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) D A) (H X : Subgroup D)
    [H.Normal] [IsElementaryAbelian 2 X]
    (I : Submodule (ZMod 2) A) (hI : IsIrrPlus ρ H I)
    (hXI : X ≤ subspaceStabilizer ρ I)
    (hfH : Function.Injective (invariantSubspace ρ H I hI.choose).toRepresentation) :
    let Y := (centralizer (H : Set D)).subgroupOf X
    let σ := constituentAction ρ H X I hI.choose hXI
    let q := QuotientGroup.mk' σ.ker
    let Xbar := (X.subgroupOf (H ⊔ X)).map q
    ∃ e : (X ⧸ Y) ≃* Xbar, ∀ a : X,
      (e (QuotientGroup.mk' Y a) : (H ⊔ X : Subgroup D) ⧸ σ.ker) =
        q ⟨a,(show X ≤ H ⊔ X from le_sup_right) a.property⟩ := by
  intro Y σ q Xbar
  let eX := subgroupOfEquivOfLe (show X ≤ H ⊔ X from le_sup_right)
  let f : X →* Xbar := (q.subgroupMap (X.subgroupOf (H ⊔ X))).comp eX.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp eX.symm.surjective
  have hk := constituent_kernel_eq_centralizer ρ H X I hI hXI hfH
  have hker : f.ker = Y := by
    ext a
    change f a = 1 ↔ (a : D) ∈ centralizer (H : Set D)
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk ⟨a,(show X ≤ H ⊔ X from le_sup_right) a.property⟩ :
      (H ⊔ X : Subgroup D) ⧸ σ.ker) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change a ∈ (invariantSubspace ρ X I hXI).toRepresentation.ker ↔ _
    rw [hk]
    rfl
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e,fun _ => rfl⟩

/-- G.9 on the literal constituent image with the actor rank measured after
its actual centralizer kernel. No faithfulness of the original actor is needed. -/
theorem component_input_of_quotient_degree
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hns : ¬ Group.IsSolvable D)
    (cover : SQTKCover KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {J : Subgroup D} (hJ : IsComponent D J) (hm : ⁅J,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) A} (hI : IsIrrPlus ρ (componentOrbit J ⊤) I)
    (hv : v ∈ I) (hXI : X ≤ subspaceStabilizer ρ I)
    (hd : finrank (ZMod 2) I ≤
      finrank (ZMod 2) (Additive (X ⧸ (centralizer (componentOrbit J ⊤ : Set D)).subgroupOf X)) + 2) :
    let H := componentOrbit J ⊤
    let Y := (centralizer (H : Set D)).subgroupOf X
    let σ := constituentAction ρ H X I hI.choose hXI
    let q := QuotientGroup.mk' σ.ker
    ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      ((X.subgroupOf (H ⊔ X)).map q) ((J.subgroupOf (H ⊔ X)).map q)
      ((H.subgroupOf (H ⊔ X)).map q) (finrank (ZMod 2) (Additive (X ⧸ Y))) := by
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let Y := (centralizer (H : Set D)).subgroupOf X
  change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 at hd
  have hi := hI.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hns) H
  have hind := cover.component_normalizer_index_le_two hJ
  obtain ⟨_,hfaith,_,_⟩ :=
    h.constituent_homogeneous_faithful_selfDual_of_point_mem hns hJ hm S hnX hind hI hv
  have hsame := h.constituent_sameModule_of_point_mem hns hJ hm S hnX hind hI hv
  refine componentHypothesis_constituent_image ρ ⟨cover⟩ X J H I hI.choose hXI hfaith hi
    (finrank (ZMod 2) (Additive (X ⧸ Y))) ?_ (by omega) hJ hm (le_componentOrbit J ⊤) ?_
  · obtain ⟨e,_⟩ := actor_quotient_marking ρ H X I hI hXI hfaith
    rw [← Nat.card_congr e.toEquiv]
    change Nat.card (Additive (X ⧸ Y)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  · rcases orbit_pair J hind with he | ⟨a,he⟩
    · exact Or.inl he
    have h₂H : J.map (MulAut.conj a).toMonoidHom ≤ H := by
      rw [show H = J ⊔ J.map (MulAut.conj a).toMonoidHom from he]
      exact le_sup_right
    exact Or.inr ⟨_,h₂H,hJ.map_equiv (MulAut.conj a),he,
      constituent_quasiequivalent_conjugate ρ H I hI.choose hi hsame J
        (le_componentOrbit J ⊤) a _ _⟩

/-- The sharp degree bound identifies the normal component orbit with its
original component, by lifting equality through the faithful H-restriction. -/
theorem orbit_eq_of_quotient_degree
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hns : ¬ Group.IsSolvable D)
    (cover : SQTKCover KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {J : Subgroup D} (hJ : IsComponent D J) (hm : ⁅J,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) A} (hI : IsIrrPlus ρ (componentOrbit J ⊤) I)
    (hv : v ∈ I) (hXI : X ≤ subspaceStabilizer ρ I)
    (hd : finrank (ZMod 2) I ≤
      finrank (ZMod 2) (Additive (X ⧸ (centralizer (componentOrbit J ⊤ : Set D)).subgroupOf X)) + 2) :
    componentOrbit J ⊤ = J := by
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let P := H ⊔ X
  let σ := constituentAction ρ H X I hI.choose hXI
  let q := QuotientGroup.mk' σ.ker
  have h9 := component_input_of_quotient_degree h hns cover S hnX hJ hm hI hv hXI hd
  have he : (H.subgroupOf P).map q = (J.subgroupOf P).map q :=
    TwoComponents.single_component_of_sharp_degree h9 hd
  have hf := (h.constituent_homogeneous_faithful_selfDual_of_point_mem
    hns hJ hm S hnX (cover.component_normalizer_index_le_two hJ) hI hv).2.1
  apply le_antisymm ?_ (le_componentOrbit J ⊤)
  intro a ha
  have hqa : q ⟨a,(show H ≤ P from le_sup_left) ha⟩ ∈ (H.subgroupOf P).map q :=
    mem_map.mpr ⟨_,ha,rfl⟩
  rw [he] at hqa
  obtain ⟨b,hb,hba⟩ := mem_map.mp hqa
  have hab : (⟨(b : D),(le_componentOrbit J ⊤) hb⟩ : H) = ⟨a,ha⟩ := by
    apply hf
    exact congrArg (kerRepresentation σ) hba
  have hba : (b : D) = a := congrArg (fun z : H => (z : D)) hab
  change (b : D) ∈ J at hb
  simpa only [hba] using hb

end FixedLineConstituent
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The single normal component and literal sharp constituent action quotient.
The actor rank is that of X/C_X(H), not the rank before restriction. -/
@[expose] def FixedLineConstituent.SingleData
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (J : Subgroup F.TerminalHdot) (I : Submodule (ZMod 2) (Additive F.Uhat))
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit J ⊤) I)
    (v : Additive F.Uhat) : Prop :=
  ∃ hv : v ∈ I, componentOrbit J ⊤ = J ∧ J.Normal ∧
    ∃ hXI : F.terminalDot (F.X g) ≤ subspaceStabilizer F.terminalRepresentation I,
    let H := componentOrbit J ⊤
    let X := F.terminalDot (F.X g)
    let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
    let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H X I hI.choose hXI
    let q := QuotientGroup.mk' σ.ker
    let Xbar := (X.subgroupOf (H ⊔ X)).map q
    let Hbar := (H.subgroupOf (H ⊔ X)).map q
    (∃ e : (X ⧸ Y) ≃* Xbar, ∀ a : X,
      (e (QuotientGroup.mk' Y a) : (H ⊔ X : Subgroup F.TerminalHdot) ⧸ σ.ker) =
        q ⟨a,(show X ≤ H ⊔ X from le_sup_right) a.property⟩) ∧
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      Xbar Hbar Hbar (finrank (ZMod 2) (Additive (X ⧸ Y))) ∧
    finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 ∧
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) ∧
    fixedSpace (kerRepresentation σ) Xbar = Submodule.span (ZMod 2) {(⟨v,hv⟩ : I)}

/-- The original marked branch has a single normal component even when its
actor is nonfaithful on the constituent. Its image has the original fixed
line and self-duality, with no extra quotient or degree premise. -/
theorem nonabelian_marked_constituent_single
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI) :
    FixedLineConstituent.SingleData F g J I hI.isIrrPlus v := by
  have hdouble := nonabelian_marked_constituent_double modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  obtain ⟨hv,_,_,hf,_,_,_,_,hXI,_,_,_,hs,hfix,_⟩ := hdata
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
  let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H X I hI.invariant hXI
  let q := QuotientGroup.mk' σ.ker
  have hd : finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 := by
    rcases hdouble.2.2.2 with ⟨_,hd⟩ | ⟨_,hd⟩
    · change finrank (ZMod 2) I = finrank (ZMod 2) (Additive (X ⧸ Y)) + 1 at hd
      omega
    · change finrank (ZMod 2) I = finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 at hd
      omega
  obtain ⟨S,_,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  have hns := nonabelian_hat_not_solvable h hn F hne
  have cover := nonabelian_sqtkCover h F
  have he := FixedLineConstituent.orbit_eq_of_quotient_degree hg10 hns cover S hnX
    hJ hm hI.isIrrPlus hv hXI hd
  have hnJ : J.Normal := he ▸ componentOrbit_top_normal J
  have h9 := FixedLineConstituent.component_input_of_quotient_degree hg10 hns cover S hnX
    hJ hm hI.isIrrPlus hv hXI hd
  have himage : (J.subgroupOf (H ⊔ X)).map q = (H.subgroupOf (H ⊔ X)).map q :=
    congrArg (fun N : Subgroup F.TerminalHdot => (N.subgroupOf (H ⊔ X)).map q) he.symm
  dsimp only at h9
  rw [himage] at h9
  exact ⟨hv,he,hnJ,hXI,FixedLineConstituent.actor_quotient_marking
    F.terminalRepresentation H X I hI.isIrrPlus hXI hf,h9,hd,hs,hfix⟩

/-- The proper A₆ constituent is impossible even with a nonfaithful actor.
The literal quotient rank bounds its degree by five; its degree spectrum
and the proved multiplicity give doubled natural coordinates, contradicting
the original factor of seven. -/
theorem nonabelian_marked_six_constituent_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI)
    (e : componentOrbit J ⊤ ≃* alternatingGroup (Fin 6)) : False := by
  have hdouble := nonabelian_marked_constituent_double modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  have hsingle := nonabelian_marked_constituent_single modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  obtain ⟨hv,_,_,hfH,_,_,_,_,hXI,_,_,eH,_,_,_⟩ := hdata
  obtain ⟨_,_,_,_,_,h9,hd,_,_⟩ := hsingle
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let R := invariantSubspace F.terminalRepresentation H I hI.invariant
  obtain ⟨eH,_⟩ := eH
  have hactor := ChapterG.Section09.DefiningCharacteristic.single_component_actor_rank_le h9 le_rfl
  rw [primeRank_equiv 2 (MulAut.congr (eH.symm.trans e))] at hactor
  have hrank := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hup : finrank (ZMod 2) I ≤ 5 := by omega
  let τ := R.toRepresentation.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective _).mpr
      (hI.isIrrPlus.irreducible_of_normal_restriction F.terminalRepresentation
        (hg10.irreducible_of_not_solvable (nonabelian_hat_not_solvable h hn F hne)) H)
  have hτ : Function.Injective τ := hfH.comp e.symm.injective
  have hspectrum := BinaryAlternatingSix.alternating_degrees τ
  change finrank (ZMod 2) I = 1 ∨ finrank (ZMod 2) I = 4 ∨ finrank (ZMod 2) I = 16 at hspectrum
  let : Group.IsPerfect H := hJ.orbit_isPerfect ⊤
  have hlo := hI.isIrrPlus.finrank_gt_two F.terminalRepresentation H
  have hI4 : finrank (ZMod 2) I = 4 := by
    rcases hspectrum with ht | ht | ht <;> omega
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace τ hτ hI4
  let c := a.linearEquiv
  have hc (k : H) (w : I) : c (R.toRepresentation k w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6) ((e.trans a.groupEquiv) k) (c w) := by
    have he := a.intertwines (e k) w
    simpa only [τ,ChapterB.QuasisimpleSource.alternatingNatural,
      MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply] using he
  obtain ⟨d⟩ := hdouble.2.1
  apply nonabelian_doubled_six_impossible h hn F hne H
  refine ⟨e.trans a.groupEquiv,d.toLinearEquiv.trans (c.prodCongr c),?_⟩
  intro k w
  have hd := LinearMap.congr_fun (d.isIntertwining' k) w
  change d (F.terminalRepresentation k w) = (R.toRepresentation k (d w).1,R.toRepresentation k (d w).2) at hd
  change (c (d (F.terminalRepresentation k w)).1,c (d (F.terminalRepresentation k w)).2) = _
  rw [hd]
  exact Prod.ext (hc k (d w).1) (hc k (d w).2)

/-- The source-selected constituent is exchanged, or proper and doubled
with one normal component and the literal sharp G.9 quotient. Both source
degrees and all original ambient hypotheses are retained. -/
theorem nonabelian_fixed_line_single_or_exchanged
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
          ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
          ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
            (F.terminalDot (F.X g)) I,
          (FixedLineConstituent.MarkedData F.terminalRepresentation B v
              (F.terminalDot (F.X g)) J I hI ∧
            FixedLineConstituent.DoubleData F g J I hI.isIrrPlus ∧
            FixedLineConstituent.SingleData F g J I hI.isIrrPlus v ∧
            ¬ Nonempty (componentOrbit J ⊤ ≃* alternatingGroup (Fin 6))) ∨
          (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
            F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I) := by
  obtain ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,hmarked | hex⟩ :=
    nonabelian_fixed_line_constituents_double modules h hn preferred earlier four F hne g hgP hgH
  · let := hX
    exact ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,Or.inl ⟨hmarked.1,hmarked.2.1,
      nonabelian_marked_constituent_single modules h hn preferred earlier four F hne g hgP hgH
        hg10 hS hJ hm hI hmarked.1,fun ⟨e⟩ =>
          nonabelian_marked_six_constituent_impossible modules h hn preferred earlier four
            F hne g hgP hgH hg10 hS hJ hm hI hmarked.1 e⟩⟩
  · exact ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,Or.inr hex⟩
end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
