module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentMathieuModule
public import Theory.Representation.BinaryOffender.ChiefCommutator
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
/-!
# The whole original Mathieu commutator

The faithful twelve-dimensional chief section exhausts the dimension bound
on the entire moved space of the component-plus-involution join. The literal
chief quotient map therefore identifies the component commutator with that
section. Transport through the actual component inclusions gives a faithful
irreducible James module inside the original action, invariant under H-star.
The original coordinate map identifies it with the image of [U_H,K].

The same marked V-star involution moves exactly the image of V₅/V₁; this
four-space lies in the component commutator. The final theorem constructs
the action on the literal U_H/V₁ quotient and retains its coordinate identity.
No splitting of the ambient quotient is assumed. The nonsingular-point
stabilizer argument, M₂₂ exclusion and universal natural reduction remain
subsequent obligations.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, using H.12.1(3),
printed pp.393–394.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative

private theorem faithful_irreducible_of_equiv
    {A U W : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A U} {τ : Representation (ZMod 2) A W}
    (e : Representation.Equiv ρ τ) (hf : Function.Injective τ) (hi : IsIrreducible τ) :
    Function.Injective ρ ∧ IsIrreducible ρ := by
  constructor
  · intro a b hab
    apply hf
    apply LinearMap.ext
    intro w
    obtain ⟨u,hu⟩ := e.toLinearEquiv.surjective w
    change e u = w at hu
    have ha := LinearMap.congr_fun (e.isIntertwining' a) u
    have hb := LinearMap.congr_fun (e.isIntertwining' b) u
    change e (ρ a u) = τ a (e u) at ha
    change e (ρ b u) = τ b (e u) at hb
    rw [hu] at ha hb
    exact ha.symm.trans ((congrArg e (LinearMap.congr_fun hab u)).trans hb)
  · let f := IntertwiningMap.equivLinearMapAsModule ρ τ e.toIntertwiningMap
    let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule τ).mp hi)

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
/-- Identify the original component commutator by its literal chief quotient
map, and retain the exact V₅ image moved by the selected V-star involution. -/
theorem SourceHypothesis.original_mathieuCover_commutator_of_binary_section
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    ∃ C : Subrepresentation σ,
      C.toSubmodule = Coinvariants.ker (σ.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      C.toSubmodule = κ.imageSpace ⁅(D.fullSetup hZ T z).UH H,c.K⁆ ∧
      Module.finrank (ZMod 2) C.toSubmodule = 12 ∧
      IsIrreducible (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      Function.Injective (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      (∃ ec : Nonabelian.Setup.star H c.K ≃* Sporadic.Mathieu.M22TripleCover,
        Nonempty (Equiv (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype)
          (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec))) ∧
      ∃ t : Nonabelian.Setup.Hstar H,
        t ∈ Nonabelian.Setup.star H V ∧ orderOf t = 2 ∧
        let X := Nonabelian.Setup.star H c.K ⊔ zpowers t
        let ρ := σ.comp X.subtype
        Coinvariants.ker ρ = C.toSubmodule ∧
        (σ t - LinearMap.id).range = κ.imageSpace (D.fullSetup hZ T z).V₅ ∧
        κ.imageSpace (D.fullSetup hZ T z).V₅ ≤ C.toSubmodule ∧
        ∃ U N : Subrepresentation ρ,
          IsIrreducible (sectionRepresentation ρ U N) ∧
          fixedCodim (sectionRepresentation ρ U N)
            (zpowers (⟨t, (le_sup_right : zpowers t ≤ X) (mem_zpowers t)⟩ : X)) = 4 ∧
          ∃ hle : C.toSubmodule ≤ N.toSubmodule,
            ∃ e : Equiv (C.toRepresentation.comp X.subtype) (sectionRepresentation ρ U N),
              ∀ v, e v = (sectionLower ρ U N).toSubmodule.mkQ (Submodule.inclusion hle v) := by
  obtain ⟨t,ht,hto,hd,U,N,hirr,hirrB,hfaith,hdim,hdisp,ec,⟨em⟩⟩ :=
    S.original_mathieuCover_chief_of_binary_section D hZ z hz hTV hTz hbound hH hn c a hm σ hσ κ
  let B := Nonabelian.Setup.star H c.K
  let : B.Normal := (S.original_cubicCover_component_normal D hZ z hz hH c (Or.inr hm)).1
  let X := B ⊔ zpowers t
  let K := B.subgroupOf X
  let ρ := σ.comp X.subtype
  let τ := sectionRepresentation ρ U N
  let C : Subrepresentation σ := {
    toSubmodule := Coinvariants.ker (σ.comp B.subtype)
    apply_mem_toSubmodule g := Coinvariants.le_comap_ker σ B g }
  let ek : K ≃* B := subgroupOfEquivOfLe le_sup_left
  have hker : Coinvariants.ker (ρ.comp K.subtype) = C.toSubmodule := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨k,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ek k) v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ek.symm b) v
  have hlewhole : C.toSubmodule ≤ Coinvariants.ker ρ := by
    rw [←hker]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker k.val v
  have hnt : τ.comp K.subtype ≠ 1 := by
    intro he
    have hv : ec.symm Sporadic.Mathieu.M22TripleCover.scalar = 1 := hfaith (by rw [he]; rfl)
    have ho := Sporadic.Mathieu.M22TripleCover.scalar_order_of_equiv ec
    rw [hv,orderOf_one] at ho
    contradiction
  let := hirrB
  have hdimle : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp K.subtype)) ≤
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) := by
    rw [hker,hdim]
    exact (Submodule.finrank_mono hlewhole).trans hd
  obtain ⟨hle,e,he⟩ := coinvariants_section_equiv_of_finrank_le ρ K U N hnt hdimle
  have hCN : C.toSubmodule ≤ N.toSubmodule := hker ▸ hle
  let eC : Equiv (C.toRepresentation.comp X.subtype) τ := {
    toLinearEquiv := (LinearEquiv.ofEq _ _ hker.symm).trans e.toLinearEquiv
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact LinearMap.congr_fun (e.isIntertwining' g) ((LinearEquiv.ofEq _ _ hker.symm) v) }
  have heC (v : C.toSubmodule) : eC v =
      (sectionLower ρ U N).toSubmodule.mkQ (Submodule.inclusion hCN v) := he _
  have hdimC : Module.finrank (ZMod 2) C.toSubmodule = 12 :=
    eC.toLinearEquiv.finrank_eq.trans hdim
  have hwhole : Coinvariants.ker ρ = C.toSubmodule :=
    (Submodule.eq_of_le_of_finrank_le hlewhole (by rw [hdimC]; exact hd)).symm
  let eK : Equiv ((C.toRepresentation.comp X.subtype).comp K.subtype) (τ.comp K.subtype) :=
    Representation.Equiv.mk eC.toLinearEquiv (fun k => eC.isIntertwining' k)
  let eB : Equiv (C.toRepresentation.comp B.subtype)
      (Sporadic.Mathieu.M22TripleCover.representationOfEquiv (ek.symm.trans ec)) :=
    Representation.Equiv.mk (eK.trans em).toLinearEquiv (fun b => (eK.trans em).isIntertwining' (ek.symm b))
  obtain ⟨hfaithC,hirrC⟩ := faithful_irreducible_of_equiv eB
    (Sporadic.Mathieu.M22TripleCover.representationOfEquiv_faithful _)
    (Sporadic.Mathieu.M22TripleCover.representationOfEquiv_irreducible _)
  let E := D.fullSetup hZ T z
  have hgroup : κ.imageSpace ⁅E.UH H,c.K⁆ = C.toSubmodule := by
    rw [commutator_comm,κ.imageSpace_commutator c.K (E.UH H) c.le_H le_rfl,
      κ.imageSpace_self]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨u,hu,v,_,rfl⟩
      exact Coinvariants.sub_mem_ker
        (⟨QuotientGroup.mk' (pCore 2 H) u,mem_map_of_mem _ hu⟩ : B) v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨⟨b,hb⟩,v⟩,rfl⟩
      obtain ⟨u,hu,rfl⟩ := hb
      exact Submodule.subset_span ⟨u,hu,v,Submodule.mem_top,rfl⟩
  have hg := S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn
  have hcomm : ⁅V,E.UH H⁆ ≤ E.V₅ := by
    rw [commutator_comm]
    exact le_sup_right.trans_eq hg.2.2.2.1.symm
  have hidx : E.V₁.relIndex E.V₅ = 2 ^ 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (E.V₁.subgroupOf E.V₅)
    rw [Nat.card_congr (subgroupOfEquivOfLe E.V₁_le_V₅).toEquiv] at hh
    change Nat.card E.V₅ = E.V₁.relIndex E.V₅ * Nat.card E.V₁ at hh
    rw [E.perpendicular_card hz,E.point_card hz] at hh
    omega
  have hdimV := κ.imageSpace_finrank_of_index E.V₅ (le_conjugateSpanBy _ _) 4 hidx
  have hdispV : (σ t - LinearMap.id).range ≤ κ.imageSpace E.V₅ := by
    obtain ⟨u,hu,rfl⟩ := ht
    exact κ.displacement_range_le_imageSpace_of_commutator_le V E.V₅ hcomm u hu
  let tx : X := ⟨t,(le_sup_right : zpowers t ≤ X) (mem_zpowers t)⟩
  have hlow : 4 ≤ Module.finrank (ZMod 2) (σ t - LinearMap.id).range := by
    have hb := fixedCodim_section_le ρ U N (zpowers tx)
    rw [hdisp,fixedCodim_zpowers_eq_displacement_rank] at hb
    exact hb
  have hdisp_eq : (σ t - LinearMap.id).range = κ.imageSpace E.V₅ :=
    Submodule.eq_of_le_of_finrank_le hdispV (by rw [hdimV]; exact hlow)
  have hVle : κ.imageSpace E.V₅ ≤ C.toSubmodule := by
    rw [←hdisp_eq,←hwhole]
    rintro _ ⟨v,rfl⟩
    exact Coinvariants.sub_mem_ker tx v
  exact ⟨C,rfl,hgroup.symm,hdimC,hirrC,hfaithC,⟨ek.symm.trans ec,⟨eB⟩⟩,
    t,ht,hto,hwhole,hdisp_eq,hVle,U,N,hirr,hdisp,hCN,eC,heC⟩

/-- On the actual U_H/V₁ quotient, [U_H/V₁,K-star] is the faithful
irreducible twelve-dimensional James module, containing the original V₅/V₁. -/
theorem SourceHypothesis.original_mathieuCover_commutator
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
    : let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
      let _ : ((D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)).Normal :=
        h.point_normal_in_UH
      let _ : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H ⧸
          (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)) :=
        h.point_quotient_elementary
      ∃ (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H)
          (Additive ((D.fullSetup hZ T z).UH H ⧸
            (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H))))
        (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
          ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))),
        Function.Injective σ ∧
        (∀ u : (D.fullSetup hZ T z).UH H, (κ.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((D.fullSetup hZ T z).V₁.subgroupOf
            ((D.fullSetup hZ T z).UH H)) u)) ∧
    ∃ C : Subrepresentation σ,
      C.toSubmodule = Coinvariants.ker (σ.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      C.toSubmodule = κ.imageSpace ⁅(D.fullSetup hZ T z).UH H,c.K⁆ ∧
      Module.finrank (ZMod 2) C.toSubmodule = 12 ∧
      IsIrreducible (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      Function.Injective (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      (∃ ec : Nonabelian.Setup.star H c.K ≃* Sporadic.Mathieu.M22TripleCover,
        Nonempty (Equiv (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype)
          (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec))) ∧
      ∃ t : Nonabelian.Setup.Hstar H,
        t ∈ Nonabelian.Setup.star H V ∧ orderOf t = 2 ∧
        let X := Nonabelian.Setup.star H c.K ⊔ zpowers t
        let ρ := σ.comp X.subtype
        Coinvariants.ker ρ = C.toSubmodule ∧
        (σ t - LinearMap.id).range = κ.imageSpace (D.fullSetup hZ T z).V₅ ∧
        κ.imageSpace (D.fullSetup hZ T z).V₅ ≤ C.toSubmodule ∧
        ∃ U N : Subrepresentation ρ,
          IsIrreducible (sectionRepresentation ρ U N) ∧
          fixedCodim (sectionRepresentation ρ U N)
            (zpowers (⟨t, (le_sup_right : zpowers t ≤ X) (mem_zpowers t)⟩ : X)) = 4 ∧
          ∃ hle : C.toSubmodule ≤ N.toSubmodule,
            ∃ e : Equiv (C.toRepresentation.comp X.subtype) (sectionRepresentation ρ U N),
              ∀ v, e v = (sectionLower ρ U N).toSubmodule.mkQ (Submodule.inclusion hle v) := by
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,hcoordinates⟩ := h.faithful_point_quotient
  exact ⟨σ,κ,hσ,hcoordinates,
    S.original_mathieuCover_commutator_of_binary_section D hZ z hz hTV hTz hbound hH hn c a hm σ hσ κ⟩

end CFSG.Quasithin.Chapter12.Section06
