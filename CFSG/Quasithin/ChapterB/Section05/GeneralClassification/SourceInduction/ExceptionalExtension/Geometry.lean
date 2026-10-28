module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Construction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.MovedGeometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Ambient and quotient geometry for the exceptional B.5.6 branch

The literal product and centralizer show that [V,G₂] lies in V₂=C_V(G₁):
the mixed action differences commute and G₂ fixes W=[V,G₁]. The two moved
spaces are disjoint and generate [V,G]. If the second moved space supplements
the global fixed space in V₂, `hyperplane_of_second_action` constructs every
geometric field of B.5.6(5), with the actual second action still explicit.

In the split F*(G₂) branch, a complement supplies a vector outside W+V₂ in
C_V(F*(G₂)). Once C_V(F*(G₂)) ∩ V₂ ≤ C_V(G) is established, its second-factor
displacements are globally fixed. Only then do we construct the ambient
submodule U₁+C_V(G) and its direct complement in the global fixed quotient.
`firstSaturatedEquiv` identifies that literal quotient summand with the chosen
four-space by restricting the original quotient map.

No earlier-source implication is assumed here. The explicit second-action and
fixed-space comparisons are intermediate obligations for the two endgame
branches, not extra hypotheses of B.5.6. These results do not complete either
branch or the exceptional endgame.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
final proof of B.5.6, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
open ComponentReduction
open HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

abbrev second (c : Conclusion ρ) : Subgroup G := centralizer (c.first : Set G)

abbrev secondAction (c : Conclusion ρ) :=
  c.productConfiguration.fixed.toRepresentation.comp (second c).subtype

theorem first_fixed_by_second (c : Conclusion ρ) :
    c.sectionData.space.toSubmodule ≤ fixedSpace ρ (second c) := by
  intro v hv g
  have hg := g.property
  change (g : G) ∈ centralizer (c.first : Set G) at hg
  rw [c.productConfiguration.centralizer_eq] at hg
  exact hg.2 v hv

theorem second_moved_le_fixed (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) :
    moved ρ (second c) ≤ c.productConfiguration.fixed.toSubmodule := by
  rw [c.productConfiguration.fixed_eq]
  apply reverse_moved_fixed ρ
  · exact le_centralizer_iff.mp le_rfl
  · rw [first_moved c he]
    exact first_fixed_by_second c

theorem moved_disjoint (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) :
    Disjoint (moved ρ c.first) (moved ρ (second c)) := by
  rw [first_moved c he]
  have hd := natural_disjoint_fixed he.1
  apply hd.mono_right
  rw [← c.productConfiguration.fixed_eq]
  exact second_moved_le_fixed c he

theorem moved_eq (c : Conclusion ρ) :
    moved ρ ⊤ = moved ρ c.first ⊔ moved ρ (second c) := by
  let : c.first.Normal := c.productConfiguration.first_normal
  let : (second c).Normal := c.productConfiguration.second_normal
  rw [← c.productConfiguration.product.sup_eq_top]
  exact moved_sup ρ _ _

theorem invariants_le_fixed (c : Conclusion ρ) :
    ρ.invariants ≤ c.productConfiguration.fixed.toSubmodule := by
  rw [c.productConfiguration.fixed_eq]
  intro v hv g
  exact hv g

theorem exists_outside_in_supplement (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (S : Submodule (ZMod 2) V)
    (hs : S ⊔ c.productConfiguration.fixed.toSubmodule = ⊤) :
    ∃ x ∈ S, x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule := by
  by_contra! hn
  have hle : S ≤ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule := hn
  have ht : c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule = ⊤ :=
    top_unique (hs ▸ sup_le hle le_sup_right)
  obtain ⟨x,hx⟩ := exists_outside he
  apply hx
  rw [← c.productConfiguration.fixed_eq, ht]
  trivial

theorem chosenSpace_le {W S : Submodule (ZMod 2) V} (hw : W ≤ S) {x : V}
    (hx : x ∈ S) : chosenSpace W x ≤ S :=
  sup_le hw (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx))

noncomputable def secondMoved (c : Conclusion ρ) : Subrepresentation ρ :=
  let : (second c).Normal := c.productConfiguration.second_normal
  normalMoved ρ (second c)

noncomputable def hyperplane_of_second_action (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (hs : moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule)
    (hn : HyperplaneSecondCase ρ (second c) (secondMoved c)) : HyperplaneCase ρ where
  first := c.first
  second := second c
  product := c.productConfiguration.product
  firstEquiv := he.1.some.groupEquiv
  firstDimension := by rw [first_moved c he]; exact first_dimension c he
  disjoint := moved_disjoint c he
  moved_eq := moved_eq c
  hyperplane := by
    rw [moved_eq c, sup_assoc, hs, first_moved c he, c.productConfiguration.fixed_eq]
    exact he.2
  secondSpace := secondMoved c
  secondSpace_eq := rfl
  secondCase := hn

theorem adequate_of_second_action (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (hs : moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule)
    (hn : HyperplaneSecondCase ρ (second c) (secondMoved c)) : AdequateAlternative ρ :=
  Or.inr (.hyperplane (hyperplane_of_second_action c he hs hn))


theorem chosen_displacement_in_fixed (c : Conclusion ρ) (x : V)
    (hx : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants) :
    ∀ b : second c, ∀ v ∈ chosenSpace c.sectionData.space.toSubmodule x,
      ρ (b : G) v - v ∈ ρ.invariants := by
  intro b v hv
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [map_add, map_smul, (show ρ (b : G) w = w from first_fixed_by_second c hw b), add_sub_add_left_eq_sub,
    ← smul_sub]
  exact ρ.invariants.smul_mem a (hx b)

/-- Saturation by the global fixed space is ambient invariant once the
second-factor displacements of the chosen vector have been proved fixed. -/
noncomputable def saturatedModule (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) (x : V)
    (hx : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants) : Subrepresentation ρ where
  toSubmodule := chosenSpace c.sectionData.space.toSubmodule x ⊔ ρ.invariants
  apply_mem_toSubmodule g v hv := by
    obtain ⟨a,b,rfl⟩ := c.productConfiguration.product.exists_mul g
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    have hb := chosen_displacement_in_fixed c x hx b u hu
    have hd : ρ (a : G) u - u ∈ c.sectionData.space.toSubmodule :=
      (first_moved c he).le (Submodule.subset_span
        ⟨a,a.property,u,Submodule.mem_top,rfl⟩)
    have hau : ρ (a : G) u ∈ chosenSpace c.sectionData.space.toSubmodule x := by
      simpa using (chosenSpace c.sectionData.space.toSubmodule x).add_mem
        (Submodule.mem_sup_left hd) hu
    have hbu : ρ (b : G) u = u + (ρ (b : G) u - u) := by abel
    rw [map_add, hz, map_mul, Module.End.mul_apply, hbu, map_add, hb]
    exact Submodule.mem_sup.mpr ⟨ρ (a : G) u,hau,
      (ρ (b : G) u - u) + z,ρ.invariants.add_mem hb hz,(add_assoc _ _ _).symm⟩

theorem saturated_quotient_isCompl [FiniteDimensional (ZMod 2) V]
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (x : V) (hx : x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule)
    (hd : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants) :
    IsCompl ((fixed ρ).quotientImage (saturatedModule c he x hd)).toSubmodule
      ((fixed ρ).quotientImage c.productConfiguration.fixed).toSubmodule := by
  have hx' : x ∉ c.sectionData.space.toSubmodule ⊔ fixedSpace ρ c.first := by
    simpa only [c.productConfiguration.fixed_eq] using hx
  have hc : IsCompl (chosenSpace c.sectionData.space.toSubmodule x)
      c.productConfiguration.fixed.toSubmodule := by
    simpa only [c.productConfiguration.fixed_eq] using
      chosenSpace_isCompl (natural_disjoint_fixed he.1) he.2 hx'
  constructor
  · apply Submodule.disjoint_def.mpr
    rintro q ⟨a,ha,rfl⟩ ⟨b,hb,heq⟩
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp ha
    have hdif : u + z - b ∈ ρ.invariants :=
      (Submodule.Quotient.eq ρ.invariants).mp heq.symm
    have huc : u ∈ c.productConfiguration.fixed.toSubmodule := by
      have h := c.productConfiguration.fixed.toSubmodule.add_mem
        (invariants_le_fixed c hdif) hb
      have h' := c.productConfiguration.fixed.toSubmodule.sub_mem h (invariants_le_fixed c hz)
      convert h' using 1; abel
    have hu0 : u = 0 := Submodule.disjoint_def.mp hc.disjoint u hu huc
    apply (Submodule.Quotient.mk_eq_zero ρ.invariants).mpr
    simpa only [hu0,zero_add] using hz
  · apply codisjoint_iff.mpr
    change (chosenSpace c.sectionData.space.toSubmodule x ⊔ ρ.invariants).map ρ.invariants.mkQ ⊔
      c.productConfiguration.fixed.toSubmodule.map ρ.invariants.mkQ = ⊤
    rw [← Submodule.map_sup]
    have hs : (chosenSpace c.sectionData.space.toSubmodule x ⊔ ρ.invariants) ⊔
        c.productConfiguration.fixed.toSubmodule = ⊤ := by
      rw [sup_assoc, sup_eq_right.mpr (invariants_le_fixed c), hc.sup_eq_top]
    rw [hs, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr ρ.invariants.mkQ_surjective

/-- The split L₂ branch can choose x inside its fixed space, because its
moved summand is contained in V₂. No ambient invariance of U₁ is assumed. -/
theorem split_exists_fixed_choice (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (L₂ : Subgroup G) (hL : L₂ ≤ second c)
    (hs : IsCompl (moved ρ L₂) (fixedSpace ρ L₂)) :
    ∃ x ∈ fixedSpace ρ L₂,
      x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule := by
  apply exists_outside_in_supplement c he
  apply top_unique
  rw [← hs.symm.sup_eq_top]
  apply sup_le_sup_left
  apply le_trans _ (second_moved_le_fixed c he)
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,hL hg,v,hv,rfl⟩


/-- L₂ is F*(G₂) followed by its original inclusion in G. -/
abbrev secondCore (c : Conclusion ρ) : Subgroup G :=
  (generalizedFitting (second c)).map (second c).subtype

/-- The source splits V over the moved space of F*(G₂), not over [V,G₂]. -/
def SplitAtSecond (c : Conclusion ρ) : Prop :=
  IsCompl (moved ρ (secondCore c)) (fixedSpace ρ (secondCore c))

theorem secondCore_le (c : Conclusion ρ) : secondCore c ≤ second c := by
  rintro _ ⟨g,_,rfl⟩
  exact g.property

theorem secondCore_normal (c : Conclusion ρ) : (secondCore c).Normal := by
  let : (second c).Normal := c.productConfiguration.second_normal
  change ((generalizedFitting (second c)).map (second c).subtype).Normal
  infer_instance

/-- Invariance of C_V(L₂) and the proved equality of fixed spaces control the
chosen vector's second-factor displacements in the split source branch. -/
theorem fixed_choice_displacement (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    {L₂ : Subgroup G} (hn : second c ≤ normalizer (L₂ : Set G))
    (hf : fixedSpace ρ L₂ ⊓ c.productConfiguration.fixed.toSubmodule ≤ ρ.invariants)
    {x : V} (hx : x ∈ fixedSpace ρ L₂) :
    ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants := by
  intro b
  apply hf
  constructor
  · exact (fixedSpace ρ L₂).sub_mem
      ((fixedSpace_invariant_normalizer ρ hn b.property x).2 hx) hx
  · apply second_moved_le_fixed c he
    exact Submodule.subset_span ⟨b,b.property,x,Submodule.mem_top,rfl⟩

/-- The original split branch constructs an ambient first summand only after
proving its displacements fixed; the decomposition is in V/C_V(G). The
remaining fixed-space equality is a second-factor model obligation. -/
theorem split_quotient_geometry [FiniteDimensional (ZMod 2) V]
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (hs : SplitAtSecond c)
    (hf : fixedSpace ρ (secondCore c) ⊓ c.productConfiguration.fixed.toSubmodule ≤ ρ.invariants) :
    ∃ (x : V) (_hx : x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule)
      (hd : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants),
      x ∈ fixedSpace ρ (secondCore c) ∧
      IsCompl ((fixed ρ).quotientImage (saturatedModule c he x hd)).toSubmodule
        ((fixed ρ).quotientImage c.productConfiguration.fixed).toSubmodule := by
  obtain ⟨x,hxf,hx⟩ := split_exists_fixed_choice c he (secondCore c) (secondCore_le c) hs
  have hn : second c ≤ normalizer (secondCore c : Set G) := by
    let := secondCore_normal c
    rw [normalizer_eq_top]
    exact le_top
  have hd := fixed_choice_displacement c he hn hf hxf
  exact ⟨x,hx,hd,hxf,saturated_quotient_isCompl c he x hx hd⟩


/-- The first quotient summand has precisely the chosen four-dimensional
G₁-action. The map is the restriction of the original quotient map. -/
noncomputable def firstSaturatedEquiv [FiniteDimensional (ZMod 2) V]
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (x : V) (hx : x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule)
    (hd : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants) :
    ActionEquiv (chosenModule c.sectionData.space (first_moved c he).le x).toRepresentation
      (((fixed ρ).quotientImage (saturatedModule c he x hd)).toRepresentation.comp c.first.subtype) := by
  let U := chosenModule c.sectionData.space (first_moved c he).le x
  let Q := (fixed ρ).quotientImage (saturatedModule c he x hd)
  let f : U.toSubmodule →ₗ[ZMod 2] Q.toSubmodule :=
    { toFun := fun u => ⟨ρ.invariants.mkQ u, ⟨u,Submodule.mem_sup_left u.property,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hx' : x ∉ c.sectionData.space.toSubmodule ⊔ fixedSpace ρ c.first := by
    simpa only [c.productConfiguration.fixed_eq] using hx
  have hc : Disjoint U.toSubmodule c.productConfiguration.fixed.toSubmodule := by
    change Disjoint (chosenSpace c.sectionData.space.toSubmodule x) c.productConfiguration.fixed.toSubmodule
    simpa only [c.productConfiguration.fixed_eq] using
      (chosenSpace_isCompl (natural_disjoint_fixed he.1) he.2 hx').disjoint
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hq : ρ.invariants.mkQ (a : V) = ρ.invariants.mkQ (b : V) := congrArg Subtype.val hab
    have hz : (a : V) - b ∈ ρ.invariants := (Submodule.Quotient.eq ρ.invariants).mp hq
    exact Submodule.disjoint_def.mp hc _ (U.toSubmodule.sub_mem a.property b.property)
      (invariants_le_fixed c hz)
  have hs : Function.Surjective f := by
    rintro ⟨q,a,ha,rfl⟩
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp ha
    refine ⟨⟨u,hu⟩, ?_⟩
    apply Subtype.ext
    change ρ.invariants.mkQ u = ρ.invariants.mkQ (u+z)
    rw [map_add, (show ρ.invariants.mkQ z = 0 from
      (Submodule.Quotient.mk_eq_zero ρ.invariants).mpr hz), add_zero]
  exact ⟨MulEquiv.refl c.first, LinearEquiv.ofBijective f ⟨hi,hs⟩, fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
