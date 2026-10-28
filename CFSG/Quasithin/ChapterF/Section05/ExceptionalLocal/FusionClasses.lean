module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSourceCore
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Generation
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionOuterClasses

/-!
# The two original involution classes and controlled source generation

Ordinary upper involutions have root or short representatives, while the
outer upper involutions have graph or graph-root representatives. The
source fusion core identifies the short and graph classes and identifies
the graph-root and root classes. Sylow conjugacy then gives the two
classes of all ambient involutions.

The controlled version composes the literal endpoint conjugators with
those from the exceptional enlargement, keeping every conjugator inside
`i.range ∨ N_G(A₂)`. Applying the generation criterion removes its entire
local-class premise. Only the subsequent F.5.5 description of the graph
centralizer and its chosen Sylow normalizing A₂ remain as inputs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.37,
F.5.3(4)–(5), and F.5.6, printed pp.293, 300–301 and 302–304.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

omit [Finite G] in
private theorem conjugator_comp {K : Subgroup G} {a b x : G}
    {g k : G} (hg : g ∈ K) (hk : k ∈ K)
    (hab : g*a*g⁻¹=b) (hbx : k*b*k⁻¹=x) :
    ∃ j ∈ K, j*a*j⁻¹=x := by
  refine ⟨k*g,K.mul_mem hk hg,?_⟩
  calc
    _=k*(g*a*g⁻¹)*k⁻¹ := by group
    _=x := by rw [hab,hbx]

/-- The exact controlled fusion family consumed by the F.5.6 generation argument. -/
theorem source_controlled_involution_classes (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hRH : Rimage c i R ≤ H c i)
    (x : G) (hx : x ∈ Source.sylowImage c i) (hx2 : orderOf x=2) :
    ∃ k ∈ i.range ⊔ H c i,
      k*rootElement c i z*k⁻¹=x ∨ k*Source.graphElement c i*k⁻¹=x := by
  classical
  by_cases hxS : x∈sourceOrdinaryUpper c i
  · obtain ⟨k,hk,hkx | hkx⟩ := sourceOrdinaryUpper_involution_classes_in_completion c i z h x hxS hx2
    · exact ⟨k,(show i.range ≤ i.range ⊔ H c i from le_sup_left) hk,Or.inl hkx⟩
    · obtain ⟨g,hg,hgt⟩ := source_controlled_graph_short_fusion c i z h R hR hRH
      obtain ⟨j,hj,hjx⟩ := conjugator_comp hg ((show i.range ≤ i.range ⊔ H c i from le_sup_left) hk) hgt hkx
      exact ⟨j,hj,Or.inr hjx⟩
  · obtain ⟨k,hk,hkx⟩ | ⟨k,hk,hkx⟩ := source_outer_involution_classes_in_range c i z h x hx hxS hx2
    · exact ⟨k,(show i.range ≤ i.range ⊔ H c i from le_sup_left) hk,Or.inr hkx⟩
    · obtain ⟨g,hg,hgz⟩ := source_controlled_root_product_fusion c i z h R hR hRH
      obtain ⟨j,hj,hjx⟩ := conjugator_comp hg ((show i.range ≤ i.range ⊔ H c i from le_sup_left) hk) hgz hkx
      exact ⟨j,hj,Or.inl hjx⟩

/-- All involutions of the original source Sylow are root or graph class. -/
theorem source_sylow_involution_classes (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (x : G) (hx : x∈Source.sylowImage c i) (hx2 : orderOf x=2) :
    IsConj (rootElement c i z) x ∨ IsConj (Source.graphElement c i) x := by
  classical
  by_cases hxS : x∈sourceOrdinaryUpper c i
  · rcases sourceOrdinaryUpper_involution_classes c i z h x hxS hx2 with hz | ht
    · exact Or.inl hz
    · exact Or.inr ((source_short_fusion_of_hypotheses c i z h).trans ht)
  · obtain ⟨k,_,hk⟩ | ⟨k,_,hk⟩ := source_outer_involution_classes_in_range c i z h x hx hxS hx2
    · exact Or.inr (isConj_iff.mpr ⟨k,hk⟩)
    · exact Or.inl ((source_root_product_fusion c i z h).trans (isConj_iff.mpr ⟨k,hk⟩))

private theorem source_two_classes_of_T_classes (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hlocal : ∀ x ∈ Source.sylowImage c i, orderOf x=2 →
      IsConj (rootElement c i z) x ∨ IsConj (Source.graphElement c i) x)
    (x : G) (hx2 : orderOf x=2) :
    IsConj (rootElement c i z) x ∨ IsConj (Source.graphElement c i) x := by
  obtain ⟨S,hS⟩ := source_sylowImage_isSylow c i z h
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (((Nat.card_zpowers x).trans hx2).trans (pow_one 2).symm)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  have hmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = Source.sylowImage c i :=
    (congrArg Sylow.toSubgroup hg).trans hS
  have hx : (MulAut.conj g) x ∈ Source.sylowImage c i :=
    hmap ▸ mem_map_of_mem _ (hP (mem_zpowers x))
  have hxconj : IsConj x ((MulAut.conj g) x) := isConj_iff.mpr ⟨g,rfl⟩
  rcases hlocal _ hx (((MulAut.conj g).orderOf_eq x).trans hx2) with hz | hf
  · exact Or.inl (hz.trans hxconj.symm)
  · exact Or.inr (hf.trans hxconj.symm)


/-- Every ambient involution belongs to one of the two original source classes. -/
theorem source_two_involution_classes (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx2 : orderOf x=2) :
    IsConj (rootElement c i z) x ∨ IsConj (Source.graphElement c i) x :=
  source_two_classes_of_T_classes c i z h (source_sylow_involution_classes c i z h) x hx2

/-- The completed source fusion calculation discharges the controlled-class
input of F.5.6. Only the subsequent normalizer/centralizer conclusions remain. -/
theorem source_generation_of_centralizer_description (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hRH : Rimage c i R ≤ H c i)
    (hcentral : C c i = Rimage c i R ⊔ D c i) :
    i.range ⊔ H c i = ⊤ :=
  source_generation_of_centralizer_join c i z h R hRH hcentral
    (source_controlled_involution_classes c i z h R hR hRH)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
