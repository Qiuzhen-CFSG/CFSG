module
public import Theory.GroupTheory.IndexTwoCyclicImage
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterActionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFixedSource

/-!
# The actual split involution in the centerless source complement

The torus complement is noncyclic by the proved transfer argument, while
its action on Z(R) is cyclic and faithful on its intersection with S.
The index-two kernel therefore supplies a central involution x outside S.
The original fixed-group row gives C_R(x)=Z(R), and the index-two cosets
identify C_T(Z(R))=R<x>. The same x commutes with the marked cyclic field
complement, supplying the literal split element for the p.539 argument.

Every input is from the original setup, apart from the separately owned
involution-closure conclusion of 2.4.21(2).
Source: Aschbacher–Smith, Lemma 2.4.24(3), printed p.538.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_split_involution
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let Z := R ⊓ centralizer (R : Set G)
    ∃ x ∈ (T : Subgroup G) ⊓ normalizer (c.hall : Set G), x ∉ S ∧ orderOf x = 2 ∧
      R ⊓ centralizer ({x} : Set G) = Z ∧
      (T : Subgroup G) ⊓ centralizer (Z : Set G) = R ⊔ zpowers x ∧
      (∀ f ∈ S ⊓ normalizer (c.hall : Set G), Commute x f) ∧
      (T : Subgroup G) ⊓ normalizer (c.hall : Set G) =
        zpowers x ⊔ (S ⊓ normalizer (c.hall : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  let ST := S.subgroupOf (T : Subgroup G)
  let A := (normalizer (c.hall : Set G)).subgroupOf (T : Subgroup G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRT : R ≤ (T : Subgroup G) := hRS.trans hST.le
  have hRC : R ≤ centralizer (Z : Set G) := le_centralizer_iff.mp inf_le_right
  have hSC : S ⊓ centralizer (Z : Set G) = R := by
    simpa only [distinguishedZ_of_centerless d hZ] using
      source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hi : ST.index = 2 := (d.lemma_2_4_8_1 hG T hST hsingle hL').1
  let := c.normal_in_sylow
  have hncyc : ¬ IsCyclic A := by
    intro hcyc
    exact c.quotient_not_cyclic_of_fusion hG hclosed
      ((c.split_ambient.symm.QuotientMulEquiv).isCyclic.mpr hcyc)
  obtain ⟨hTZ,hcyc⟩ := source_centerless_center_action_cyclic d hG T hST hsingle hL
    hM hTM hu c hZ
  let α := Z.normalizerMonoidHom.comp (inclusion hTZ)
  let : IsCyclic α.range := hcyc
  have hker (a : T) (ha : α.rangeRestrict a = 1) : (a:G) ∈ centralizer (Z : Set G) := by
    have he := congrArg Subtype.val ha
    change a ∈ α.ker at he
    change a ∈ (Z.normalizerMonoidHom.comp (inclusion hTZ)).ker at he
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker] at he
    exact he
  obtain ⟨x,hxA,hxS,hx2,hxker,hxc,hgen⟩ :=
    Subgroup.exists_central_involution_of_index_two_cyclic_image ST A hi hncyc α.rangeRestrict (by
      intro a haA haS ha1
      have haR : (a:G) ∈ R := hSC ▸ (show (a:G) ∈ S ⊓ centralizer (Z : Set G) from ⟨haS,hker a ha1⟩)
      exact disjoint_def.mp c.split_ambient.disjoint haR haA)
  have hxC : (x:G) ∈ centralizer (Z : Set G) := hker x hxker
  have hxord : orderOf (x:G) = 2 := (orderOf_coe x).trans hx2
  have hxpow : (x:G)^2=1 := by simpa only [hxord] using pow_orderOf_eq_one (x:G)
  refine ⟨x,⟨x.property,hxA⟩,hxS,hxord,
    (source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hu
      x x.property hxS hxpow hxC).1,?_,?_,?_⟩
  · apply le_antisymm
    · intro a ha
      by_cases haS : a ∈ S
      · exact mem_sup_left (hSC.le ⟨haS,ha.2⟩)
      · have har : a*(x:G)⁻¹ ∈ R := by
          rw [←hSC]
          refine ⟨?_,(centralizer (Z:Set G)).mul_mem ha.2 ((centralizer (Z:Set G)).inv_mem hxC)⟩
          exact (ST.mul_mem_iff_of_index_two hi (a := ⟨a,ha.1⟩) (b := x⁻¹)).mpr
            (by change (a ∈ S ↔ (x:G)⁻¹ ∈ S); rw [inv_mem_iff]; exact iff_of_false haS hxS)
        have hh := (R ⊔ zpowers (x:G)).mul_mem (mem_sup_left har) (mem_sup_right (mem_zpowers _))
        simpa only [inv_mul_cancel_right] using hh
    · exact sup_le (le_inf hRT hRC) (zpowers_le.mpr ⟨x.property,hxC⟩)
  · intro f hf
    exact congrArg Subtype.val (hxc ⟨f,hST.le hf.1⟩ hf.2)
  · have hm := congrArg (Subgroup.map (T : Subgroup G).subtype) hgen
    rw [Subgroup.map_sup,MonoidHom.map_zpowers] at hm
    have hAmap : A.map (T : Subgroup G).subtype = (T : Subgroup G) ⊓ normalizer (c.hall:Set G) := by
      ext g
      exact ⟨fun ⟨t,ht,he⟩ => he ▸ ⟨t.property,ht⟩,fun h => ⟨⟨g,h.1⟩,h.2,rfl⟩⟩
    have hFmap : (A ⊓ ST).map (T : Subgroup G).subtype = S ⊓ normalizer (c.hall:Set G) := by
      rw [map_inf _ _ _ (T : Subgroup G).subtype_injective,hAmap,map_subgroupOf_eq_of_le hST.le]
      ext g
      simp only [mem_inf]
      exact ⟨fun h=>⟨h.2,h.1.2⟩,fun h=>⟨⟨hST.le h.1,h.2⟩,h.1⟩⟩
    rw [hAmap,hFmap] at hm
    exact hm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
