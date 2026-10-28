module
public import Theory.SpecificGroups.SymplecticFour.FixedComponents
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks
public import Theory.GroupTheory.PrimeRankSylow
/-!
# The symplectic row in the original overcomponent argument

The original Mathieu source supplies simplicity and its actual Sylow two
shape. Transport to the concrete symplectic model then excludes the inner
and graph involutions and forces the field involution of Sp₄(4), with fixed
component A₆. The conclusion retains the field conjugacy marking.

Source: Aschbacher–Smith, Lemma 2.5.19(3)(c), p.561.
-/
public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection DiagramAutomorphisms

theorem source_symplectic_fixed_component {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Finite E] {n:ℕ} (hn:1<n)
    (hm:ClassicalGroup.IsPSp E 2 (2^n)) (a:MulAut E) (ha:orderOf a=2)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B) (eK:K≃*B) :
    n=2 ∧ Nonempty (K≃*alternatingGroup (Fin 6)) ∧
      ∃(F:Type)(_:Field F)(_:Finite F)(_:CharP F 2),Nat.card F=4 ∧
        ∃e:E≃*Sp F, IsConj (MulAut.congr e a) (FieldFixedResidual.representative (F:=F) 1) := by
  obtain ⟨F,hField,hFinite,hF,⟨e0⟩⟩:=hm
  let : CharP F 2:=EvenProjective.charTwo_of_card hF
  let e:E≃*Sp F:=e0.trans EvenProjective.equiv.symm
  let a':=MulAut.congr e a
  let ef:=MulAut.fixedSubgroupCongr e a
  let D:=B.map ef.toMonoidHom
  let C:=D.map a'.fixedSubgroup.subtype
  have hC:IsComponentIn C a'.fixedSubgroup := by
    refine ⟨map_subtype_le _,?_⟩
    have he:C.subgroupOf a'.fixedSubgroup=D:=comap_map_eq_self_of_injective a'.fixedSubgroup.subtype_injective _
    rw [he]
    exact hB.map_equiv ef
  let eB:B≃*C:=(ef.subgroupMap B).trans (D.equivMapOfInjective a'.fixedSubgroup.subtype a'.fixedSubgroup.subtype_injective)
  let k:K≃*C:=eK.trans eB
  have hs:=ComponentSelection.MathieuSourceSetup.small_source_structure c hG hempty hgen hb
  let : IsSimpleGroup K:=hs.2.1
  let : IsSimpleGroup C:=k.symm.isSimpleGroup
  let P:Sylow 2 K:=default
  let Q:=P.mapSurjective (f:=k.toMonoidHom) k.surjective
  let eP:P≃*Q:=(P:Subgroup K).equivMapOfInjective k.toMonoidHom k.injective
  have hQ:SourceSylowTwoShape Q:=(hs.1.sylowTwoShape P).of_mulEquiv eP.symm
  have hr:primeRank 2 C≤2:=by rw [Q.primeRank_eq];exact hQ.rank_and_involutions.1
  obtain ⟨hn2,⟨d⟩,hfield⟩:=FixedComponents.component_of_source_sylow_shape hn hF a'
    (((MulAut.congr e).orderOf_eq a).trans ha) C hC hr Q hQ.rank_and_involutions.2
  exact ⟨hn2,⟨k.trans d⟩,F,hField,hFinite,inferInstance,by simpa [hn2] using hF,e,hfield⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
