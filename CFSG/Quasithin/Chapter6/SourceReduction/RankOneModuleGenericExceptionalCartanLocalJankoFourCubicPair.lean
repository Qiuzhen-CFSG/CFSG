module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.HallActors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourMax4Compatibility

/-!
# The original J₄ escaping actor is a cubic in an elementary nine

The remaining max1 placement has a literal M₂₄ quotient with two-group
kernel. Hall existence and native M₂₄ geometry restrict its cyclic odd
actor to order three. The original normalizing cubic centralizes it;
escape makes the two cubics distinct. Both original permuting products
then give an elementary nine and a whole actor of order 9·2²¹. Under
the SAME max1 conjugation, the literal M₂₄ image has order 9,216 and lies in an actual octad or translated trio stabilizer.

Every original map, Hall condition, residual and S₅/S₃ marking is retained.
Normalization of that residual by this nine still requires the compatible
M₂₄ geometry; these order calculations do not assert that max1 contains it.

Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
variable {G : Type*} [Group G] [Finite G]

/-- The original native action supplies an elementary nine and the exact Mathieu image. -/
theorem normal_jankoFour_native_cubic_pair
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (S : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ x : C, f x = e (QuotientGroup.mk' (pCore 2 C) x)) ∧
      (S : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      let R := ((residual H).subgroupOf Y).map f
      let D := (A.subgroupOf Y).map f
      let E := (B.subgroupOf Y).map f
      R ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      Nat.card B = 3 ∧ Nat.card E = 3 ∧ E ≤ R ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set Janko4.Model) ∧
      (D : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (D : Set Janko4.Model) ∧
      Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ∧
      (E : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (E : Set Janko4.Model) ∧
      Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 ∧
      Nat.card (pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) = 2^20 ∧
      Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
        pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
        Equiv.Perm (Fin 5)) ∧
      (∃ e₃ : ((E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
          pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
          Equiv.Perm (Fin 3),
        let N := E ⊔ (S : Subgroup Janko4.Model)
        let q := e₃.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf N).map q) = 2 ∧
        Nat.card ((E.subgroupOf N).map q) = 3) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E ∧
      pCore 2 ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ≠ ⊥ ∧
      JankoFourWholeActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      JankoFourSolvableActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∀ g : MulAut Janko4.Model,
        (S : Subgroup Janko4.Model).map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        D.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        ¬ R.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup) ∧
      pCore 2 R ≠ ⊥ ∧
      JankoFourRemainingActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∃ g : Janko4.Model,
        (S : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom =
          Janko4.OuterReduction.OddIndex.twoSubgroup ∧
        ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤
          Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∧
        let I := (((((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E).map
          (MulAut.conj g).toMonoidHom).subgroupOf
          (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)).map
          Janko4.LocalStructure.MathieuHallActors.projection)
        Nat.card I = 9216 ∧
          ((∃ O : Sporadic.Mathieu.M24LocalGeometry.Octad,
            I ≤ Sporadic.Mathieu.M24LocalGeometry.octadStabilizer O) ∨
           ∃ t : Sporadic.Mathieu.M24,
            I ≤ Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.conjugateTrioStabilizer t)) ∧
      Nat.card D = 3 ∧ ⁅D,E⁆ = ⊥ ∧ Disjoint D E ∧
      Nat.card (D ⊔ E : Subgroup Janko4.Model) = 9 ∧
      IsElementaryAbelian 3 (D ⊔ E : Subgroup Janko4.Model) ∧
      Nat.card ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) = 9 * 2^21 := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    g,hSg,hKM⟩ := normal_jankoFour_native_max1 h hH hgen c hY hescape hR C hC hRC e
  obtain ⟨hD,hDE,hdis,h9,hel,hK⟩ := Janko4.LocalStructure.MathieuHallActors.cubic_pair
    S _ _ hsol hodd hcyc hE hED hnot hDS hES (MulAut.conj g) hKM
  let K := (((A.subgroupOf Y).map f ⊔ (S : Subgroup Janko4.Model)) ⊔
    (B.subgroupOf Y).map f)
  let a := MulAut.conj g
  let P := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : Nat.card P = Nat.card S := by
    change Nat.card ((S : Subgroup Janko4.Model).map a.toMonoidHom) = Nat.card S
    exact card_map_of_injective a.injective
  have hKm : Nat.card (K.map a.toMonoidHom) = 9 * Nat.card P := by
    rw [card_map_of_injective a.injective,hP]
    exact hK
  have himage := Janko4.LocalStructure.MathieuHallActors.whole_actor_image_card
    P (K.map a.toMonoidHom) (map_mono (le_sup_right.trans le_sup_left)) hKM hKm
  let : Group.IsSolvable K := hsol
  let : Group.IsSolvable (K.map a.toMonoidHom) := Group.isSolvable_of_surjective
    (f := a.toMonoidHom.subgroupMap K) (a.toMonoidHom.subgroupMap_surjective K)
  have hgeometry := Janko4.LocalStructure.MathieuHallActors.whole_actor_image_geometry
    P (K.map a.toMonoidHom) (map_mono (le_sup_right.trans le_sup_left)) hKM
    inferInstance hKm
  refine ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    ⟨g,hSg,hKM,himage,hgeometry⟩,hD,hDE,hdis,h9,hel,?_⟩
  rwa [Janko4.OuterReduction.OddIndex.ambient_sylow_card S] at hK

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
