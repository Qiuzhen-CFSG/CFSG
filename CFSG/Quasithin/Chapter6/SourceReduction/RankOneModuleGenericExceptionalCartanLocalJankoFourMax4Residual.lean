module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Residual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourSolvable

/-!
# Same-residual normalization under common max4 placement

The literal max4 quotient is S₅ × SL₃(2). The lower-layer proof identifies
any full-Sylow-normalized perfect A₅ section inside max4 with the solvable
residual of the marked A₅ preimage, so the whole max4 normalizes it.
Ambient automorphisms transport this conclusion with the same subgroup
and Sylow; an escaping Cartan actor cannot share that max4 placement.

The native application retains the original surjection, residual, both Hall
products, S₅ quotient, marked S₃ quotient and whole-actor placements.
It discharges normalization when the residual and actor share max4.
Their simultaneous placement, and the max1 and involution-centralizer
branches, remain required in the source argument.

Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

/-- A common max4 placement normalizes the same original local A₅ residual. -/
theorem jankoFour_common_max4_normalizes
    (S : Sylow 2 Model) (R : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (g : MulAut Model)
    (hS : (S : Subgroup Model).map g.toMonoidHom ≤ max4Subgroup)
    (hR : R.map g.toMonoidHom ≤ max4Subgroup) :
    max4Subgroup ≤ normalizer (R.map g.toMonoidHom : Set Model) := by
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hl
  let : Group.IsPerfect (R.map g.toMonoidHom) := Group.IsPerfect.map _
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let d := g.subgroupMap R
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  exact max4_normalizes_perfect_five
    (S.mapSurjective (f := g.toMonoidHom) g.surjective) (R.map g.toMonoidHom)
    (a.symm.trans eR)
    ((map_mono (f := g.toMonoidHom) hn).trans (R.le_normalizer_map g.toMonoidHom)) hS hR

/-- An escaping actor and its original residual cannot share any conjugate max4. -/
theorem jankoFour_no_common_max4
    (S : Sylow 2 Model) (R D : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hout : ¬ D ≤ normalizer (R : Set Model))
    (g : MulAut Model)
    (hS : (S : Subgroup Model).map g.toMonoidHom ≤ max4Subgroup)
    (hD : D.map g.toMonoidHom ≤ max4Subgroup) :
    ¬ R.map g.toMonoidHom ≤ max4Subgroup := by
  intro hR
  have hd := hD.trans (jankoFour_common_max4_normalizes S R hl hn he g hS hR)
  rw [← map_equiv_normalizer_eq] at hd
  exact hout ((map_le_map_iff_of_injective g.injective).mp hd)

open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The original native map retains every marking and excludes common max4
placement of the escaping actor and the same residual. -/
theorem normal_jankoFour_native_max4_residual
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
        (S : Subgroup Janko4.Model).map g.toMonoidHom ≤ max4Subgroup →
        D.map g.toMonoidHom ≤ max4Subgroup →
        ¬ R.map g.toMonoidHom ≤ max4Subgroup) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace⟩ :=
    normal_jankoFour_native_solvable_placement h hH hgen c hY hescape hR C hC hRC e
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,
    fun g hSg hDg => jankoFour_no_common_max4 S _ _ hl hSR hfour hout g hSg hDg⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
