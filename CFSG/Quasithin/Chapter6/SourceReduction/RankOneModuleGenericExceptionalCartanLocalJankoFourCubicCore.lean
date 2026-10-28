module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CubicCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCubicPair
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer


/-!
# The original J₄ cubic fixes the marked eight in the max4 two-core

For a full-Sylow-normalized local A₅ section, the checked max4 placement
identifies its perfect residual with the residual of the literal A₅ preimage.
The original cubic therefore lies in that preimage. The model fixed-core
bound gives at most eight fixed elements, while the perfect A₅ section
centralizes the certified normal eight. These inclusions give exact equality.
The equality transports under every specified ambient automorphism.

The native application retains the original quotient map, both Hall products,
residual and S₅/S₃ markings. Sylow conjugacy constructs an actual max4 marking;
no new module or source premise is imposed. Comparing the max1 kernel with
this same fixed subgroup, and normalization of the original residual by the
escaping actor, remain separate steps of the source argument.

Source: Aschbacher--Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

private theorem perfect_five_centralizes_eight (R : Subgroup max4Subgroup)
    [Group.IsPerfect R] (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5)) :
    R ≤ centralizer (NormalEight.eight : Set max4Subgroup) := by
  let := NormalEight.elementary_eight
  let := NormalEight.normal_eight
  have hn : R ≤ normalizer (NormalEight.eight : Set max4Subgroup) := by
    rw [normalizer_eq_top]
    exact le_top
  let f := NormalEight.eight.normalizerMonoidHom.comp (inclusion hn)
  have hf : f = 1 := AlternatingFiveSmallAction.small_elementary_action_trivial e
    (by rw [NormalEight.card_eight]) f
  intro r hr
  have hk : inclusion hn ⟨r,hr⟩ ∈ NormalEight.eight.normalizerMonoidHom.ker := by
    change f ⟨r,hr⟩ = 1
    rw [hf]
    rfl
  rwa [normalizerMonoidHom_ker] at hk

/-- The original cubic fixes exactly the certified eight inside the SAME max4 two-core. -/
theorem jankoFour_same_cubic_fixed_core (S : Sylow 2 Model) (R E : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hE : Nat.card E = 3) (hER : E ≤ R)
    (hS : (S : Subgroup Model) ≤ max4Subgroup) :
    pCore 2 max4Subgroup ⊓ centralizer (E.subgroupOf max4Subgroup : Set max4Subgroup) =
      NormalEight.eight := by
  have hR := jankoFour_residual_le_max4 S R hl hn he hS
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hl
  let d := subgroupOfEquivOfLe hR
  let : Group.IsPerfect (R.subgroupOf max4Subgroup) :=
    Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
    (eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  have hSR : ((S.subtype hS : Sylow 2 max4Subgroup) : Subgroup max4Subgroup) ≤
      normalizer (R.subgroupOf max4Subgroup : Set max4Subgroup) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro r
    exact mem_normalizer_iff.mp (hn hx) (r : Model)
  have hRpre : R.subgroupOf max4Subgroup ≤ a5Preimage := by
    rw [perfect_five_eq_residual_preimage (R.subgroupOf max4Subgroup) eR
      ((pCore_isPGroup.le_sylow_of_normal (S.subtype hS)).trans hSR)]
    exact map_subtype_le _
  have hEpre : E.subgroupOf max4Subgroup ≤ a5Preimage :=
    (comap_mono hER).trans hRpre
  have hc := CubicCore.subgroup_core_centralizer_card (E.subgroupOf max4Subgroup)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe (hER.trans hR)).toEquiv]) hEpre
  let := NormalEight.elementary_eight
  let := NormalEight.normal_eight
  have h8 : NormalEight.eight ≤ pCore 2 max4Subgroup :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 _⟩
  have hCE : NormalEight.eight ≤ centralizer (E.subgroupOf max4Subgroup : Set max4Subgroup) :=
    le_centralizer_iff.mp ((comap_mono hER).trans (perfect_five_centralizes_eight (R.subgroupOf max4Subgroup) eR))
  exact (eq_of_le_of_card_ge (le_inf h8 hCE) (by rwa [NormalEight.card_eight])).symm

/-- The fixed-core identity follows under every specified simultaneous max4 transport. -/
theorem jankoFour_same_cubic_fixed_core_map (S : Sylow 2 Model) (R E : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hE : Nat.card E = 3) (hER : E ≤ R) (a : MulAut Model)
    (hS : (S : Subgroup Model).map a.toMonoidHom ≤ max4Subgroup) :
    pCore 2 max4Subgroup ⊓
      centralizer ((E.map a.toMonoidHom).subgroupOf max4Subgroup : Set max4Subgroup) =
        NormalEight.eight := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot a.injective]
    infer_instance
  let d := a.subgroupMap R
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  exact jankoFour_same_cubic_fixed_core (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (R.map a.toMonoidHom) (E.map a.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl a.toMonoidHom)
    ((map_mono hn).trans (R.le_normalizer_map a.toMonoidHom)) (he.of_mulEquiv e.symm)
    ((card_map_of_injective a.injective).trans hE) (map_mono hER) hS

private theorem exists_max4_marking (S : Sylow 2 Model) :
    ∃ a : MulAut Model, (S : Subgroup Model).map a.toMonoidHom ≤ max4Subgroup := by
  have hidx : ¬2 ∣ max4Subgroup.index := by
    intro hh
    have hd := Nat.mul_dvd_mul max4_twoPart_dvd hh
    rw [max4Subgroup.card_mul_index] at hd
    exact OuterReduction.OddIndex.model_two_part_bound (by convert hd using 1; norm_num)
  let P : Sylow 2 max4Subgroup := default
  let Q := (P.isPGroup'.map max4Subgroup.subtype).toSylow (by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hidx)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S Q
  refine ⟨MulAut.conj g,?_⟩
  have he := congrArg Sylow.toSubgroup hg
  exact he.trans_le (map_subtype_le _)

open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The original native map supplies the fixed-core identity at an actual max4 marking. -/
theorem normal_jankoFour_native_cubic_fixed_core
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
      Nat.card ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) = 9 * 2^21 ∧
      ∃ a : MulAut Janko4.Model,
        (S : Subgroup Janko4.Model).map a.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup ∧
        pCore 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup ⊓
          centralizer ((E.map a.toMonoidHom).subgroupOf
            Janko4.LocalStructure.SymmetricLinear.max4Subgroup :
              Set Janko4.LocalStructure.SymmetricLinear.max4Subgroup) =
            Janko4.LocalStructure.SymmetricLinear.NormalEight.eight := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    hmax1,hD,hDE,hdis,h9,hel,hK⟩ :=
    normal_jankoFour_native_cubic_pair h hH hgen c hY hescape hR C hC hRC e
  obtain ⟨a,hSa⟩ := exists_max4_marking S
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    hmax1,hD,hDE,hdis,h9,hel,hK,a,hSa,
    jankoFour_same_cubic_fixed_core_map S _ _ hl hSR hfour hE hER a hSa⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
