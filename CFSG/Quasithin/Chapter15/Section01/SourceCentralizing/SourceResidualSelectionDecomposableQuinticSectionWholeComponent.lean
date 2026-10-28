module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNormalizerFullSource

/-!
# The normal component moves the entire original quintic section

The exact original offender cost saturates the binary displacement bound.
Its moved space is therefore the whole marked E/Uc plane. The normal
component contains that plane, and the original conjugates of E generate F.
Consequently the literal F/Uc section is fully moved and belongs to Irr⁺
for this same component. No faithfulness is transferred to an arbitrary
quotient and no component is lifted to the original ambient group.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The same normal component moves the whole literal partner section, and
its original marked plane is exactly the displacement of the original V-image. -/
theorem PreparedChosenModule.decomposable_five_core_or_whole_section_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      V ≤ Mc.pCoreIn 2 ∨
        ∃ he : IsElementaryAbelian 2 F,
          letI := he
          ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ Uc.subgroupOf F)),
            ∃ dF : BinaryConjugationSection Mc F Uc ρ,
            Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
            (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
              commutatorPreimage Mc F Uc ∧
            Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
              (commutatorPreimage Mc F Uc).relIndex V ∧
            pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            IsQuadratic (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            Module.finrank (ZMod 2) (subspaceCommutator
              (Representation.BinaryOffender.imageRepresentation ρ) ⊤
              (actionSubgroup ρ (V.subgroupOf Mc))) ≤ 2 ∧
            IsMinimalBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            ((rank (actionSubgroup ρ (V.subgroupOf Mc)) = 2 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 1) ∨
             (rank (actionSubgroup ρ (V.subgroupOf Mc)) = 4 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 2)) ∧
            let A := actionSubgroup ρ (V.subgroupOf Mc)
            A ≤ centralizer (fittingSubgroup (Representation.BinaryOffender.actionImage ρ) :
              Set (Representation.BinaryOffender.actionImage ρ)) ∧
            ∃ K, IsComponent (Representation.BinaryOffender.actionImage ρ) K ∧ ⁅K,A⁆ = K ∧
              K ≤ normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              (K.subgroupOf (normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)))).Normal ∧
              IsIrrPlus (Representation.BinaryOffender.imageRepresentation ρ) K
                (ChapterB.QuasisimpleSource.moved (Representation.BinaryOffender.imageRepresentation ρ) K) ∧
              ChapterB.QuasisimpleSource.SmallMoved.ActorList K ∧
              normalizer (A : Set (Representation.BinaryOffender.actionImage ρ)) ≤
                normalizer (K : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              actionSubgroup ρ ((T : Subgroup G).subgroupOf Mc) ≤
                normalizer (K : Set (Representation.BinaryOffender.actionImage ρ)) ∧ K.Normal ∧
              dF.imageSpace (thompsonFixed T V) = subspaceCommutator
                (Representation.BinaryOffender.imageRepresentation ρ) ⊤ A ∧
              ChapterB.QuasisimpleSource.moved
                (Representation.BinaryOffender.imageRepresentation ρ) K = ⊤ ∧
              IsIrrPlus (Representation.BinaryOffender.imageRepresentation ρ) K ⊤ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
      hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hNA,hTK,hn⟩ :=
    h.decomposable_five_core_or_normal_section_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact (hVQ hcore).elim
  right
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le (hUE.trans inf_le_left))).trans hCMc
  have hEF : E ≤ F := le_conjugateSpanBy E C
  have hVF : ⁅V,F⁆ ≤ E :=
    ((h.decomposable_five_partner_core_alternatives
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ).2.2.2.2.1
  have hdim : Module.finrank (ZMod 2) (dF.imageSpace E) = 2 := by
    apply dF.imageSpace_finrank_of_index E hEF 2
    have hm := (Uc.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hm
    change Uc.relIndex E * Nat.card Uc = Nat.card E at hm
    rw [hcU,s.fixed_card] at hm
    change Uc.relIndex E = 2 ^ 2
    norm_num only [Nat.reducePow]
    omega
  have hmove : subspaceCommutator σ ⊤ A ≤ dF.imageSpace E := by
    change subspaceCommutator σ ⊤ ((V.subgroupOf Mc).map
      (Representation.BinaryOffender.actionHom ρ)) ≤ _
    rw [←subspaceCommutator_comp_map]
    change subspaceCommutator ρ ⊤ (V.subgroupOf Mc) ≤ _
    have he := dF.imageSpace_commutator V F hVMc le_rfl
    rw [dF.imageSpace_self] at he
    rw [←he]
    exact dF.imageSpace_mono hVF
  have hfullmove : dF.imageSpace E = subspaceCommutator σ ⊤ A := by
    apply (Submodule.eq_of_le_of_finrank_eq hmove ?_).symm
    change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2 at hplane
    have hb := rank_le_fixedCodim_mul_dual σ hfaith A
    rw [fixedCodim_dual_eq_moved_finrank] at hb
    rw [hdim]
    rcases hcost with ⟨hr,hc⟩ | ⟨hr,hc⟩
    · rw [hr,hc,one_mul] at hb
      omega
    · rw [hr,hc] at hb
      omega
  let : K.Normal := hn
  let : IsQuasisimple K := hK.2
  have hKn : K ≠ ⊥ := by
    intro he
    apply hirr.not_le_fixedSpace σ
    rw [he]
    simp
  have hAK : subspaceCommutator σ ⊤ A ≤ subspaceCommutator σ ⊤ K :=
    hmin.moved_le_moved_perfect σ hfaith hKn hplane hKA
  have hstable : (⊤ : Subgroup (Representation.BinaryOffender.actionImage ρ)) ≤
      subspaceStabilizer σ (subspaceCommutator σ ⊤ K) :=
    subspaceCommutator_invariant_normalizer σ
      (le_subspaceStabilizer σ ⊤ (by intros; trivial))
      (by rw [normalizer_eq_top])
  let P : Subrepresentation ρ :=
    { toSubmodule := subspaceCommutator σ ⊤ K
      apply_mem_toSubmodule := fun g v hv =>
        (hstable (mem_top (Representation.BinaryOffender.actionHom ρ g)) v).2 hv }
  have hgen : F = conjugateSpanBy E Mc := le_antisymm
    (conjugateSpanBy_mono le_rfl hCMc) (conjugateSpanBy_le hEF dF.normalized)
  have hwhole : ChapterB.QuasisimpleSource.moved σ K = ⊤ :=
    dF.generated_image_le E hgen P (hfullmove ▸ hAK)
  exact ⟨heF,ρ,dF,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
    hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hNA,hTK,hn,hfullmove,hwhole,hwhole ▸ hirr⟩

end CFSG.Quasithin.Chapter15.Section01
