module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpOrdinaryPumpup
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedRankTwoModels

/-!
# The remaining proper models at the original exterior cubic

Apply the five rank-two exclusions to the faithful involution on the
containing component's central quotient. Proper containment now leaves
only the three odd Lie families, binary PSU₄, and McL.

The original cubic, involution, full J₄ cover, PSL₅(2) section and exterior
module of order at least 1024 remain on the same literal maps. OddNormalizer
applies this construction to the actual Hall counterexample. Equality with
the residual and the two distinct source endgames remain open.
Source: Aschbacher--Smith 4.2.13, printed p.612; the separate odd-local
argument is on printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02 ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Apply the rank-two exclusions to the same proper containing component. -/
theorem exterior_pushingUp_cubic_rank_two_proper_models
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3)
    (hfix : 16 ≤ Nat.card (V ⊓ centralizer ({((k : H) : G)} : Set G) : Subgroup G))
    (r : G) (hr : orderOf r = 2)
    (hKC : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hKN : ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal) :
    let R := solvableResidual (centralizer ({k} : Set K))
    let Rg := R.map (H.subtype.comp (K.subtype.comp
      (centralizer ({k} : Set K)).subtype))
    let X := centralizer ({((k : H) : G)} : Set G)
    ∃ ht : r ∈ X,
      let t : X := ⟨r,ht⟩
      let B := Rg.subgroupOf X
      let E := componentOrbit B (oddELayer X)
      Rg ≤ X ∧ B ≤ E ∧ IsComponent X E ∧ E.Normal ∧
        E.map (MulAut.conj t).toMonoidHom = E ∧
        ChapterA.Section02.IsTheoremBModel (E ⧸ center E) ∧
        (B = E ∨ ∃ a : MulAut E, orderOf a = 2 ∧
          (∀ y : E, (a y : X) = t * (y : X) * t⁻¹) ∧
          orderOf (quotientAut (center E) a) = 2 ∧
          let Q := (B.subgroupOf E).map (QuotientGroup.mk' (center E))
          IsComponentIn Q (quotientAut (center E) a).fixedSubgroup ∧
            Nonempty ((Q ⧸ center Q) ≃* Sporadic.Mathieu.M22) ∧
          MathieuProperModelResidue (E ⧸ center E)) := by
  obtain ⟨ht,hRX,hBE,hE,hEN,hinv,hm,hcase⟩ := exterior_pushingUp_cubic_ordinary_pumpup
    s h hw K hK hn e k hk hfix r hr hKC hKN
  let R := solvableResidual (centralizer ({k} : Set K))
  let Rg := R.map (H.subtype.comp (K.subtype.comp
    (centralizer ({k} : Set K)).subtype))
  let X := centralizer ({((k : H) : G)} : Set G)
  let B := Rg.subgroupOf X
  let E := componentOrbit B (oddELayer X)
  let := hE.2
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : Group.IsPerfect (E ⧸ center E) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  refine ⟨ht,hRX,hBE,hE,hEN,hinv,hm,?_⟩
  rcases hcase with heq | ⟨a,ha,hact,haq,hQ,heQ⟩
  · exact Or.inl heq
  · have hf : HasMathieuFixedComponent (E ⧸ center E) := ⟨_,haq,_,hQ,heQ⟩
    exact Or.inr ⟨a,ha,hact,haq,hQ,heQ,hf.proper_model_residue hm⟩

/-- The unchanged exterior configuration with the reduced proper-component
model list at the same cubic and the same selected involution. -/
@[expose] def ExteriorPushingUpRankTwoProperModelsCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        let R := solvableResidual (centralizer ({k} : Set K))
        (IsQuasisimple R ∧ Nonempty ((R ⧸ center R) ≃* Sporadic.Mathieu.M22) ∧
          IsComponent (centralizer ({(k : H)} : Set H))
            (R.map (K.subtype.elementCentralizerMap k)) ∧
          R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M) ∧
        let I := F ⊔ J.pCoreIn 2
        I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
          ∃ (r : G) (H' W' : Subgroup G),
            r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
            K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
            centralizer ({r} : Set G) ≤ H' ∧ Witness L V A I H' W' ∧
            IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
            ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal ∧
            let Rg := R.map (H.subtype.comp (K.subtype.comp
              (centralizer ({k} : Set K)).subtype))
            let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg C ∧ (Rg.subgroupOf C).Normal ∧
            let X := centralizer ({((k : H) : G)} : Set G)
            ∃ ht : r ∈ X,
              let t : X := ⟨r,ht⟩
              let B := Rg.subgroupOf X
              let E := componentOrbit B (oddELayer X)
              Rg ≤ X ∧ B ≤ E ∧ IsComponent X E ∧ E.Normal ∧
                E.map (MulAut.conj t).toMonoidHom = E ∧
                ChapterA.Section02.IsTheoremBModel (E ⧸ center E) ∧
                (B = E ∨ ∃ a : MulAut E, orderOf a = 2 ∧
                  (∀ y : E, (a y : X) = t * (y : X) * t⁻¹) ∧
                  orderOf (quotientAut (center E) a) = 2 ∧
                  let Q := (B.subgroupOf E).map (QuotientGroup.mk' (center E))
                  IsComponentIn Q (quotientAut (center E) a).fixedSubgroup ∧
                    Nonempty ((Q ⧸ center Q) ≃* Sporadic.Mathieu.M22) ∧
                    MathieuProperModelResidue (E ⧸ center E))

/-- The original configuration with its proved proper-component model exclusions. -/
theorem exterior_pushingUp_rank_two_proper_models_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpInvolutionResidualCase s A) :
    ExteriorPushingUpRankTwoProperModelsCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    exterior_pushingUp_cubic_rank_two_proper_models s h hw K hK hn e k hk
      (by simpa only [hkx] using hfix) r ho hKc.1 hKn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
