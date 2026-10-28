module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpPumpup
public import CFSG.Quasithin.ChapterI.Section03.MathieuOvercomponent
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleModels

/-!
# The exterior cubic lies in a normal ordinary component

The sixteen exterior cubic-fixed vectors bound every odd-prime core.
The original full Mathieu residual centralizes the odd core, so its
single containing two-component is ordinary. The Mathieu-square section
obstruction makes that containing component normal in C_G(x).

If containment is proper, the selected involution acts faithfully on the
component's literal central quotient, a Theorem B model. The image of the
original residual remains a Mathieu component of the full quotient fixed
group. All quotient maps, the original J₄ cover, exterior module of order
at least 1024, PSL₅(2) section, cubic and selected involution are retained.

The proper-model exclusion and p.612 commutator contradiction still remain;
the p.623 odd-local endgame is separate. Source: Aschbacher--Smith 4.2.13,
printed p.612, with A.1.9, A.1.28 and I.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02 ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Construct the normal ordinary overcomponent and the literal proper-containment alternative. -/
theorem exterior_pushingUp_cubic_ordinary_pumpup
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
            Nonempty ((Q ⧸ center Q) ≃* Sporadic.Mathieu.M22)) := by
  let x : G := ((k : H) : G)
  let X := centralizer ({x} : Set G)
  let C := centralizer ({r} : Set G) ⊓ X
  let R := solvableResidual (centralizer ({k} : Set K))
  let Rg := R.map (H.subtype.comp (K.subtype.comp
    (centralizer ({k} : Set K)).subtype))
  obtain ⟨ht,hRX,hBE,hE,hinv⟩ := exterior_pushingUp_cubic_single_pumpup
    s h hw K hK hn e k hk r hr hKC hKN
  let t : X := ⟨r,ht⟩
  let B := Rg.subgroupOf X
  let E := componentOrbit B (oddELayer X)
  let eq : R ≃* B :=
    (R.equivMapOfInjective _
      (H.subtype_injective.comp (K.subtype_injective.comp
        (centralizer ({k} : Set K)).subtype_injective))).trans
      (subgroupOfEquivOfLe hRX).symm
  let := exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eq
  obtain ⟨eqR⟩ := exterior_pushingUp_cubic_residual_center_quotient s h hw K hK hn e k hk
  let eqB := (centerQuotientCongr eq).symm.trans eqR
  let U := V ⊓ X
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 (U.subgroupOf X) := IsElementaryAbelian.subgroupOf
    (show U ≤ X from inf_le_right)
  have hsize : 8 < Nat.card (U.subgroupOf X) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ≤ X from inf_le_right)).toEquiv]
    change 16 ≤ Nat.card U at hfix
    omega
  have he : IsComponent X E := mathieu_orbit_isComponent
    (h.simpleQTKE.quasithin.subgroup X) (U.subgroupOf X) hsize B eqB hE
  have hproper : X ≠ ⊤ := by
    intro htX
    let := h.simpleQTKE.simple
    have hkG : orderOf x = 3 :=
      (orderOf_coe (k : H)).trans ((orderOf_coe k).trans hk)
    have hz : x ∈ center G := by
      apply mem_center_iff.mpr
      intro y
      exact mem_centralizer_singleton_iff.mp (show y ∈ X from htX ▸ mem_top y)
    have hcbot : center G = ⊥ := by
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | hh
      · exact hb
      · exact (h.simpleQTKE.nonabelian (center_eq_top_iff.mp hh)).elim
    have hx1 : x = 1 := by simpa only [hcbot,mem_bot] using hz
    rw [hx1,orderOf_one] at hkG
    omega
  have hXK := h.simpleQTKE.properK X hproper
  have heN := component_containing_mathieu_normal
    (h.simpleQTKE.quasithin.subgroup X) hXK B E eqB he hBE
  let := he.2
  have hm := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    ((h.simpleQTKE.quasithin.subgroup X).subgroup E) (hXK.subgroup E)
  refine ⟨ht,hRX,hBE,he,heN,hinv,hm,?_⟩
  have hp := exterior_pushingUp_cubic_residual_in_involution_centralizer
    s h hw K hK hn e k hk r hKC hKN
  let Ct := centralizer ({t} : Set X)
  have hBCt : B ≤ Ct := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp (hp.1.1 hb).1))
  let F := B.subgroupOf Ct
  let f : Ct →* C := (X.subtype.comp Ct.subtype).codRestrict C (fun b =>
    ⟨mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp b.property)),b.val.property⟩)
  have hF : IsComponent Ct F := ⟨hp.1.2.1.comap f,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBCt).symm⟩
  have hbE : F.map Ct.subtype ≤ E := by
    rw [map_subgroupOf_eq_of_le hBCt]
    exact hBE
  have hcase := fixed_component_eq_or_involution t ((orderOf_coe t).symm.trans hr)
    F hF E he hbE hinv
  rw [map_subgroupOf_eq_of_le hBCt] at hcase
  rcases hcase with heq | ⟨a,haw,hact,haq⟩
  · exact Or.inl heq
  · have hf := fixed_component_in_overgroup t F hF E hbE a hact
    rw [map_subgroupOf_eq_of_le hBCt] at hf
    have hquot := fixed_mathieu_central_quotient a (B.subgroupOf E) hf
      ((centerQuotientCongr (subgroupOfEquivOfLe hBE)).trans eqB)
    exact Or.inr ⟨a,haw,hact,haq,hquot⟩

/-- The unchanged exterior configuration with a normal ordinary containing
component at the same cubic and the same selected involution. -/
@[expose] def ExteriorPushingUpOrdinaryPumpupCase (s : SylowExteriorMarking D)
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
                    Nonempty ((Q ⧸ center Q) ≃* Sporadic.Mathieu.M22))

/-- The original configuration with its normal ordinary overcomponent and faithful involution alternative. -/
theorem exterior_pushingUp_ordinary_pumpup_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpInvolutionResidualCase s A) :
    ExteriorPushingUpOrdinaryPumpupCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    exterior_pushingUp_cubic_ordinary_pumpup s h hw K hK hn e k hk
      (by simpa only [hkx] using hfix) r ho hKc.1 hKn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
