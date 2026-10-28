module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpInvolution
public import CFSG.Quasithin.ChapterI.Section03.MathieuPumpup

/-!
# The original exterior cubic has a single containing two-component

Apply I.3.2 inside C_G(x) to the constructed involution r and the unchanged
full cubic residual. The literal simultaneous centralizer supplies the
ordinary component input. The Mathieu-square exclusion removes the
exchanged pair and produces one r-invariant two-component containing the
full residual, using the actual odd-E normal closure.

The original J₄ cover, cubic marking, exterior module of order at least
1024, sixteen fixed vectors and Mathieu triple-cover quotient are retained.
Equality with the containing component, the p.612 commutator contradiction
and the separate p.623 odd-local comparison remain required.
Source: Aschbacher--Smith 4.2.13, printed p.612, and I.3.2, p.415.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02 ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Construct the original cubic residual’s containing two-component in C_G(x). -/
theorem exterior_pushingUp_cubic_single_pumpup
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3)
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
      Rg ≤ X ∧ B ≤ E ∧ E.IsTwoComponent ∧
        E.map (MulAut.conj t).toMonoidHom = E := by
  let x : G := ((k : H) : G)
  let X := centralizer ({x} : Set G)
  let C := centralizer ({r} : Set G) ⊓ X
  let R := solvableResidual (centralizer ({k} : Set K))
  let Rg := R.map (H.subtype.comp (K.subtype.comp
    (centralizer ({k} : Set K)).subtype))
  have hp := exterior_pushingUp_cubic_residual_in_involution_centralizer
    s h hw K hK hn e k hk r hKC hKN
  have hx : x ∈ centralizer ({r} : Set G) := hKC (mem_map_of_mem H.subtype k.property)
  have ht : r ∈ X := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hx).symm
  let t : X := ⟨r,ht⟩
  have hRX : Rg ≤ X := hp.1.1.trans inf_le_right
  let B := Rg.subgroupOf X
  let Ct := centralizer ({t} : Set X)
  have hBCt : B ≤ Ct := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp (hp.1.1 hb).1))
  let U := B.subgroupOf Ct
  let f : Ct →* C := (X.subtype.comp Ct.subtype).codRestrict C (fun b =>
    ⟨mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp b.property)),b.val.property⟩)
  let eq : R ≃* U :=
    (R.equivMapOfInjective _
      (H.subtype_injective.comp (K.subtype_injective.comp
        (centralizer ({k} : Set K)).subtype_injective))).trans
      ((subgroupOfEquivOfLe hRX).symm.trans (subgroupOfEquivOfLe hBCt).symm)
  have hU : IsComponent Ct U := by
    refine ⟨hp.1.2.1.comap f,?_⟩
    let := exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk
    exact IsQuasisimple.of_mulEquiv eq
  obtain ⟨eqR⟩ := exterior_pushingUp_cubic_residual_center_quotient s h hw K hK hn e k hk
  let eqU := (centerQuotientCongr eq).symm.trans eqR
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
  have hm := mathieu_involution_pumpup (h.simpleQTKE.quasithin.subgroup X)
    (h.simpleQTKE.properK X hproper) t ((orderOf_coe t).symm.trans hr) U hU eqU
  rw [map_subgroupOf_eq_of_le hBCt] at hm
  exact ⟨ht,hRX,hm⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource


namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The unchanged exterior configuration with a single containing
two-component at the same cubic and the same selected involution. -/
@[expose] def ExteriorPushingUpPumpupResidualCase (s : SylowExteriorMarking D)
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
              Rg ≤ X ∧ B ≤ E ∧ E.IsTwoComponent ∧
                E.map (MulAut.conj t).toMonoidHom = E

/-- Preserve the whole original configuration while removing I.3.2's
exchanged-component branch at its prescribed exterior cubic. -/
theorem exterior_pushingUp_pumpup_residual_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpInvolutionResidualCase s A) :
    ExteriorPushingUpPumpupResidualCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    exterior_pushingUp_cubic_single_pumpup s h hw K hK hn e k hk r ho hKc.1 hKn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
