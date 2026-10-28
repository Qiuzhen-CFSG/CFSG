module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpOrdinaryPumpup
public import CFSG.Quasithin.ChapterI.Section03.MathieuCentralCubic

/-!
# Equality with the original exterior cubic residual

The original cubic belongs to the full residual and is central in its full
centralizer. It is therefore a central element of order three in the
containing ordinary component. The remaining Lie families have no such
covering kernel (with the exceptional small fields excluded by order).
A centered McL cover has local three-rank at least three, contradicting
quasithinness. Thus proper containment is impossible, and the unchanged
residual is a normal ordinary component of the full cubic centralizer.
Consequently all commutators of the chosen involution with cubic-fixing
elements centralize this residual, supplying the normality side of the
printed commutator contradiction.

All original covers, quotient maps, the PSL₅(2) section and the exterior
module of order at least 1024 are retained. The p.612 commutator argument
and the separate p.623 odd-local comparison remain to be constructed.
Source: Aschbacher--Smith 4.2.13, printed p.612; A.2.19, p.41.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02 ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original full cubic residual equals its normal ordinary overcomponent. -/
theorem exterior_pushingUp_cubic_component_equality
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
        B = E := by
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
  have hkR := (exterior_pushingUp_full_cubic_residual s h hw K hK hn e k hk).2.2.2.1
  let x : X := ⟨((k : H) : G),mem_centralizer_singleton_iff.mpr rfl⟩
  have hxB : x ∈ B := by
    change ((k : H) : G) ∈ Rg
    exact mem_map_of_mem _ hkR
  let z : E := ⟨x,hBE hxB⟩
  have hz : z ∈ center E := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp y.val.property))
  have hz3 : orderOf z = 3 := by
    rw [←orderOf_coe z,←orderOf_coe x]
    exact (orderOf_coe (k : H)).trans ((orderOf_coe k).trans hk)
  have h3 : 3 ∣ Nat.card (center E) := by
    rw [←hz3,orderOf_coe (⟨z,hz⟩ : center E)]
    exact orderOf_dvd_natCard _
  refine ⟨ht,hRX,hBE,hE,hEN,hinv,hm,?_⟩
  rcases hcase with heq | ⟨a,ha,hact,haq,hQ,heQ⟩
  · exact heq
  · have hf : HasMathieuFixedComponent (E ⧸ center E) := ⟨_,haq,_,hQ,heQ⟩
    exact (no_central_cubic_mathieu_fixed_component
      ((h.simpleQTKE.quasithin.subgroup X).subgroup E) h3 hf hm).elim

/-- The full original residual is a normal ordinary component of the full
cubic centralizer, with the literal ambient inclusion unchanged. -/
theorem exterior_pushingUp_cubic_residual_normal_component
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
    IsComponentIn Rg X ∧ (Rg.subgroupOf X).Normal := by
  obtain ⟨ht,hRX,hBE,hE,hEN,hinv,hm,heq⟩ :=
    exterior_pushingUp_cubic_component_equality s h hw K hK hn e k hk hfix r hr hKC hKN
  exact ⟨⟨hRX,heq.symm ▸ hE⟩,heq.symm ▸ hEN⟩

/-- Every commutator of the chosen involution with an element fixing the
original cubic centralizes its full residual. This is the normality side
of the p.612 contradiction; the commutator isomorphism still has to be constructed. -/
theorem exterior_pushingUp_cubic_residual_commutator_centralizes
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
    ⁅zpowers r, X⁆ ≤ centralizer (Rg : Set G) := by
  obtain ⟨hR,hnR⟩ := exterior_pushingUp_cubic_residual_normal_component
    s h hw K hK hn e k hk hfix r hr hKC hKN
  let R := solvableResidual (centralizer ({k} : Set K))
  let Rg := R.map (H.subtype.comp (K.subtype.comp
    (centralizer ({k} : Set K)).subtype))
  let X := centralizer ({((k : H) : G)} : Set G)
  have hXN : X ≤ normalizer (Rg : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hR.1).mp hnR
  have hXRc := hXN.trans (normalizer_le_normalizer_centralizer Rg)
  have hRgK : Rg ≤ K.map H.subtype := by
    rintro y ⟨c,hc,rfl⟩
    exact mem_map_of_mem H.subtype c.val.property
  have hz : zpowers r ≤ centralizer (Rg : Set G) := by
    apply zpowers_le.mpr
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hKC (hRgK hy))
  exact (commutator_mono hz le_rfl).trans
    ((le_normalizer_iff_commutator_le_left).mp hXRc)


/-- The unchanged exterior configuration with full residual equality at the original cubic. -/
@[expose] def ExteriorPushingUpComponentEqualityCase (s : SylowExteriorMarking D)
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
            IsComponentIn Rg X ∧ (Rg.subgroupOf X).Normal ∧
              ⁅zpowers r, X⁆ ≤ centralizer (Rg : Set G)

/-- The original configuration with the proved full residual equality. -/
theorem exterior_pushingUp_component_equality_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpInvolutionResidualCase s A) :
    ExteriorPushingUpComponentEqualityCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn⟩ := hj
  obtain ⟨hRcX,hRnX⟩ := exterior_pushingUp_cubic_residual_normal_component
    s h hw K hK hn e k hk (by simpa only [hkx] using hfix) r ho hKc.1 hKn
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,exterior_pushingUp_cubic_residual_commutator_centralizes s h hw K hK hn e k hk
      (by simpa only [hkx] using hfix) r ho hKc.1 hKn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
