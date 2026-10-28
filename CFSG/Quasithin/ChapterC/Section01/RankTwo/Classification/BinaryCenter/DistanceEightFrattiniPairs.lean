module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightFrattini

/-!
# Both original doubled Frattini sections

The equivariant core equivalence transports the Frattini subgroup and its
centralizer. Restricting to that centralizer gives the doubled-dual middle
section; the full core map gives the doubled-natural upper section. Both use
the same CommonFacts marking as the single-dual Frattini/center section.
All actions are those of the original component, and all denominators are
the literal Frattini subgroup or its centralizer.

The only extra premise is the exact whole fixed-factor equality, whose
producer is qt-ms93-distance-eight-fixed-factor. The SmallMSPair application
in MarkedMS/LinearThree/DistanceEightFrattini consumes both sections;
qt-rank-two-ms93 retains final C.1.34 assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(vi)--(vii), printed p.895;
Aschbacher--Smith C.1.34(4), printed p.136.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
open DistanceEight.CoreFactors
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)

/-- The two original doubled sections, with the same marking as the single
Frattini/center dual section. -/
theorem frattini_pairSectionModels_of_fixedFactor
    (hb : 4 < s.geometry.b s.reduction.radical)
    (hfixed : core s.reduction.radical (alpha s.reduction.radical) ⊓ centralizer
      (Ltilde s.reduction.radical (alpha s.reduction.radical) : Set (FreeAmalgam s.reduction.radical)) =
        H s.reduction.radical (alpha s.reduction.radical)) :
    let Phi := frattiniIn (msQ L R)
    let D := msQ L R ⊓ centralizer (Phi : Set J)
    let a := linearThreeActor (h.quotientEquiv.trans common.natural.marking)
    let v := Representation.specialLinearNatural (k := ZMod 2) 3
    HasSectionModel L D Phi a (v.dual.prod v.dual) ∧
      HasSectionModel L (msQ L R) D a (v.prod v) := by
  dsimp only
  let r := s.reduction.radical
  let C := core r (alpha r)
  let Q₀ := commutatorCore L
  let Phi := (frattini Q₀).map Q₀.subtype
  let Z₀ := (center Q₀).map Q₀.subtype
  let PhiC := (frattini C).map C.subtype
  let ZC := (center C).map C.subtype
  let e := h.quotientEquiv.trans common.natural.marking
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨d⟩ := Center.frattini_centralizer_marked_pair_of_fixedFactor common earlier hfixed
  obtain ⟨n⟩ := Center.core_frattini_centralizer_marked_pair_of_fixedFactor common earlier hfixed
  have hQ : msQ L R = Q₀ := by
    have hc : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,h.sup_eq_top,hc]
  rw [hQ]
  let D := Q₀ ⊓ centralizer (Phi : Set J)
  let DC := C ⊓ centralizer (PhiC : Set (FreeAmalgam r))
  change HasSectionModel L D Phi (linearThreeActor e) (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) ∧
    HasSectionModel L Q₀ D (linearThreeActor e) (BinaryLinearThree.W.prod BinaryLinearThree.W)
  let E : Q₀ ≃* C := h.intrinsicCoreEquiv.symm.trans s.intrinsicCoreEquiv
  have hE (l : L) (x y : Q₀)
      (hy : (y : J) = l * (x : J) * (l : J)⁻¹) :
      (E y : FreeAmalgam r) =
        embedM r (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) *
          (E x : FreeAmalgam r) *
          (embedM r (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l))⁻¹ := by
    have hy' : y = h.coreConjugate l x := by
      apply Subtype.ext
      rw [h.coreConjugate_val]
      exact hy
    have hi : h.intrinsicCoreEquiv.symm y =
        blockConjugate L l (h.intrinsicCoreEquiv.symm x) := by
      apply h.intrinsicCoreEquiv.injective
      rw [MulEquiv.apply_symm_apply,h.intrinsicCoreEquiv_conjugate,
        MulEquiv.apply_symm_apply,hy']
    change s.componentEmbedding (h.intrinsicCoreEquiv.symm y : L) = _
    rw [hi]
    change s.componentEmbedding (l * (h.intrinsicCoreEquiv.symm x : L) * l⁻¹) = _
    rw [map_mul,map_mul,map_inv]
    rfl
  let ePhi : Phi ≃* PhiC :=
    ((frattini Q₀).equivMapOfInjective Q₀.subtype Q₀.subtype_injective).symm.trans
      (((E.subgroupMap (frattini Q₀)).trans (MulEquiv.subgroupCongr (frattini_map_equiv E))).trans
        ((frattini C).equivMapOfInjective C.subtype C.subtype_injective))
  have hePhi (x : Phi) : (ePhi x : FreeAmalgam r) = E ⟨x,map_subtype_le _ x.property⟩ := by
    change (E (((frattini Q₀).equivMapOfInjective Q₀.subtype
      Q₀.subtype_injective).symm x).val : FreeAmalgam r) = _
    apply congrArg (fun q : Q₀ => (E q : FreeAmalgam r))
    exact Subtype.ext (congrArg (fun q : Phi => (q : J))
      (((frattini Q₀).equivMapOfInjective Q₀.subtype Q₀.subtype_injective).apply_symm_apply x))
  have hcentral (x : Q₀) :
      (E x : FreeAmalgam r) ∈ centralizer (PhiC : Set (FreeAmalgam r)) ↔
        (x : J) ∈ centralizer (Phi : Set J) := by
    constructor
    · intro hx p hp
      have hh := hx (ePhi ⟨p,hp⟩) (ePhi ⟨p,hp⟩).property
      rw [hePhi] at hh
      have hcomm : (⟨p,map_subtype_le _ hp⟩ : Q₀) * x =
          x * ⟨p,map_subtype_le _ hp⟩ := by
        apply E.injective
        rw [map_mul,map_mul]
        exact Subtype.ext hh
      exact congrArg Q₀.subtype hcomm
    · intro hx p hp
      obtain ⟨v,hv⟩ := ePhi.surjective ⟨p,hp⟩
      have hh := congrArg (fun q : PhiC => (q : FreeAmalgam r)) hv
      rw [hePhi] at hh
      change (E ⟨v,map_subtype_le _ v.property⟩ : FreeAmalgam r) = p at hh
      rw [← hh]
      have he : (⟨v,map_subtype_le _ v.property⟩ : Q₀) * x =
          x * ⟨v,map_subtype_le _ v.property⟩ := Subtype.ext (hx v v.property)
      exact congrArg C.subtype (by simpa only [map_mul] using congrArg E he)
  have hED : (D.subgroupOf Q₀).map E.toMonoidHom = DC.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(E y).property,(hcentral y).mpr hy.2⟩
    · intro hx
      refine ⟨E.symm x,?_,E.apply_symm_apply x⟩
      refine ⟨(E.symm x).property,(hcentral _).mp ?_⟩
      rw [E.apply_symm_apply]
      exact hx.2
  let eD : D ≃* DC :=
    (subgroupOfEquivOfLe (show D ≤ Q₀ from inf_le_left)).symm.trans
      (((E.subgroupMap (D.subgroupOf Q₀)).trans (MulEquiv.subgroupCongr hED)).trans
        (subgroupOfEquivOfLe (show DC ≤ C from inf_le_left)))
  have heD (x : D) : (eD x : FreeAmalgam r) = E ⟨x,x.property.1⟩ := rfl
  have hPhi (x : Q₀) : (E x : FreeAmalgam r) ∈ PhiC ↔ (x : J) ∈ Phi := by
    constructor
    · rintro ⟨y,hy,he⟩
      have he' : y = E x := Subtype.ext he
      rw [he',← frattini_map_equiv E] at hy
      obtain ⟨z,hz,hzx⟩ := hy
      have hzx' : z = x := E.injective hzx
      exact mem_map_of_mem Q₀.subtype (hzx' ▸ hz)
    · rintro ⟨y,hy,he⟩
      have he' : y = x := Subtype.ext he
      subst y
      refine ⟨E x,?_,rfl⟩
      rw [← frattini_map_equiv E]
      exact mem_map_of_mem E.toMonoidHom hy
  let := h.component_normal
  let : Q₀.Normal := commutator_normal _ _
  have hLQ : L ≤ normalizer Q₀ := by rw [normalizer_eq_top]; exact le_top
  have hLPhi : L ≤ normalizer Phi := hLQ.trans
    (normalizer_le_normalizer_characteristic_image Q₀ (frattini Q₀))
  have hLD : L ≤ normalizer D := le_normalizer_inf hLQ
    (hLPhi.trans (normalizer_le_normalizer_centralizer Phi))
  constructor
  · let p := d.quotient.comp eD.toMonoidHom
    have hpk : p.ker = Phi.subgroupOf D := by
      ext x
      change eD x ∈ d.quotient.ker ↔ _
      rw [d.kernel]
      exact hPhi ⟨x,x.property.1⟩
    let f := BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv
    let f₂ := f.prodCongr f
    let q := f₂.toAddEquiv.toMultiplicative.toMonoidHom.comp p
    have hqk : q.ker = Phi.subgroupOf D :=
      (MonoidHom.ker_comp_of_injective p
        f₂.toAddEquiv.toMultiplicative.toMonoidHom f₂.injective).trans hpk
    let hn : (Phi.subgroupOf D).Normal := hqk ▸ q.normal_ker
    let := hn
    let qe := (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q
        (f₂.surjective.comp (d.onto.comp eD.surjective)))
    have hPhiD : Phi ≤ D := by
      intro x hx
      have hc : (E ⟨x,map_subtype_le _ hx⟩ : FreeAmalgam r) ∈ PhiC := (hPhi _).mpr hx
      have hDC := d.lower_le hc
      exact ⟨map_subtype_le _ hx,(hcentral _).mp hDC.2⟩
    refine ⟨hPhiD,hLD,hLPhi,hn,qe,?_⟩
    intro l x y hy
    have he := d.action (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
      (eD x) (eD y) (hE l _ _ hy)
    have hm : s.source.projection
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
        h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
    rw [hm] at he
    change f₂ (p y).toAdd = (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)
      (e (QuotientGroup.mk' (pCore 2 L) l)) (f₂ (p x).toAdd)
    change f₂ (d.quotient (eD y)).toAdd = _
    rw [he]
    apply Prod.ext <;>
      exact LinearMap.congr_fun
        (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' _) _
  · let q := n.quotient.comp E.toMonoidHom
    have hqk : q.ker = D.subgroupOf Q₀ := by
      ext x
      change E x ∈ n.quotient.ker ↔ _
      rw [n.kernel]
      change (E x : FreeAmalgam r) ∈ DC ↔ (x : J) ∈ D
      exact ⟨fun hx => ⟨x.property,(hcentral x).mp hx.2⟩,
        fun hx => ⟨(E x).property,(hcentral x).mpr hx.2⟩⟩
    let hn : (D.subgroupOf Q₀).Normal := hqk ▸ q.normal_ker
    let := hn
    let qe := (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q (n.onto.comp E.surjective))
    refine ⟨inf_le_left,hLQ,hLD,hn,qe,?_⟩
    intro l x y hy
    have he := n.action (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
      (E x) (E y) (hE l x y hy)
    have hm : s.source.projection
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
        h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
    rw [hm] at he
    exact he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
