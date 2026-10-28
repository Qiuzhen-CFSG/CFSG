module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.FrattiniSections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFour
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.SubgroupTransport

/-!
# The original Frattini/center action in the distance-eight branch

The core equivalence carries the Frattini subgroup and the entire center
through the characteristic replacement and the amalgam embedding. Restricting
that equivalence to the Frattini subgroup transports the marked dual quotient
back to the original component action. The inverse-transpose coordinates are
converted to the literal dual representation with the same quotient marking.

The genuine Earlier input is constructed from the original source and distance.
Only the whole fixed-factor equality remains explicit, owned by
qt-ms93-distance-eight-fixed-factor. The combined SmallMSPair application is
in MarkedMS/LinearThree/DistanceEightFrattini; qt-rank-two-ms93 retains final
C.1.34 assembly and discharge of the fixed-factor premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(v), printed p.895;
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

/-- The exact original Frattini/center section of C.1.34(4), with the component
marking fixed by CommonFacts. Earlier is constructed from the source distance;
only the whole fixed-factor equality is an additional premise. -/
theorem frattini_sectionModel_of_fixedFactor
    (hb : 4 < s.geometry.b s.reduction.radical)
    (hfixed : core s.reduction.radical (alpha s.reduction.radical) ⊓ centralizer
      (Ltilde s.reduction.radical (alpha s.reduction.radical) : Set (FreeAmalgam s.reduction.radical)) =
        H s.reduction.radical (alpha s.reduction.radical)) :
    HasSectionModel L (frattiniIn (msQ L R)) (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ L R))
      (linearThreeActor (h.quotientEquiv.trans common.natural.marking))
      (Representation.specialLinearNatural (k := ZMod 2) 3).dual := by
  let r := s.reduction.radical
  let C := core r (alpha r)
  let Q₀ := commutatorCore L
  let Phi := (frattini Q₀).map Q₀.subtype
  let Z₀ := (center Q₀).map Q₀.subtype
  let PhiC := (frattini C).map C.subtype
  let ZC := (center C).map C.subtype
  let e := h.quotientEquiv.trans common.natural.marking
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨d⟩ := Center.frattini_marked_dual_of_fixedFactor common earlier hfixed
  have hQ : msQ L R = Q₀ := by
    have hc : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,h.sup_eq_top,hc]
  rw [hQ]
  change HasSectionModel L Phi Z₀ (linearThreeActor e) BinaryLinearThree.W.dual
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
  have hZPhi : Z₀ ≤ Phi := by
    apply map_mono
    intro z hz
    have hzC := (centerCongr E ⟨z,hz⟩).property
    have hpC := Center.core_center_le_frattini_of_fixedFactor common earlier hfixed hzC
    rw [← frattini_map_equiv E] at hpC
    obtain ⟨y,hy,he⟩ := hpC
    have he' : y = z := E.injective he
    exact he' ▸ hy
  let := h.component_normal
  let : Q₀.Normal := commutator_normal _ _
  have hLQ : L ≤ normalizer Q₀ := by rw [normalizer_eq_top]; exact le_top
  have hLPhi : L ≤ normalizer Phi := hLQ.trans
    (normalizer_le_normalizer_characteristic_image Q₀ (frattini Q₀))
  have hLZ : L ≤ normalizer Z₀ := hLQ.trans
    (normalizer_le_normalizer_characteristic_image Q₀ (center Q₀))
  let p := d.quotient.comp ePhi.toMonoidHom
  have hpk : p.ker = Z₀.subgroupOf Phi := by
    ext x
    change ePhi x ∈ d.quotient.ker ↔ _
    rw [d.kernel]
    change (ePhi x : FreeAmalgam r) ∈ ZC ↔ (x : J) ∈ Z₀
    rw [hePhi]
    constructor
    · rintro ⟨y,hy,he⟩
      have he' : y = E ⟨x,map_subtype_le _ x.property⟩ := Subtype.ext he
      have hh := (centerCongr E.symm ⟨y,hy⟩).property
      change E.symm y ∈ center Q₀ at hh
      rw [he',MulEquiv.symm_apply_apply] at hh
      exact mem_map_of_mem Q₀.subtype hh
    · rintro ⟨y,hy,he⟩
      have he' : y = (⟨x,map_subtype_le _ x.property⟩ : Q₀) := Subtype.ext he
      exact mem_map_of_mem C.subtype ((centerCongr E ⟨_,he' ▸ hy⟩).property)
  let f := BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv
  let q := f.toAddEquiv.toMultiplicative.toMonoidHom.comp p
  have hqk : q.ker = Z₀.subgroupOf Phi :=
    (MonoidHom.ker_comp_of_injective p
      f.toAddEquiv.toMultiplicative.toMonoidHom f.injective).trans hpk
  let hn : (Z₀.subgroupOf Phi).Normal := hqk ▸ q.normal_ker
  let := hn
  let qe := (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      (f.surjective.comp (d.onto.comp ePhi.surjective)))
  refine ⟨hZPhi,hLPhi,hLZ,hn,qe,?_⟩
  intro l x y hy
  have he := d.action (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
    (ePhi x) (ePhi y) (by rw [hePhi,hePhi]; exact hE l _ _ hy)
  have hm : s.source.projection
      (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
      h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
  rw [hm] at he
  change f (p y).toAdd = BinaryLinearThree.W.dual
    (e (QuotientGroup.mk' (pCore 2 L) l)) (f (p x).toAdd)
  change f (d.quotient (ePhi y)).toAdd = _
  rw [he]
  exact LinearMap.congr_fun
    (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' _) _

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
