module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.CenterCorrection

/-!
# Original Sylow action in the distance-four MS branch

The proved natural center is elementary and has no component-fixed points.
Averaging over the component Sylow cosets therefore gives unique corrections
inside the original center, fixed by the entire original Sylow subgroup.
Consequently a component element fixing C_{Z(Q)}(S) centralizes Ω₁Z(S).

If R were the two-core of this omega-center centralizer, every such element
would normalize the characteristic replacement radical, through its literal
inclusions in L ∨ R and G. Thus a movement witness on that replacement gives
the source radical inequality. The final theorem applies it to C.1.34(3),
using one marking for the natural center and the two dual factors.

The movement witness remains a local obligation of qt-rank-two-ms93, which
also retains the distance-eight original-action clauses and final C.1.34
assembly. No original action is inferred from replacement centrality here.
Source: Aschbacher--Smith C.1.34(3), printed pp.136--137; the final remark
on MS93 cases (11)--(13), printed p.831, and (4.6.5)--(4.6.6), p.903.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S D : Subgroup G}

omit [Finite G] in
private theorem natural_whole_properties
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel L D ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3)) :
    IsElementaryAbelian 2 D ∧ D ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨_,_,_,hn,f,hf⟩ := hm
  let := hn
  let q : D ≃* Multiplicative (Fin 3 → ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D).symm).trans f)
  have hq (x : D) : q x = f (QuotientGroup.mk' _ x) := rfl
  let he : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change v.toAdd + v.toAdd = 0
      ext i
      exact CharTwo.add_self_eq_zero _) }
  refine ⟨IsElementaryAbelian.of_surjective q.symm.toMonoidHom q.symm.surjective, ?_⟩
  apply le_bot_iff.mp
  intro x hx
  let xD : D := ⟨x,hx.1⟩
  have hfixed (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Representation.specialLinearNatural 3 g (q xD).toAdd = (q xD).toAdd := by
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm g)
    have hlg : linearThreeActor e l = g := by
      change e (QuotientGroup.mk' _ l) = g
      rw [hl,e.apply_symm_apply]
    rw [← hlg, hq]
    exact (hf l xD xD (by
      change x = (l : G) * x * (l : G)⁻¹
      rw [hx.2 l l.property,mul_inv_cancel_right])).symm
  have hz : (q xD).toAdd = 0 :=
    BinaryMS.MS93.DistanceFour.Linear.equivariantDualMap_zero
      (fun _ => (q xD).toAdd) (fun g _ => (hfixed g).symm) 0
  have hx1 : xD = 1 := q.injective ((congrArg Multiplicative.ofAdd hz).trans q.map_one.symm)
  exact congrArg Subtype.val hx1

/-- The original natural center is elementary and has trivial component-fixed subgroup. -/
theorem SmallMSPair.distance_four_center_properties (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4) :
    IsElementaryAbelian 2 (msCenter (msQ L R)) ∧
      msCenter (msQ L R) ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨e',hz,_⟩ := h.distance_four_source_sections e t common hb
  exact natural_whole_properties e' hz

private theorem center_sylow_fixed_correction (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (he : IsElementaryAbelian 2 (msCenter (msQ L R)))
    (hf : msCenter (msQ L R) ⊓ centralizer (L : Set G) = ⊥)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) :
    ∀ z ∈ omegaCenterIn S,
      ∃ q ∈ msCenter (msQ L R) ⊓ centralizer (S : Set G),
        q⁻¹ * z ∈ centralizer (L : Set G) := by
  let := he
  let J := L ⊔ R
  let K := L.subgroupOf J
  let Q := BinaryMS.commutatorCore K
  let Z := (center Q).map Q.subtype
  let f : center Q ≃* msCenter (msQ L R) :=
    (centerCongr (binaryCoreEquiv L R)).trans
      ((center (msQ L R)).equivMapOfInjective (msQ L R).subtype (msQ L R).subtype_injective)
  have heQ : IsElementaryAbelian 2 (center Q) :=
    IsElementaryAbelian.of_surjective f.symm.toMonoidHom f.symm.surjective
  have hZmap : Z.map J.subtype = msCenter (msQ L R) := by
    change (msCenter Q).map J.subtype = _
    rw [← centerIn_map Q J.subtype J.subtype_injective,binaryCore_map]
  have hfixed : Z ⊓ centralizer (K : Set J) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    apply show (x : G) ∈ (⊥ : Subgroup G) → (x : G) = 1 from id
    rw [← hf]
    refine ⟨?_,?_⟩
    · rw [← hZmap]
      exact mem_map_of_mem J.subtype hx.1
    · intro l hl
      exact congrArg Subtype.val (hx.2 ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)
  obtain ⟨P,hP⟩ := hS
  have hSJ : S ≤ J := hP ▸ map_subtype_le (P : Subgroup J)
  intro z hz
  have hzS : z ∈ S := map_subtype_le _ hz
  have hzC : z ∈ centralizer (S : Set G) := by
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hz
    intro s hs
    exact congrArg S.subtype (mem_center_iff.mp b.property ⟨s,hs⟩)
  let zJ : J := ⟨z,hSJ hzS⟩
  have hzP : zJ ∈ centralizer (P : Set J) := by
    intro p hp
    exact Subtype.ext (hzC p (hP ▸ mem_map_of_mem J.subtype hp))
  obtain ⟨q,hq,hqc⟩ := (h.binaryInput e).center_sylow_fixed_correction heQ hfixed P zJ hzP
  refine ⟨q,⟨?_,?_⟩,?_⟩
  · rw [← hZmap]
    exact mem_map_of_mem J.subtype hq.1
  · intro s hs
    obtain ⟨p,hp,hps⟩ := (show s ∈ (P : Subgroup J).map J.subtype from hP.symm ▸ hs)
    rw [← hps]
    exact congrArg Subtype.val (hq.2 p hp)
  · intro l hl
    exact congrArg Subtype.val (hqc ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)

/-- Every original Sylow omega-center element has a component-central correction
in the Sylow-fixed part of the actual commutator-core center. -/
theorem SmallMSPair.distance_four_sylow_fixed_correction (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) :
    ∀ z ∈ omegaCenterIn S,
      ∃ q ∈ msCenter (msQ L R) ⊓ centralizer (S : Set G),
        q⁻¹ * z ∈ centralizer (L : Set G) := by
  obtain ⟨he,hf⟩ := h.distance_four_center_properties e t common hb
  exact center_sylow_fixed_correction h e he hf hS

/-- Fixing the original Sylow-fixed center suffices to fix the entire original
Sylow omega-center. The source section discharges all averaging premises. -/
theorem SmallMSPair.distance_four_centralizer_omega_le (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) :
    L ⊓ centralizer (msCenter (msQ L R) ⊓ centralizer (S : Set G) : Set G) ≤
      centralizer (omegaCenterIn S : Set G) := by
  intro l hl z hz
  obtain ⟨q,hq,hc⟩ := h.distance_four_sylow_fixed_correction e t common hb hS z hz
  have he : q * (q⁻¹ * z) = z := mul_inv_cancel_left q z
  calc
    z * l = (q * (q⁻¹ * z)) * l := by rw [he]
    _ = q * ((q⁻¹ * z) * l) := mul_assoc _ _ _
    _ = q * (l * (q⁻¹ * z)) := by rw [(hc l hl.1).symm]
    _ = (q * l) * (q⁻¹ * z) := (mul_assoc _ _ _).symm
    _ = (l * q) * (q⁻¹ * z) := by rw [hl.2 q hq]
    _ = l * z := by rw [mul_assoc, he]


/-- Movement of the literal characteristic replacement excludes the original
radical-centralizer equality. The movement calculation remains with the
C.1.34 owner qt-rank-two-ms93. -/
theorem SmallMSPair.distance_four_not_centralizer_core_of_replacement_movement
    (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R))
    (hmove : ¬ L ⊓ centralizer (msCenter (msQ L R) ⊓ centralizer (S : Set G) : Set G) ≤
      normalizer (t.reduction.ambient.map (L ⊔ R).subtype : Set G)) :
    MSNotCentralizerCore L R S := by
  intro heq
  apply hmove
  intro l hl
  have hlC := h.distance_four_centralizer_omega_le e t common hb hS hl
  let C := (L ⊔ R) ⊓ centralizer (omegaCenterIn S : Set G)
  have hlN : l ∈ normalizer (R : Set G) := by
    rw [heq]
    exact normalizer_le_normalizer_characteristic_image C (pCore 2 C)
      (C.le_normalizer ⟨(show L ≤ L ⊔ R from le_sup_left) hl.1,hlC⟩)
  let j : (L ⊔ R : Subgroup G) := ⟨l,(show L ≤ L ⊔ R from le_sup_left) hl.1⟩
  have hjN : j ∈ normalizer (R.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) :=
    (Subgroup.le_normalizer_comap (L ⊔ R).subtype) hlN
  let := t.reduction.characteristic
  have hjT : j ∈ normalizer (t.reduction.ambient : Set (L ⊔ R : Subgroup G)) :=
    normalizer_le_normalizer_characteristic_image (R.subgroupOf (L ⊔ R))
      t.reduction.subgroup hjN
  exact t.reduction.ambient.le_normalizer_map (L ⊔ R).subtype
    (mem_map_of_mem (L ⊔ R).subtype hjT)

/-- Apply the original-action argument to the literal third alternative, with
one common marking. Only the explicit replacement-movement calculation
remains before this distance-four branch is unconditional. -/
theorem SmallMSPair.distance_four_source_of_replacement_movement
    (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R))
    (hmove : ¬ L ⊓ centralizer (msCenter (msQ L R) ⊓ centralizer (S : Set G) : Set G) ≤
      normalizer (t.reduction.ambient.map (L ⊔ R).subtype : Set G)) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e',hZ,hQ⟩ := h.distance_four_source_sections e t common hb
  exact ⟨e',Or.inr (Or.inr (Or.inl ⟨hZ,hQ,
    h.distance_four_not_centralizer_core_of_replacement_movement e t common hb hS hmove⟩))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
