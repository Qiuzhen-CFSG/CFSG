module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictRank
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# The crossing fixed-vector bound on U/Z(U)

For each u outside W = C_U(Z_S), the natural I/P-module P/E identifies
linear displacement from X/E to W/E. The translated-subspace identity
on the actual natural tensor identifies the inverse image of Z(U)E/E
with Z(U)^d E/E, using the original right-conjugation convention.

An actor fixing u modulo Z(U) therefore belongs to that preimage.
The known kernel E vanishes in the faithful dotted actor, giving
C_{U/Z(U)}(x-dot) ≤ W-hat whenever x-dot is outside Z(U)^d-dot.
The two quotients by Z(U) and by the original point remain distinct.

Source: Aschbacher--Smith, 6.2.17(5), printed p.690, using G.2.3.
StrictInputs and its Chapter12 application consume this bound in the
literal G.10.1 hypothesis. LocalAnalysis is supplied by
qt-d-1222-rankone-recognition-identification; classification and final
elimination remain with qt-d-1222-recognition-strict-elimination.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise TensorProduct
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The exact center preimage under displacement by any original u outside W. -/
theorem LocalAnalysis.strict_crossing_center_preimage
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    {u x : G} (hu : u ∈ sourceClosure (T : Subgroup G) L R z)
    (huw : u ∉ centralizer (ZS (T : Subgroup G) L R : Set G))
    (hx : x ∈ strictCrossingGroup (T : Subgroup G) L R z d) :
    let U := sourceClosure (T : Subgroup G) L R z
    let E := strictCrossingIntersection (T : Subgroup G) L R z d
    ⁅x,u⁆ ∈ (center U).map U.subtype ⊔ E ↔
      x ∈ strictCrossingCenter (T : Subgroup G) L R z d ⊔ E := by
  obtain ⟨heU, hE, hPc, hI, hP, e, hN, hA, σ, c, hVE, hEP, _, _, _, _, _, hcompl,
      ⟨j, hj⟩, hmarks⟩ :=
    A.strict_binary_crossing_module h611 hnatural hz horder hTH hstrict hdres hdH
  let D := strictBinarySetup (T : Subgroup G) L R z
  let := hN
  let := hA
  let U := sourceClosure (T : Subgroup G) L R z
  let C := (center U).map U.subtype
  let W := U ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I d)))
  let ui : D.I d := ⟨u, mem_sup_left (heU.ge hu)⟩
  let di : D.I d := ⟨d⁻¹, (D.I d).inv_mem (hI.ge (mem_sup_left hdres))⟩
  let xp : D.S d := ⟨x, hP.ge (mem_sup_right hx)⟩
  have hCW : C ≤ W := by
    refine le_inf (map_subtype_le _) ?_
    rintro _ ⟨a, ha, rfl⟩ s hs
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨s, (hstrict.le hs).1⟩)
  have hWP : W ≤ D.S d := le_sup_left.trans hP.ge
  have hCP : C ≤ D.S d := hCW.trans hWP
  have hpi (a : D.I d) : π a = 1 ↔ (a : G) ∈ D.S d := by
    constructor
    · intro ha
      have ha' : QuotientGroup.mk' (pCore 2 (D.I d)) a = 1 :=
        e.injective (ha.trans (map_one e).symm)
      exact mem_map_of_mem (D.I d).subtype ((QuotientGroup.eq_one_iff a).mp ha')
    · rintro ⟨b, hb, he⟩
      have hab : a = b := Subtype.ext he.symm
      rw [hab]
      change e (QuotientGroup.mk' (pCore 2 (D.I d)) b) = 1
      rw [show QuotientGroup.mk' (pCore 2 (D.I d)) b = 1 from
        (QuotientGroup.eq_one_iff b).mpr hb, map_one]
  have ht1 : π ui ≠ 1 := by
    intro h
    exact huw (hPc.le ((hpi ui).mp h)).2
  have ht2 : π ui * π ui = 1 := by
    rw [← map_mul]
    apply (hpi _).mpr
    have hpU : IsPGroup 2 U :=
      ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
    let : Fact (IsPGroup 2 U) := ⟨hpU⟩
    have hs : u ^ 2 ∈ (frattini U).map U.subtype := mem_map_of_mem U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : U))
    rw [(A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1] at hs
    exact hEP (hVE (zpowers_le.mpr hz (by simpa only [pow_two, ui, Subgroup.coe_mul] using hs)))
  obtain ⟨_, _, hW, hX⟩ :=
    A.strict_binary_crossing_identifications h611 hnatural hz horder hTH hstrict hdres hdH
  have hWX : W.conjBy (di : G) = X := by
    change W.map (MulAut.conj d⁻¹).toMonoidHom = X
    change D.W d = W at hW
    rw [← hW]
    exact hX
  have hWmap : c.imageSpace X = (c.imageSpace W).map (σ (π di)) := by
    rw [← hWX]
    exact c.imageSpace_conjBy W hWP di
  have hCmap : c.imageSpace (strictCrossingCenter (T : Subgroup G) L R z d) =
      (c.imageSpace C).map (σ (π di)) := c.imageSpace_conjBy C hCP di
  obtain ⟨hk, hr, _⟩ := hmarks ui hu (fun hh => huw hh.2)
  have hpre := Representation.BinaryQuadraticPair.translated_subspace_preimage_of_compl
    σ j hj (π ui) (π di) ht2 ht1 (c.imageSpace W) (c.imageSpace C)
    hk hr (hWmap ▸ hcompl) (c.coordinates xp).toAdd
    (by rw [← hWmap]; exact (c.mem_imageSpace_iff X _).mpr ⟨xp, hx, rfl⟩)
  have hCX : strictCrossingCenter (T : Subgroup G) L R z d ≤ X :=
    strictCrossingCenter_le_group h611 hz ((map_subtype_le _ hdres).2)
  rw [← hCmap, c.coordinates_mem_imageSpace_iff _ (hCX.trans (le_sup_right.trans hP.ge)) xp] at hpre
  have hdisp := c.displacement_mem_imageSpace_iff C hCP ui xp
  change (σ (π ui) - 1) (c.coordinates xp).toAdd ∈ c.imageSpace C ↔ _ at hdisp
  rw [hdisp, hE] at hpre
  have hinv : ⁅x,u⁆ ∈ C ⊔ strictCrossingIntersection (T : Subgroup G) L R z d ↔
      ⁅u,x⁆ ∈ C ⊔ strictCrossingIntersection (T : Subgroup G) L R z d := by
    rw [← commutatorElement_inv, inv_mem_iff]
  exact hinv.trans hpre


/-- Source 6.2.17(5), on the literal central quotient and faithful actor. -/
theorem LocalAnalysis.strict_crossing_fixed_bound
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {a : StrictActor (T : Subgroup G) L R z}
    (ha : a ∈ strictCrossingImage (T : Subgroup G) L R z d)
    (ha0 : a ∉ strictCrossingCenterImage (T : Subgroup G) L R z d)
    {v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)}
    (hfix : strictRepresentation (T : Subgroup G) L R z a v = v) :
    v ∈ strictHatSpace (T : Subgroup G) L R z
      (sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)) := by
  classical
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  let E := strictCrossingIntersection (T : Subgroup G) L R z d
  let C' := strictCrossingCenter (T : Subgroup G) L R z d
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center U) v.toMul
  have hv : v = strictHatElement (T : Subgroup G) L R z u :=
    (congrArg Additive.ofMul hu).symm
  rw [hv] at hfix ⊢
  by_contra hvW
  have huw : (u : G) ∉ centralizer (ZS (T : Subgroup G) L R : Set G) := by
    intro hw
    exact hvW ⟨u, ⟨u.property, hw⟩, rfl⟩
  have hcomm : ⁅(x : G),(u : G)⁆ ∈ (center U).map U.subtype := by
    have he : strictQuotientAction (T : Subgroup G) L R z x
        (QuotientGroup.mk' (center U) u) = QuotientGroup.mk' (center U) u :=
      Additive.ofMul.injective hfix
    rw [strictQuotientAction_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨strictClosureAction (T : Subgroup G) L R z x u / u, hc, ?_⟩
    change ((x : G) * (u : G) * (x : G)⁻¹) / (u : G) = _
    simp only [div_eq_mul_inv, commutatorElement_def]
  have hxCE : (x : G) ∈ C' ⊔ E :=
    (A.strict_crossing_center_preimage h611 hnatural hz horder hTH hstrict hdres hdH
      u.property huw hx).mp (mem_sup_left hcomm)
  have hUH : U ≤ H := A.closure_le_core.trans (H.pCoreIn_le 2)
  have hEH : E ≤ H := inf_le_left.trans hUH
  have hCH : C' ≤ H := (strictCrossingCenter_le_group h611 hz
    ((map_subtype_le _ hdres).2)).trans (strictCrossingGroup_le_centralizer _ _ _ _ _ hz)
  have hqE : (E.subgroupOf H).map q = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨e, he, rfl⟩
    apply Subgroup.mem_bot.mpr
    apply (QuotientGroup.eq_one_iff e).mpr
    exact A.strict_closure_le_dotted_kernel h611 hnatural hz horder hstrict
      (show (e : G) ∈ U from he.1)
  have hmap : ((C' ⊔ E).subgroupOf H).map q =
      strictCrossingCenterImage (T : Subgroup G) L R z d := by
    rw [subgroupOf_sup hCH hEH, Subgroup.map_sup, hqE, sup_bot_eq]
    rfl
  apply ha0
  rw [← hmap]
  exact mem_map_of_mem q hxCE

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
