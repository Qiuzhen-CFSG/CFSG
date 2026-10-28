module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadAction
public import Theory.Mathieu.M22.CentralCover.ElementaryHexadAction

public import Theory.Representation.BinaryPermutation.SixPlaneInvolution
public import Theory.Representation.BinaryOffender.NonFFDisplacement

/-!
# Excluding the original covered hexad and closing natural local containment

For an escaping natural member of the original local family, the moving
plane W has order four and is disjoint from the original fixed summand F.
The same F is C_V(L). Thus W avoids the covering center. In the marked
augmentation surjection onto the full hexad core, the constant image lies
in that center; it cannot be a nonidentity point of W. The six-letter
plane theorem supplies an actual even involution preserving and moving W.

Transport through the same lifted complement gives an involution of L
normalizing W and V, and centralizing F. Since V = W F, its displacement
on the entire original V lies in W. The involution fixes its displacement
but moves W, so that displacement has rank one. The original quadratic
ratio two excludes it. The full central kernel and fixed summand are
retained throughout.

Consequently every eligible natural local member K lies in M_Z, for both
original source primes, and so does its Borel. This completes the group
and intersection rows of 15.1.20(2) for the general original local family.
The additional block assertions still belong to the actual C-component
branch. Whole-core A₆ reconstruction, earlier 15.1.14 and final source
15.1.22 assembly retain their existing producers and obligations.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095; the source
module has quadratic ratio two by 15.1.4--12, pp.1087--1090; B.3.3 and
I.2.2(6), pp.84 and412, give the six-letter hexad model used here.
-/

public section
open Subgroup Representation Representation.OneCohomology Sporadic.Mathieu
open scoped IsMulCommutative Pointwise
open Sporadic.Mathieu.M22CentralCover
open Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD.UniqueFactor ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
private theorem no_plane_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (W F : Subgroup G) (hsplit : V = W ⊔ F) (hcard : Nat.card W = 4)
    (g : G) (hg2 : g ^ 2 = 1) (hgW : g ∈ normalizer (W : Set G))
    (hgV : g ∈ normalizer (V : Set G)) (hgF : g ∈ centralizer (F : Set G))
    (hmove : g ∉ centralizer (W : Set G)) : False := by
  let := h.elementary
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hFV : F ≤ V := le_sup_right.trans hsplit.symm.le
  have hgM : g ∈ M := by
    rw [UniformControl.source_local_eq_normalizer hG T hM.1]
    change g ∈ normalizer (localModule T M : Set G)
    exact hfull ▸ hgV
  let ρ := imageRepresentation M V h.normalized
  let f : M →* ChapterD.internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let a := f ⟨g,hgM⟩
  have ha2 : a ^ 2 = 1 := by
    change f ⟨g,hgM⟩ ^ 2 = 1
    rw [←map_pow,show (⟨g,hgM⟩ : M) ^ 2 = 1 from Subtype.ext hg2,map_one]
  let U : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf V).toAddSubgroup
  have hUcard : Nat.card U = 4 := by
    change Nat.card (W.subgroupOf V) = 4
    rw [Nat.card_congr (subgroupOfEquivOfLe hWV).toEquiv,hcard]
  have hdim : Module.finrank (ZMod 2) U = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod,hUcard] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  have hnot : ¬ U ≤ fixedSpace ρ (zpowers a) := by
    intro hh
    apply hmove
    intro w hw
    have hv := (mem_fixedSpace_zpowers_iff ρ a _).mp
      (hh (show Additive.ofMul (⟨w,hWV hw⟩ : V) ∈ U from hw))
    have he := congrArg (fun z : Additive V => (z.toMul : G)) hv
    change g*w*g⁻¹=w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hlt : U ⊓ fixedSpace ρ (zpowers a) < U :=
    lt_of_le_of_ne inf_le_left (fun hh => hnot (hh ▸ inf_le_right))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have hr : LinearMap.range (ρ a - LinearMap.id) ≤ U ⊓ fixedSpace ρ (zpowers a) := by
    rintro _ ⟨v,rfl⟩
    refine ⟨?_,(mem_fixedSpace_zpowers_iff ρ a _).mpr
      (involution_fixes_displacement ρ (by simpa only [pow_two] using ha2) v)⟩
    change (g*(v.toMul : G)*g⁻¹) / (v.toMul : G) ∈ W
    rw [div_eq_mul_inv]
    have hWF : W ≤ normalizer (F : Set G) := by
      apply le_trans (le_centralizer_iff.mpr ?_) (Subgroup.centralizer_le_normalizer _)
      exact hFV.trans (V.le_centralizer.trans (centralizer_le hWV))
    have hv : (v.toMul : G) ∈ (W : Set G)*(F : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right W F hWF]
      exact hsplit ▸ v.toMul.property
    obtain ⟨w,hw,z,hz,hv⟩ := hv
    have hgz : g*z*g⁻¹=z := mul_inv_eq_iff_eq_mul.mpr (hgF z hz).symm
    have he : g*(v.toMul : G)*g⁻¹*(v.toMul : G)⁻¹ = (g*w*g⁻¹)*w⁻¹ := by
      rw [←hv]
      calc
        g*(w*z)*g⁻¹*(w*z)⁻¹ = (g*w*g⁻¹)*(g*z*g⁻¹)*(w*z)⁻¹ := by group
        _ = (g*w*g⁻¹)*w⁻¹ := by rw [hgz]; group
    rw [he]
    exact W.mul_mem ((mem_normalizer_iff.mp hgW w).mp hw) (W.inv_mem hw)
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1 := by
    have hh := Submodule.finrank_mono hr
    omega
  have ha1 : a ≠ 1 := by
    intro ha
    apply hnot
    intro v hv
    apply (mem_fixedSpace_zpowers_iff ρ a v).mpr
    rw [ha,map_one]
    rfl
  have hff : IsFFModule ρ :=
    ⟨zpowers a,(bestOffender_of_involution_displacement_le_one ρ a ha2 ha1 hrank).isOffender⟩
  have hq := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
  rw [show quadraticRatio ρ = 2 from h.quadratic_ratio] at hq
  norm_num at hq

/-- The actual lifted complement contains an involution moving the original
plane, normalizing the entire original V and fixing its original fixed summand. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_plane_involution
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    let R0 := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
    let W := ⁅V,R0⁆
    let F := V ⊓ centralizer (R0 : Set G)
    ∃ g ∈ d.L, g ^ 2 = 1 ∧ g ∈ normalizer (W : Set G) ∧
      g ∈ normalizer (V : Set G) ∧ g ∈ centralizer (F : Set G) ∧
      g ∉ centralizer (W : Set G) := by
  intro R0 W F
  obtain ⟨hVQ,hZ,e,B,hB,hMLH,hMZN,hgen,hm,hspan,hE,t,ht,b,hsur,he,hproj⟩ :=
    s.localFamily_linearTwo_m22_hexad_augmentation (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let J := preimage e (MulAction.stabilizer M22 B)
  let H := J.map d.L.subtype
  let f := localProjection e (MulAction.stabilizer M22 B)
  let R := ((m22SetAction B).ker).comap f
  let j : J →* G := d.L.subtype.comp J.subtype
  let i : R →* G := j.comp R.subtype
  have hi : Function.Injective i := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hir : i.range = H.pCoreIn 2 := by
    rw [MonoidHom.range_eq_map]
    change (⊤ : Subgroup R).map (d.L.subtype.comp (J.subtype.comp R.subtype)) = _
    rw [←map_map,←map_map,←MonoidHom.range_eq_map,range_subtype]
    exact hm
  obtain ⟨hsplit,hdis,_,_⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hfixed := s.localFamily_linearTwo_fixed_carrier (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hWL : W ≤ d.L := by
    have hWU := (s.localFamily_linearTwo_moving_plane_four (h := h)
      hp hG hM hJ hu hfull hK hq hout hb).2.2.1
    have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
    exact hWU.trans ((map_subtype_le _).trans hKL)
  have hWi : W ≤ i.range := by
    rw [hir]
    exact (le_inf hWV hWL).trans ((le_conjugateSpanBy (V ⊓ d.L) H).trans hspan.le)
  let W0 := W.comap i
  have hWmap : W0.map i = W := map_comap_eq_self hWi
  have hc : Nat.card W0 = 4 := by
    rw [←card_map_of_injective hi,hWmap]
    exact (s.localFamily_linearTwo_moving_plane_four (h := h)
      hp hG hM hJ hu hfull hK hq hout hb).2.2.2
  let := h.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 W0 := IsElementaryAbelian.of_injective
    (i.subgroupComap W) (by
      intro x y hh
      exact Subtype.ext (hi (congrArg (fun z : W => (z : G)) hh)))
  have hz : b (Multiplicative.ofAdd BinaryPermutation.sixCoreConstant) ∈ W0 →
      b (Multiplicative.ofAdd BinaryPermutation.sixCoreConstant) = 1 := by
    intro hzW
    let z := b (Multiplicative.ofAdd BinaryPermutation.sixCoreConstant)
    have hp0 : BinaryPermutation.coreToNatural (Fin 6) BinaryPermutation.sixCoreConstant = 0 := by
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span (by simp [BinaryPermutation.sixCoreConstant])
    have hn : m22HexadNaturalCoordinates hB (f.subgroupComap (m22SetAction B).ker z) = 1 := by
      apply Multiplicative.toAdd.injective
      exact (hproj (Multiplicative.ofAdd BinaryPermutation.sixCoreConstant)).trans hp0
    have hfz : f z = 1 := congrArg Subtype.val
      ((m22HexadNaturalCoordinates hB).injective (hn.trans (map_one _).symm))
    have hzL : z.val.val ∈ center d.L := by
      have hzker : z.val ∈ f.ker := hfz
      rw [show f = localProjection e (MulAction.stabilizer M22 B) from rfl,
        localProjection_ker] at hzker
      exact hzker
    have hzC : i z ∈ centralizer (d.L : Set G) := by
      intro l hl
      exact congrArg Subtype.val (mem_center_iff.mp hzL ⟨l,hl⟩)
    have hzF : i z ∈ F := hfixed.ge ⟨hWV hzW,hzC⟩
    apply hi
    exact (disjoint_def.mp hdis hzW hzF).trans (map_one i).symm
  obtain ⟨a,ha,haW,w,hw,haw⟩ := BinaryPermutation.four_group_involution
    (MulAut.conjNormal.comp t) b hsur he W0 hc hz
  let g := j (t a)
  have hgL : g ∈ d.L := (t a).val.property
  have hconj (r : R) : i ((MulAut.conjNormal.comp t) a r) = g * i r * g⁻¹ := rfl
  have hgW : g ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨r,hr,rfl⟩ := hWmap.ge hx
      have hh := haW r hr
      change i ((MulAut.conjNormal.comp t) a r) ∈ W at hh
      exact hh
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have hgF : g ∈ centralizer (F : Set G) := by
    intro v hv
    exact (hfixed.le hv).2 g hgL |>.symm
  have hgV : g ∈ normalizer (V : Set G) := by
    rw [hsplit]
    exact normalizer_inf_normalizer_le_normalizer_sup W F
      ⟨hgW,Subgroup.centralizer_le_normalizer _ hgF⟩
  have hgn : g ∉ centralizer (W : Set G) := by
    intro hgC
    apply haw
    apply hi
    rw [hconj,mul_inv_eq_iff_eq_mul]
    exact (hgC (i w) hw).symm
  exact ⟨g,hgL,by change j (t a) ^ 2 = 1; rw [←map_pow,←map_pow,ha,map_one,map_one],
    hgW,hgV,hgF,hgn⟩

/-- The full covered-hexad action contradicts the original quadratic ratio two. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_impossible
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    False := by
  obtain ⟨g,_,hg2,hgW,hgV,hgF,hn⟩ :=
    s.localFamily_linearTwo_m22_plane_involution (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hsplit := (s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)).1
  have hcard := (s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb).2.2.2
  exact no_plane_involution hG hM h hfull _ _ hsplit hcard g hg2 hgW hgV hgF hn

/-- Every eligible natural member of the original local family lies in M_Z,
without an additional ambient C-component or normalization hypothesis. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    K ≤ d.MZ := by
  by_contra hout
  exact s.localFamily_linearTwo_m22_impossible (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb

/-- All group and intersection rows for the general original local family.
The source's additional block assertions remain restricted to C-components. -/
theorem PreExclusionSource.localFamily_constrained_source_rows
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K := by
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    exact (hout (s.localFamily_linearTwo_le_MZ (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hb)).elim
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Apply natural containment, Borel containment and the complete group/intersection
rows to the same original marker, retaining either original source prime. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_containment
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ∀ n : ℕ, IsL2EvenBlock K n →
          K ≤ d.MZ ∧ d.localSylowBorel K ≤ d.MZ) ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧
            CaseIComponentData.LocalConstrainedSourceRows d K) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_,?_⟩
  · intro K hK hq n hb
    have hk := s.localFamily_linearTwo_le_MZ (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hb
    exact ⟨hk,inf_le_left.trans hk⟩
  · intro K hK hq hout hf
    exact s.localFamily_constrained_source_rows (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf

end CFSG.Quasithin.Chapter15.Section01
