module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitKernelControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EqualKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitDisplacement

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift

/-!
# Strict forward slices on the original exceptional Borel graph

Each conjugate of the shifted normal radius section is elementary. For a
nonzero seed-kernel displacement, the Borel cover alternative and the actual
radius escape force endpoint control. For zero displacement, the pulled-back
two-subgroup centralizes the seed and therefore lies in its two-core, even
with the odd cubic kernel quotient. Its displacement lies in the moved
order-two line and in the endpoint seed, forcing it to vanish.

These individual controls make the whole orbit span invariant; no
assertion of elementarity of that whole span is needed. The original
residual-action theorem, residual-edge generation and nilpotent saturation
collapse the orbit span. The actual transported kernel then controls the
full stabilizer orbit of the shifted seed, contradicting its Baumann-slice
escape. This proves the strict forward bound for both critical image sizes
and both full moving covers, at every original component vertex.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.920--922.
The proof replaces the full-stabilizer R₃-centrality step by per-conjugate
control. It keeps the original graph, maps, central attachments and E/Q of
order three. The terminal exclusions (5.10)--(5.12), whole-core exhaustion
and exceptional reconstruction remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e hz hk in
/-- An elementary actor in both predecessor cores controls the full endpoint
or has reverse-kernel displacement of order at most two. -/
theorem borel_elementary_reverse_kernel_control_or_card
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hTa : T ≤ Q Rg a)
    [IsElementaryAbelian 2 T] :
    (⁅T,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,T⁆) ∨
    Nat.card (⁅Z Rg z ⊓ Q Rg a,T⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  by_cases hescape : ⁅T,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,T⁆
  · exact Or.inl hescape
  apply Or.inr
  have hb := distance_gt_two h e hz hk
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ =
      ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hT).symm
  have hcontrol : ¬ ⁅U Rg z,T⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hT]
    rw [hfixed] at hh
    exact hh.trans (sup_le le_sup_right (by
      rw [commutator_comm]
      exact ((commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)).trans le_sup_left))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p T hT 1 (one_mem _)
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hp i hi hiQ hiU hA hAr
  let A := (Z Rg a).comap i
  let P := T.comap i
  let F := W₀ ⊓ centralizer (A : Set M)
  have hF : F.map i = U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA]
  have h2 : ∀ g ∈ P.map π, g^2 = 1 := by
    rintro _ ⟨g,hg,rfl⟩
    have hg2 : g^2 = 1 := by
      apply hi
      simpa only [map_pow,map_one] using
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (i g) hg)
    rw [←map_pow,hg2,map_one]
  have hab : ∀ g ∈ P.map π, ∀ k ∈ P.map π, Commute g k := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨k,hk,rfl⟩
    change π g * π k = π k * π g
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simpa only [map_mul,Subgroup.coe_mul] using congrArg (fun y : T => (y : FreeAmalgam Rg))
      (mul_comm (⟨i g,hg⟩ : T) (⟨i k,hk⟩ : T))
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hTa hg)).symm
  have hbound := borel_cover_uncontrolled_fixed_card h e hz hk u τ (hApi hτ)
    hτswap A P hτeq hPpi h2 hab hcomm (by
      intro hh
      apply hcontrol
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,map_commutator W₀ P i,hiU,hP,
        map_commutator _ P i,hF,hP,map_commutator W₀ A i,hiU,hA] at hm)
  rw [←card_map_of_injective hi,map_commutator,hF,hP,hfixed] at hbound
  exact hbound

include h e hz in
private theorem borel_predecessor_kernel_displacement_escape
    (hb : 2 < sourceDistance h) {c z a : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c z)
    (ha : color Rg a = false) (hca : (cosetGraph Rg).dist c a ≤ 2)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hYB : ¬ Y ≤ B Rg a ((sourceGeometry h).Z_normal _))
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg c)
    (hne : ⁅(Z Rg a).map (MulAut.conj x).toMonoidHom,
      Z Rg z ⊓ Q Rg c⁆ ≠ ⊥) :
    ¬ ⁅Y.map (MulAut.conj x).toMonoidHom,Z Rg z ⊓ Q Rg c⁆ ≤
      ⁅(Z Rg a).map (MulAut.conj x).toMonoidHom,Z Rg z ⊓ Q Rg c⁆ := by
  let K := Z Rg z ⊓ Q Rg c
  let f := (MulAut.conj x).toMonoidHom
  let fi := (MulAut.conj x⁻¹).toMonoidHom
  let A := K.map fi
  have hAf : A.map f = K := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam Rg) := by
      apply MonoidHom.ext
      intro v
      change x*(x⁻¹*v*(x⁻¹)⁻¹)*x⁻¹ = v
      group
    rw [he,map_id]
  have hAQ : A ≤ Q Rg c :=
    (map_mono (show K ≤ Q Rg c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized Rg c) ((stabilizer Rg c).inv_mem hx)))
  have hAG : A ≤ stabilizer Rg a := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
  have hZA : ⁅Z Rg a,A⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg a))
  have hZAmap : (⁅Z Rg a,A⁆ : Subgroup (FreeAmalgam Rg)).map f =
      ⁅(Z Rg a).map f,K⁆ := by rw [map_commutator,hAf]
  have hnA : ¬ A ≤ Q Rg a := by
    intro hAcore
    have hzero : ⁅Z Rg a,A⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl hAcore).trans_eq (Z_centralizes_Q Rg a ha))
    apply hne
    rw [←hZAmap,hzero,Subgroup.map_bot]
  intro hle
  have hYA : ⁅Y,A⁆ ≤ Z Rg a := by
    apply le_trans _ hZA
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj x).injective).mp
    rwa [hZAmap,map_commutator,hAf]
  exact hYB (normalized_radius_le_slice_of_controlled_actor h e hz hb ha Y A hYV hYN hAG
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c
      q.start_color).to_le hAQ) hnA hYA)


include h e hz hk in
/-- Every conjugate normal section is controlled, including the zero seed-kernel case. -/
theorem borel_conjugate_section_control
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c z a : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c z)
    (hsmall : (Q Rg z).relIndex (Z Rg c) < 4)
    (ha : color Rg a = false) (hca : (cosetGraph Rg).dist c a ≤ 2)
    (Y H P : Subgroup (FreeAmalgam Rg))
    (hYV : Y ≤ V Rg a)
    (hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hYB : ¬ Y ≤ B Rg a ((sourceGeometry h).Z_normal _))
    (hZaY : Z Rg a ≤ Y) (hZcY : Z Rg c ≤ Y)
    (hPG : P ≤ stabilizer Rg c) (hPH : P ≤ centralizer (H : Set (FreeAmalgam Rg)))
    (hHcard : Nat.card H = 2) (hmove : ¬ H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)))
    (hcomm : ⁅Y,Q Rg a ⊓ centralizer
      (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ ≤ H)
    (hDcard : Nat.card (⁅conjugateSpanBy (Z Rg a) P,Z Rg z ⊓ Q Rg c⁆ :
      Subgroup (FreeAmalgam Rg)) = 2)
    (hWpre : conjugateSpanBy Y P ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (x : P) :
    let Yx := Y.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom
    ⁅Yx,Z Rg z⁆ ≤ ⁅Yx,Z Rg z ⊓ Q Rg c⁆ ⊔ Z Rg c := by
  let K := Z Rg z ⊓ Q Rg c
  let f := (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom
  let fi := (MulAut.conj (x : FreeAmalgam Rg)⁻¹).toMonoidHom
  let Yx := Y.map f
  let J := ⁅(Z Rg a).map f,K⁆
  let E := ⁅Yx,K⁆
  let D := conjugateSpanBy (Z Rg a) P
  have hxG := hPG x.property
  have hYxW : Yx ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map (MulAut.conj (k : FreeAmalgam Rg)).toMonoidHom) x
  have hZxD : (Z Rg a).map f ≤ D := by
    rw [show D = conjugateSpanBy (Z Rg a) P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z Rg a).map
      (MulAut.conj (k : FreeAmalgam Rg)).toMonoidHom) x
  have hpre : color Rg (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = sourceDistance h := q.length_eq_b
    omega
  have hYxz : Yx ≤ stabilizer Rg z := (hYxW.trans hWpre).trans
    (Q_le_stabilizer_of_dist_le_two _ _ hpre q.end_color (by
      rw [q.dist_end]
      have hl : q.walk.length = sourceDistance h := q.length_eq_b
      omega))
  have hEZ : E ≤ Z Rg z := by
    rw [show E = ⁅Yx,K⁆ from rfl,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYxz.trans (Z_normalized Rg z)))
  let := finite_Z Rg z
  let : Finite E := Finite.of_injective (inclusion hEZ) (inclusion_injective _)
  have hJE : J ≤ E := commutator_mono (map_mono hZaY) le_rfl
  let : Finite J := Finite.of_injective (inclusion hJE) (inclusion_injective _)
  have hZcYx : Z Rg c ≤ Yx := by
    exact (mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c hxG)).symm.le.trans
      (map_mono hZcY)
  by_cases hJ : J = ⊥
  · let A := K.map fi
    have hAf : A.map f = K := by
      rw [map_map]
      have he : f.comp fi = MonoidHom.id (FreeAmalgam Rg) := by
        apply MonoidHom.ext
        intro v
        change (x : FreeAmalgam Rg)*((x : FreeAmalgam Rg)⁻¹*v*
          ((x : FreeAmalgam Rg)⁻¹)⁻¹)*(x : FreeAmalgam Rg)⁻¹ = v
        group
      rw [he,map_id]
    have hAQc : A ≤ Q Rg c := (map_mono (show K ≤ Q Rg c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized Rg c ((stabilizer Rg c).inv_mem hxG)))
    have hAGa : A ≤ stabilizer Rg a := hAQc.trans
      (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
    have hzero : ⁅Z Rg a,A⁆ = ⊥ := by
      apply (map_injective (f := f) (MulAut.conj (x : FreeAmalgam Rg)).injective)
      rw [map_commutator,hAf,Subgroup.map_bot]
      exact hJ
    have hAQa : A ≤ Q Rg a :=
      two_subgroup_seed_centralizer_le_core h e hz ha A
        ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c
          q.start_color).to_le hAQc)
        (le_inf hAGa (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)))
    have hAT : A ≤ Q Rg a ⊓ centralizer
        (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :=
      le_inf hAQa ((hAQc.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c q.start_color)))).trans
          (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg c))))
    have hEH : E ≤ H := by
      have hh := map_mono (f := f) ((commutator_mono le_rfl hAT).trans hcomm)
      rw [map_commutator,hAf] at hh
      have hHmap : H.map f = H := mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer _ (hPH x.property))
      exact hh.trans_eq hHmap
    have hEbot : E = ⊥ := by
      by_contra hn
      have hpos := (one_lt_card_iff_ne_bot E).mpr hn
      let : Finite H := Nat.finite_of_card_ne_zero (by omega)
      have he : E = H := eq_of_le_of_card_ge hEH (by omega)
      have hHZ := he ▸ hEZ
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z q.end_color
      exact hmove (hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    exact (small_critical_kernel_commutator h e hz hk q hsmall Yx hYxz
      (commutator_eq_bot_iff_le_centralizer.mp hEbot)).trans
        ((critical_seed_commutator_le h q).trans le_sup_right)
  · have hDfinite : Finite (⁅D,K⁆ : Subgroup (FreeAmalgam Rg)) :=
      Nat.finite_of_card_ne_zero (by change Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam Rg)) = 2 at hDcard; omega)
    let := hDfinite
    have hJle : J ≤ ⁅D,K⁆ := commutator_mono hZxD le_rfl
    have hJcard : Nat.card J = 2 := by
      have hpos := (one_lt_card_iff_ne_bot J).mpr hJ
      have hbound := card_le_of_le hJle
      change Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam Rg)) = 2 at hDcard
      omega
    have hnot := borel_predecessor_kernel_displacement_escape h e hz
      (by omega : 2 < sourceDistance h) q ha hca Y hYV hYN hYB x hxG hJ
    have hYQ : Y ≤ Q Rg c := hYV.trans
      (V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) ha (by
        change (cosetGraph Rg).dist a c + 2 < sourceDistance h
        rw [SimpleGraph.dist_comm]
        omega))
    have hYxQ : Yx ≤ Q Rg c := (map_mono hYQ).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c hxG))
    let := V_elementary_of_four_lt Rg (geometry := sourceGeometry h) ha hb
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYV
    let : IsElementaryAbelian 2 Yx := IsElementaryAbelian.map f
    rcases borel_elementary_reverse_kernel_control_or_card h e hz hk u hR q hsmall
        Yx (hYxW.trans hWpre) hYxQ with hcontrol | hcard
    · rw [commutator_comm (Z Rg z ⊓ Q Rg c) Yx,
        sup_comm (Z Rg c) (⁅Yx,Z Rg z ⊓ Q Rg c⁆)] at hcontrol
      exact hcontrol
    · have hbound : Nat.card E ≤ 2 := by
        rw [commutator_comm (Z Rg z ⊓ Q Rg c) Yx] at hcard
        exact hcard
      have he : J = E := eq_of_le_of_card_ge hJE (by omega)
      exact (hnot he.symm.le).elim


end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open AlternatingSixReconstruction.Exceptional.OriginalSylow
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R

private theorem borel_acting_seed_le_local_span
    {c a t : Vertex Rg} (hc : color Rg c = false)
    (ha : color Rg a = false)
    (hct : Adjacent Rg c t) (hat : Adjacent Rg a t) :
    Z Rg a ≤ localZSpan Rg c a := by
  conv_lhs => rw [Z,if_pos ha]
  apply iSup_le
  intro v
  apply iSup_le
  intro hav
  have hv : color Rg v ≠ false := by
    simpa only [ha] using (adjacent_color_ne Rg hav).symm
  obtain ⟨g,hg,hgv⟩ := stabilizer_transitive_neighbors Rg a hat hav
  have hseed : Z Rg t ≤ localZSpan Rg c a :=
    (adjacent_Z_le Rg hc hct).trans (Z_le_localZSpan Rg c a)
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hseed
  have he : (localZSpan Rg c a).map (MulAut.conj g⁻¹).toMonoidHom =
      localZSpan Rg c a := mem_normalizer_iff_map_conj_eq.mp
    (localZSpan_normalized Rg c a ((stabilizer Rg a).inv_mem hg))
  rw [he,←Z_act,hgv] at hh
  simpa only [Z,if_neg hv] using hh

namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- Control of each elementary conjugate makes the whole span invariant.
Residual-edge generation and nilpotent saturation then collapse that span. -/
theorem borel_spanOrbit_collapse
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    stabilizer Rg (p.walk.getVert 2) ≤ normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) ∧
      s.spanOrbit = s.span := by
  let c := p.walk.getVert 2
  let a := s.centerVertex
  let t := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  let Y := s.span
  let W := s.spanOrbit
  let P := s.lineCentralizer
  let K := s.orbitKernel
  let N := ⁅W,Q Rg c⁆ ⊔ Z Rg c
  let Yx (x : P) := Y.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom
  have hb2 : 2 < sourceDistance h := by omega
  have hc : color Rg c = false := s.path.start_color
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg a t := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [s.fixes_second] using (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr hh
  have hca : (cosetGraph Rg).dist c a ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hYV : Y ≤ V Rg a := s.span_le_radius hb2
  have hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    localZSpan_normalized Rg c a
  have hZaY : Z Rg a ≤ Y := borel_acting_seed_le_local_span hc s.center_color hct hat
  have hZcY : Z Rg c ≤ Y := Z_le_localZSpan Rg c a
  have hel := (borel_critical_paths h e hz hk u hR p).2.2.2
  have hYB := s.span_not_le_slice hb2 hel
  have hsmall : (Q Rg s.endpoint).relIndex (Z Rg c) < 4 := by
    rw [(s.borel_shifted_indices e hz hk hb u hR hslice hel).1]
    decide
  have hWpre : W ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-2)) := by
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
    exact (s.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb u hR hslice hel).2
  have hcomm : ⁅Y,Q Rg a ⊓ centralizer
      (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ ≤ s.line := by
    change ⁅Y,forwardSliceKernel h a c⁆ ≤ s.line
    rw [←s.kernel_eq hb2]
    exact (s.borel_span_commutator e hz hk hb2 u hR hslice).le
  have hcontrols (x : P) : ⁅Yx x,Z Rg s.endpoint⁆ ≤ ⁅Yx x,K⁆ ⊔ Z Rg c :=
    borel_conjugate_section_control h e hz hk hb u hR s.path hsmall s.center_color hca
      Y s.line P hYV hYN hYB hZaY hZcY inf_le_left inf_le_right
      (s.borel_line_facts e hz hk hb2 u hR hslice).1 s.moves hcomm
      (s.borel_orbit_displacement_card_two e hz hk hb u hR hslice) hWpre x
  have hQY : Q Rg c ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (Q_le_stabilizer_of_dist_le_two c a hc s.center_color hca).trans hYN
  have hQYx (x : P) : Q Rg c ≤ normalizer (Yx x : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom) hQY).trans
      (Y.le_normalizer_map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom)
    exact (mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c x.property.1)).symm.le.trans hh
  have hZYx (x : P) : Z Rg c ≤ Yx x := by
    have hh := map_mono (f := (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom) hZcY
    exact (mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c x.property.1)).symm.le.trans hh
  have hZYnorm (x : P) : Z Rg s.endpoint ≤ normalizer (Yx x : Set (FreeAmalgam Rg)) :=
    le_normalizer_iff_commutator_le_left.mpr ((hcontrols x).trans
      (sup_le (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans (hQYx x))) (hZYx x)))
  have hZW : Z Rg s.endpoint ≤ normalizer (W : Set (FreeAmalgam Rg)) := by
    rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact (le_iInf hZYnorm).trans (iInf_normalizer_le_normalizer_iSup _)
  have hWN : stabilizer Rg c ≤ normalizer (W : Set (FreeAmalgam Rg)) := by
    rw [←s.generates]
    exact sup_le (le_normalizer_conjugateSpanBy Y P) hZW
  have hYQ : Y ≤ Q Rg c := hYV.trans
    (V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) s.center_color (by
      change (cosetGraph Rg).dist a c + 2 < sourceDistance h
      rw [SimpleGraph.dist_comm]
      omega))
  have hWQ : W ≤ Q Rg c := conjugateSpanBy_le hYQ (inf_le_left.trans (Q_normalized Rg c))
  have hWG : W ≤ stabilizer Rg c := hWQ.trans (fun _ hx => hx.1)
  have hYW : Y ≤ W := le_conjugateSpanBy Y P
  have hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [N]
    rw [Subgroup.map_sup,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hWN hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c hg)]
  have hNW : N ≤ W := sup_le
    (le_normalizer_iff_commutator_le_left.mp ((show Q Rg c ≤ stabilizer Rg c from
      fun _ hx => hx.1).trans hWN)) (hZcY.trans hYW)
  have hNG : N ≤ stabilizer Rg c := hNW.trans hWG
  have hYxW (x : P) : Yx x ≤ W := by
    rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map (MulAut.conj (k : FreeAmalgam Rg)).toMonoidHom) x
  have hWE : ⁅W,Z Rg s.endpoint⁆ ≤ N := by
    conv_lhs => rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact commutator_iSup_le_of_relative_normal (stabilizer Rg c) (Z Rg s.endpoint) N Yx
      hNN (fun x => (hYxW x).trans hWG)
      (fun x => (hcontrols x).trans (sup_le_sup_right
        (commutator_mono (hYxW x) inf_le_right) _))
  have hres : ⁅W,Ltilde Rg c⁆ ≤ N :=
    normal_section_residual_control_mod e hz hk s.path W N hWG hWN hNN hNG hWE
  have hQtG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hQtY : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg a from fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans hYN
  have hjoinN : stabilizer Rg c ≤ normalizer ((Y ⊔ N : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) := by
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) hc hct]
    refine sup_le ?_ ((le_inf hQtY (hQtG.trans hNN)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
    apply le_normalizer_iff_commutator_le_left.mpr
    apply le_trans ?_ le_sup_right
    apply commutator_sup_le_of_relative_normal (stabilizer Rg c)
      Y N (Ltilde Rg c) N hNN (hYW.trans hWG) hNG
      ((commutator_mono hYW le_rfl).trans hres)
    exact le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans hNN)
  have hcover : W ≤ Y ⊔ ⁅W,Q Rg c⁆ := by
    have hs : W ≤ Y ⊔ N := conjugateSpanBy_le le_sup_left (inf_le_left.trans hjoinN)
    exact hs.trans (sup_le le_sup_left (sup_le le_sup_right (hZcY.trans le_sup_left)))
  let := finite_stabilizer Rg c
  let : Finite (Q Rg c) := Finite.of_injective
    (inclusion (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)) (inclusion_injective _)
  have hWY : W ≤ Y := le_of_le_sup_commutator_of_isNilpotent (Q Rg c) W Y (Q Rg c)
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).isNilpotent
    hWQ hYQ le_rfl hQY hcover
  exact ⟨hWN,le_antisymm hWY hYW⟩

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R

include h e hz hk in
/-- MS93 (5.9): on the original Borel graph, every forward slice has index
strictly greater than two above distance four, for either critical image size. -/
theorem borel_forward_slice_strict
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < sourceDistance h := by omega
  obtain ⟨s,hcomm,hHcard,_⟩ := borel_small_slice_shift_control h e hz hk hb2 u hR p hslice
  have hcollapse := s.borel_spanOrbit_collapse e hz hk hb u hR hslice
  let c := p.walk.getVert 2
  let a := s.centerVertex
  let t := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  have hc : color Rg c = false := s.path.start_color
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg a t := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [s.fixes_second] using (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr hh
  have hca : (cosetGraph Rg).dist c a ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hZaY : Z Rg a ≤ s.span := borel_acting_seed_le_local_span hc s.center_color hct hat
  have hYN : stabilizer Rg c ≤ normalizer (s.span : Set (FreeAmalgam Rg)) := by
    rw [←hcollapse.2]
    exact hcollapse.1
  have hTQa : s.kernel ≤ Q Rg a := by
    rw [s.kernel_eq hb2]
    exact inf_le_left
  have hTG : s.kernel ≤ stabilizer Rg c := hTQa.trans
    (Q_le_stabilizer_of_dist_le_two a c s.center_color hc (by
      rw [SimpleGraph.dist_comm]
      exact hca))
  have hcommU : ⁅U Rg c,s.kernel⁆ = s.line := by
    have hUm : (U Rg c).map (MulAut.conj s.conjugator).toMonoidHom = U Rg c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c (Ltilde_le_stabilizer _ s.residual))
    dsimp only [SmallSliceShift.line,forwardSliceLine,SmallSliceShift.kernel]
    rw [map_commutator,hUm]
  have hHc : s.line ≤ Z Rg c := by
    rw [←hcommU]
    exact (le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))).trans
      (DistanceEight.U_le_Z Rg c)
  have hTne : ¬ s.kernel ≤ Q Rg c := by
    intro hle
    have he : ⁅U Rg c,s.kernel⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z Rg c) hle).trans_eq
        (Z_centralizes_Q Rg c hc))
    rw [hcommU] at he
    rw [he,card_bot] at hHcard
    omega
  let F := conjugateSpanBy (Z Rg a) (stabilizer Rg c)
  have hFY : F ≤ s.span := conjugateSpanBy_le hZaY hYN
  have hFV : F ≤ V Rg c := conjugateSpanBy_le
    ((le_conjugateSpanBy _ _).trans (s.seedOrbit_radius_and_escape e hz hb2).1)
    (DistanceEight.V_normalized Rg c)
  have hFB := normalized_radius_le_slice_of_controlled_actor h e hz hb2 hc F s.kernel hFV
    (le_normalizer_conjugateSpanBy _ _) hTG
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a
      s.center_color).to_le hTQa) hTne
    (((commutator_mono hFY le_rfl).trans_eq hcomm).trans hHc)
  have hDF : s.seedOrbit ≤ F := conjugateSpanBy_le (le_conjugateSpanBy _ _)
    (inf_le_left.trans (le_normalizer_conjugateSpanBy _ _))
  exact (s.seedOrbit_radius_and_escape e hz hb2).2 (hDF.trans hFB)

include h e hz hk in
/-- The strict bound at every component vertex, using the actual critical
walk, transported Baumann slice and second vertex. -/
theorem borel_forward_slice_strict_at
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (by change 2 < sourceDistance h; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := borel_forward_slice_strict h e hz hk hb u hR p₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
