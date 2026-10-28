module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalShifts

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourAdjustedSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEqual

/-!
# Initial compatible paths at distance four in the original Borel graph

The small-image selectors retain both generating edge equations and both
full edge-seed fixed-subgroup comparisons for the paired critical paths.
The six-letter choices lift through the original cubic kernel E, using its
no-supplement property; E is not identified with its two-core.

Choose a strict two-edge Baumann slice if one exists. The paired trapped
kernel comparisons then force an escaping seed, for either mover comparison.
If all slices are small, an eligible seed escapes by the two-slice residual
calculation in the centrally generated case, or by the invariant two-seed
span argument outside central generation. Thus one of the paired paths has
an actual backward critical extension with generation and its full fixed
subgroup comparison on that very path.

Together with the adjusted large-image selection on both covers, this gives
an initial compatible pair without any forward-path assumption. Applying
the normalized-selection theorem either exhibits a large critical image or
constructs three overlapping critical paths with an actual residual
transporter and whole restricted-kernel normalization. This removes the
initial compatibility premise; the subsequent distance-four contradiction,
CoreExhaustion and exceptional reconstruction remain separate obligations.

Both full moving covers and their central attachments are retained. The
literal original c.L,d.S applications are in OriginalSylowExceptional.
Private imports reuse the established six-letter choices and path constructor
within this exceptional reconstruction package.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.8) and the initial selection in (5.12), printed
pp.915--920,924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders.Six
open BorelSelection Exhaustion.LargeDistance.CubicFull.PlaneSelection

private theorem initial_fixed_choices (u : S) (t : Fin 15) :
    let c : alternatingGroup (Fin 6) := ⟨coordinate t,coordinate_even t⟩
    let w := u*c.val
    let k : alternatingGroup (Fin 6) := MulAut.conjNormal u (c*position)
    let x : alternatingGroup (Fin 6) := MulAut.conjNormal w shift
    let E := D.map (MulAut.conj u).toMonoidHom
    let P := E.map (MulAut.conj k.val).toMonoidHom
    E ⊔ P = ⊤ ∧ E.map (MulAut.conj x.val).toMonoidHom ⊔ P = ⊤ := by
  let c : alternatingGroup (Fin 6) := ⟨coordinate t,coordinate_even t⟩
  let w := u*c.val
  let k : alternatingGroup (Fin 6) := MulAut.conjNormal u (c*position)
  let x : alternatingGroup (Fin 6) := MulAut.conjNormal w shift
  change (D.map (MulAut.conj u).toMonoidHom) ⊔
      (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom = ⊤ ∧
    (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj x.val).toMonoidHom ⊔
      (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom = ⊤
  constructor
  · have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) (fixed_generators t).1
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj u).surjective] at hh
    convert hh using 1
    rw [map_conj_comp,map_conj_comp]
    congr 4
    change (u*(c.val*position.val)*u⁻¹)*u=u*(coordinate t*position.val)
    dsimp only [c]
    group
  · have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) (fixed_generators t).2
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj u).surjective] at hh
    have he : (D.map (MulAut.conj u).toMonoidHom) ⊔
        ((D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom).map
          (MulAut.conj x.val⁻¹).toMonoidHom = ⊤ := by
      convert hh using 1
      rw [map_conj_comp,map_conj_comp,map_conj_comp,map_conj_comp]
      congr 4
      change (w*shift.val*w⁻¹)⁻¹*((u*(c.val*position.val)*u⁻¹)*u) =
        u*(coordinate t*step.val*(coordinate t)⁻¹)*(coordinate t*position.val)
      dsimp only [w,c,step]
      change ((u*coordinate t)*shift.val*(u*coordinate t)⁻¹)⁻¹*
        ((u*(coordinate t*position.val)*u⁻¹)*u) =
        u*(coordinate t*shift.val⁻¹*(coordinate t)⁻¹)*(coordinate t*position.val)
      group
    have hm := congrArg (Subgroup.map (MulAut.conj x.val).toMonoidHom) he
    have cancel (B : Subgroup S) :
        (B.map (MulAut.conj x.val⁻¹).toMonoidHom).map (MulAut.conj x.val).toMonoidHom = B := by
      rw [map_conj_comp,mul_inv_cancel]
      exact map_id B
    rw [Subgroup.map_sup,cancel,map_top_of_surjective _ (MulAut.conj x.val).surjective] at hm
    exact hm

private theorem initial_choices (u a : S) (ha : a.IsSwap) :
    ∃ k x : alternatingGroup (Fin 6),
      let E := D.map (MulAut.conj u).toMonoidHom
      let P := E.map (MulAut.conj k.val).toMonoidHom
      let T := (borel.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom
      (P ⊔ zpowers a) ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        T ⊔ zpowers a = ⊤ ∧
        T ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        E ⊔ P = ⊤ ∧ E.map (MulAut.conj x.val).toMonoidHom ⊔ P = ⊤ := by
  let b := u⁻¹*a*u
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  obtain ⟨t,hc⟩ := coordinate_complete b hb
  let c : alternatingGroup (Fin 6) := ⟨coordinate t,coordinate_even t⟩
  let w := u*c.val
  let k : alternatingGroup (Fin 6) := MulAut.conjNormal u (c*position)
  let x : alternatingGroup (Fin 6) := MulAut.conjNormal w shift
  let f := (MulAut.conj w).toMonoidHom
  have ha' : f swap01 = a := by
    change (u*c.val)*swap01*(u*c.val)⁻¹=a
    calc
      _ = u*(c.val*swap01*c.val⁻¹)*u⁻¹ := by group
      _ = a := by rw [show c.val*swap01*c.val⁻¹=b from hc]; dsimp [b]; group
  have hP (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom =
      (B.map (MulAut.conj position.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (u*(c.val*position.val)*u⁻¹)*u=(u*c.val)*position.val
    group
  have hPx (A : Subgroup S) : (A.map f).map (MulAut.conj x.val).toMonoidHom =
      (A.map (MulAut.conj shift.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (w*shift.val*w⁻¹)*w=w*shift.val
    group
  have hAx : (zpowers a).map (MulAut.conj x.val).toMonoidHom =
      (zpowers (shift.val*swap01*shift.val⁻¹)).map f := by
    rw [←ha',←MonoidHom.map_zpowers,hPx,MonoidHom.map_zpowers]
    rfl
  refine ⟨k,x,?_⟩
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hP,hAx]
    have hh := congrArg (Subgroup.map f) standard_generators.1
    rwa [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh
  · rw [hP,hPx]
    have hh := congrArg (Subgroup.map f) standard_generators.2
    rwa [Subgroup.map_sup,map_top_of_surjective f (MulAut.conj w).surjective] at hh
  · rw [hP]
    have hh := congrArg (Subgroup.map f) step_borel_generators.1
    rwa [Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh
  · have hh := congrArg (Subgroup.map (MulAut.conj shift.val).toMonoidHom)
      step_borel_generators.2
    rw [Subgroup.map_sup,map_conj_comp] at hh
    have he : shift.val * step.val = 1 := by change shift.val * shift.val⁻¹ = 1; group
    rw [he] at hh
    change (borel.map (MulAut.conj position.val).toMonoidHom).map (MonoidHom.id S) ⊔
      (zpowers swap01).map (MulAut.conj shift.val).toMonoidHom = _ at hh
    rw [map_id,MonoidHom.map_zpowers,
      map_top_of_surjective _ (MulAut.conj shift.val).surjective] at hh
    have hm := congrArg (Subgroup.map f) hh
    rw [Subgroup.map_sup,map_top_of_surjective f (MulAut.conj w).surjective] at hm
    rw [hP,hAx]
    exact hm
  · exact (initial_fixed_choices u t).1
  · exact (initial_fixed_choices u t).2

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem initial_plane_lifts (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a) :
    ∃ g ∈ K, ∃ r ∈ K,
      let F := borelPlane h e hz hk u
      let P := F.map (MulAut.conj g).toMonoidHom
      let T := (Rg).map (MulAut.conj g).toMonoidHom
      (P ⊔ A) ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        T ⊔ A = ⊤ ∧ T ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        Rg ⊔ P = ⊤ ∧ (Rg).map (MulAut.conj r).toMonoidHom ⊔ P = ⊤ := by
  obtain ⟨k,x,hgen,hpair,hBfirst,hBsecond,hfirst,hsecond⟩ := initial_choices u a ha
  obtain ⟨g,hg,hgk⟩ : k.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨r,hr,hrx⟩ : x.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact x.property
  let F := borelPlane h e hz hk u
  let P := F.map (MulAut.conj g).toMonoidHom
  have hFm : F.map π = D.map (MulAut.conj u).toMonoidHom :=
    borelPlane_image h e hz hk u hR
  have hPm : P.map π = (D.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom := by
    rw [selection_map_conj,hFm,hgk]
  have hQP : pCore 2 M ≤ P := by
    have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
    rw [←hQ]
    exact map_mono (borelPlane_core_le h e hz hk u)
  have lift (B : Subgroup M) (hQB : pCore 2 M ≤ B) (hB : B.map π = ⊤) : B = ⊤ := by
    have hBE : B ⊔ extensionKernel h = ⊤ := by
      have he := congrArg (Subgroup.comap π) hB
      rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
    have hEB := extensionKernel_no_supplement h B (hBE ▸ (le_top : K ≤ ⊤))
    rw [extensionKernel_twoCore h,sup_of_le_left hQB] at hEB
    rwa [sup_of_le_left hEB] at hBE
  refine ⟨g,hg,r,hr,?_,?_,?_,?_,?_,?_⟩
  · apply lift _ (hQP.trans (le_sup_left.trans le_sup_left))
    rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj π A r,hPm,hA,hrx]
    exact hgen
  · apply lift _ (hQP.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π P r,hPm,hrx]
    exact hpair
  · have hQR : pCore 2 M ≤ (Rg).map (MulAut.conj g).toMonoidHom := by
      have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
        mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
      rw [←hQ]
      exact map_mono h.relative_radical.twoCore_le
    apply lift _ (hQR.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π Rg g,hR,hA,hgk]
    exact hBfirst
  · have hQR : pCore 2 M ≤ (Rg).map (MulAut.conj g).toMonoidHom := by
      have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
        mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
      rw [←hQ]
      exact map_mono h.relative_radical.twoCore_le
    apply lift _ (hQR.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π Rg g,selection_map_conj π A r,hR,hA,hgk,hrx]
    exact hBsecond

  · apply lift _ (hQP.trans le_sup_right)
    rw [Subgroup.map_sup,hR,hPm]
    apply top_unique
    rw [←hfirst]
    exact sup_le_sup (map_mono BorelCalculation.plane_le_borel) le_rfl
  · apply lift _ (hQP.trans le_sup_right)
    rw [Subgroup.map_sup,selection_map_conj π Rg r,hR,hPm,hrx]
    apply top_unique
    rw [←hsecond]
    exact sup_le_sup (map_mono (map_mono BorelCalculation.plane_le_borel)) le_rfl
include h e hz hk in
private theorem initial_mover_chart (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) (v : M) :
    edgeOffenderJoin (alpha Rg) (act Rg ((embedM Rg v)⁻¹) (beta Rg)) =
      ((borelPlane h e hz hk u).map (MulAut.conj v).toMonoidHom).map (embedM Rg) := by
  let i := embedM Rg
  have fixed (v : M) : act Rg ((i v)⁻¹) (alpha Rg) = alpha Rg := by
    have hv : (i v)⁻¹ ∈ stabilizer Rg (alpha Rg) := by
      change (i v)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨v⁻¹,by simp only [i,map_inv]⟩
    exact hv
  let j := i.comp (MulAut.conj v).toMonoidHom
  have hadj : Adjacent Rg (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) := by
    rw [←fixed v]
    exact (adjacent_act_iff Rg ((i v)⁻¹) (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
  have hQ : (pCore 2 M).map (MulAut.conj v).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
  have hW : (W).map (MulAut.conj v).toMonoidHom = W := by
    let := h.relative_normal
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
  have hJR : (Rg).map j = Q Rg (act Rg ((i v)⁻¹) (beta Rg)) := by
    rw [Q_act,Q_beta,inv_inv]
    change (Rg).map (i.comp (MulAut.conj v).toMonoidHom) = _
    rw [←map_map]
    exact selection_map_conj i Rg v
  have hJQ : (pCore 2 M).map j = Q Rg (alpha Rg) := by
    rw [←map_map,hQ,Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  have hJW : (W).map j = U Rg (alpha Rg) := by
    rw [←map_map,hW,graph_U_map h e hz]
  have hh := remaining_join_in_chart h e hz hk u (Or.inr hR) rfl hadj j
    ((embedM_injective Rg).comp (MulAut.conj v).injective) hJR hJQ hJW
  simpa only [j,map_map] using hh

include h e hz hk in
private theorem initial_graph_selectors_base (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
      (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      Q Rg (beta Rg) ⊔ edgeOffenderJoin (alpha Rg) t = stabilizer Rg (alpha Rg) ∧
      Q Rg (act Rg x (beta Rg)) ⊔ edgeOffenderJoin (alpha Rg) t = stabilizer Rg (alpha Rg) := by
  let i := embedM Rg
  let F := borelPlane h e hz hk u
  let A := (Z Rg z).comap i
  have hAm : A.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  obtain ⟨g,hg,r,hr,hgen,hpair,hBfirst,hBsecond,hfirstgen,hsecondgen⟩ :=
    initial_plane_lifts h e hz hk u hR A a ha hA
  let f := (i g)⁻¹
  let x := (i r)⁻¹
  let t := act Rg f (beta Rg)
  have fixed (v : M) : act Rg ((i v)⁻¹) (alpha Rg) = alpha Rg := by
    have hv : (i v)⁻¹ ∈ stabilizer Rg (alpha Rg) := by
      change (i v)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨v⁻¹,by simp only [i,map_inv]⟩
    exact hv
  have hat : Adjacent Rg (alpha Rg) t := by
    rw [←fixed g]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←fixed r]
    exact (adjacent_act_iff Rg x (alpha Rg) t).mpr hat
  have chart (v : M) := initial_mover_chart h e hz hk u hR v
  have ht : edgeOffenderJoin (alpha Rg) t = (F.map (MulAut.conj g).toMonoidHom).map i := chart g
  have htt : act Rg x t = act Rg ((i (r*g))⁻¹) (beta Rg) := by
    dsimp [t,x,f]
    rw [map_mul,mul_inv_rev,act_mul]
  have ht' : edgeOffenderJoin (alpha Rg) (act Rg x t) =
      ((F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj r).toMonoidHom).map i := by
    rw [htt,chart]
    congr 1
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (r*g)*v*(r*g)⁻¹=r*(g*v*g⁻¹)*r⁻¹
    group
  have map_top (B : Subgroup M) (hB : B = ⊤) : B.map i = stabilizer Rg (alpha Rg) := by
    rw [hB,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base Rg).symm
  have hG := map_top _ hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj i A r,hAm,←ht] at hG
  have hZ : (Z Rg z).map (MulAut.conj (i r)).toMonoidHom = Z Rg (act Rg x z) := by
    rw [Z_act,show x⁻¹=i r from inv_inv _]
  rw [hZ] at hG
  have hJJ := map_top _ hpair
  rw [Subgroup.map_sup,←ht,←ht'] at hJJ
  have hQt : ((Rg).map (MulAut.conj g).toMonoidHom).map i = Q Rg t := by
    rw [Q_act,Q_beta,inv_inv]
    exact selection_map_conj i Rg g
  have hBfirst' := map_top _ hBfirst
  rw [Subgroup.map_sup,hQt,hAm] at hBfirst'
  have hBsecond' := map_top _ hBsecond
  rw [Subgroup.map_sup,hQt,selection_map_conj i A r,hAm,hZ] at hBsecond'
  have hGfirst := map_top _ hfirstgen
  rw [Subgroup.map_sup,←Q_beta,←ht] at hGfirst
  have hGsecond := map_top _ hsecondgen
  rw [Subgroup.map_sup,selection_map_conj i Rg r,←Q_beta,←ht] at hGsecond
  have hQx : (Q Rg (beta Rg)).map (MulAut.conj (i r)).toMonoidHom =
      Q Rg (act Rg x (beta Rg)) := by
    rw [Q_act,show x⁻¹=i r from inv_inv _]
  rw [hQx] at hGsecond
  exact ⟨t,hat,x,fixed r,hG,hJJ,hBfirst',hBsecond',hGfirst,hGsecond⟩

include h e hz hk in
private theorem initial_seed_selectors_base (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hfirst : p.walk.getVert 1 = beta Rg) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
      (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      (Z Rg (p.walk.getVert 1) ⊓ centralizer
        (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
      (Z Rg (act Rg x (p.walk.getVert 1)) ⊓ centralizer
        (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) := by
  obtain ⟨t,hat,x,hx,hgen,hpair,hgen₀,hgen₁,hGfirst,hGsecond⟩ :=
    initial_graph_selectors_base h e hz hk u hR p hsmall
  rw [←hfirst] at hGfirst hGsecond
  have full_fixed (v : Vertex Rg) (hv : color Rg v = true)
      (hgen : Q Rg v ⊔ edgeOffenderJoin (alpha Rg) t = stabilizer Rg (alpha Rg)) :
      Z Rg v ⊓ centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (terminal_edge_seed_central hv)))
      (le_centralizer_iff.mp inf_le_right)
  have hcol : color Rg (p.walk.getVert 1) = true := by rw [hfirst]; rfl
  exact ⟨t,hat,x,hx,hgen,hpair,hgen₀,hgen₁,
    full_fixed _ hcol hGfirst,full_fixed _ (by rw [action_preserves_color,hcol]) hGsecond⟩
include h e hz hk in
private theorem initial_slice_choice {t : Vertex Rg}
    (hat : Adjacent Rg (alpha Rg) t) : ∃ c, Adjacent Rg c t ∧
      ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∧
      (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∨
        ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t → Adjacent Rg c t →
          (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) := by
  have hb2 := distance_gt_two h e hz hk
  by_cases hstrict : ∃ c t : Vertex Rg, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)
  · obtain ⟨c₀,t₀,hat₀,hct₀,hi⟩ := hstrict
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat₀ hat
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hy))
    have hi' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg y c₀)) := by
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
      exact hi
    refine ⟨act Rg y c₀,?_,?_,Or.inl hi'⟩
    · rw [←hyt]
      exact (adjacent_act_iff Rg y _ _).mpr hct₀
    · intro hn
      have hh := relIndex_eq_one.mpr hn
      omega
  · have hbase (c t : Vertex Rg) (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t) :
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
      by_contra! hi
      exact hstrict ⟨c,t,hat,hct,hi⟩
    have hall (a c t : Vertex Rg) (ha : color Rg a = false)
        (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
        (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
      obtain ⟨y,hy⟩ := exists_mVertex_of_color Rg ha
      have hya : act Rg y⁻¹ a = alpha Rg := by
        rw [hy,act_mVertex,mul_inv_cancel]
        rfl
      have hat' : Adjacent Rg (alpha Rg) (act Rg y⁻¹ t) := by
        rw [←hya]
        exact (adjacent_act_iff Rg y⁻¹ _ _).mpr hat
      have hh := hbase _ _ hat' ((adjacent_act_iff Rg y⁻¹ _ _).mpr hct)
      rw [←hya,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) hb2 y⁻¹ a ha,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹⁻¹).injective] at hh
      exact hh
    obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb2 rfl hat
    exact ⟨c,hct,hel,Or.inr hall⟩


include h e hz hk in
private theorem initial_small_pair_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hfirst : p.walk.getVert 1 = beta Rg) :
    ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4 ∧
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  obtain ⟨t,hat,x,hx,hgen,hpair,hgen₀,hgen₁,hfix₀,hfix₁⟩ :=
    initial_seed_selectors_base h e hz hk u hR p hp hfirst
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hpact : ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
      ∀ i, s.walk.getVert i = act Rg x (p.walk.getVert i) := by
    have hh : ∃ s : CriticalPath Rg (sourceGeometry h)
        (act Rg x (alpha Rg)) (act Rg x z),
        ∀ i, s.walk.getVert i = act Rg x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  obtain ⟨s,hsverts⟩ := hpact
  have hs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  obtain ⟨c,hct,hel,hchoice⟩ := initial_slice_choice h e hz hk hat
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hat
    have hh' := adjacent_color_ne Rg hct
    change false ≠ color Rg t at hh
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have escape : ¬ Z Rg c ≤ Q Rg (p.walk.getVert 2) ∨
      ¬ Z Rg c ≤ Q Rg (s.walk.getVert 2) := by
    by_contra! hbad
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hsl : s.walk.length = 4 := s.length_eq_b.trans hb
    have hbad₀ : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
      simpa only [hl,Nat.reduceSub] using hbad.1
    have hbad₁ : Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2)) := by
      simpa only [hsl,Nat.reduceSub] using hbad.2
    by_cases hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
        (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
    · rcases hchoice with hstrict | hsmall
      · by_cases heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t
        · exact borel_equal_strict_paired_not_trapped h e hz hk u hR p x hx s hsverts
            hp hs hat hct heq hgen hpair hbad₀ hbad₁ hstrict
        · exact borel_central_distinct_strict_escape h e hz hk u hR p hp hat hct
            hgen₀ hsplit heq hstrict hbad₀
      · have hc2 : color Rg (p.walk.getVert 2) = false :=
          (p.vertex_color (by omega)).mpr (by decide)
        have hc3 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
          (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
        have hz3 : Adjacent Rg z (p.walk.getVert 3) := by
          have hh := (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 3) (by omega))
          change Adjacent Rg (p.walk.getVert 3) (p.walk.getVert 4) at hh
          rw [←hl,SimpleGraph.Walk.getVert_length] at hh
          exact adjacent_symm Rg hh
        have hpre : (B Rg (p.walk.getVert (p.walk.length-2))
            ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
          simpa only [hl,Nat.reduceSub] using hsmall _ _ _ hc2 hc3 hz3
        exact hel ((DistanceEight.U_le_Z Rg c).trans
          (borel_central_two_slice_trapped_le_slice h e hz hk u hR p hat hct hgen₀
            hsplit (hsmall _ _ _ rfl hat hct) hpre hbad₀))
    · exact hel ((DistanceEight.U_le_Z Rg c).trans
        (borel_trapped_slice_of_not_central_generation h e hz hk u hR p s hp hs
          hat hct hsplit hgen hbad₀ hbad₁))
  rcases escape with hn | hn
  · obtain ⟨q,hqt,hover⟩ := four_prepend_selected h hb p hc hat hct hn
    exact ⟨z,p,hp,c,t,q,hqt,hover,hgen₀,hfix₀⟩
  · obtain ⟨q,hqt,hover⟩ := four_prepend_selected h hb s hc hat hct hn
    refine ⟨_,s,hs,c,t,q,hqt,hover,hgen₁,?_⟩
    simpa only [hsverts] using hfix₁

include h e hz hk in
/-- A small critical image supplies initial compatible paths, including
whole-stabilizer generation and the full fixed-subgroup comparison on the
same path. No forward critical path or fixed-subgroup bound is assumed. -/
theorem borel_four_small_initial_compatible_paths
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4 ∧
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨x,hx,hxb⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hab (base_adjacent Rg)
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hpact : ∃ s : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      s.walk.getVert 1 = act Rg x (p.walk.getVert 1) :=
    ⟨p.act x,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa,hxb] at hpact
  obtain ⟨s,hs⟩ := hpact
  have hsmall : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  exact initial_small_pair_base h e hz hk u hR s hsmall hs

include h e hz hk in
/-- The original Borel graph has an initial compatible pair in every image
case and on both full covers. Its generation and fixed-subgroup comparison
are precisely the inputs consumed by distance-four normalized selection. -/
theorem borel_four_initial_compatible_paths
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ a z y, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y,
        r.walk.getVert 2 = z ∧
        Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2) ∧
        Z Rg (p.walk.getVert 3) ⊓ centralizer
          (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  obtain ⟨z,hzcrit⟩ := criticalPair_exists Rg (alpha Rg)
    ((sourceGeometry h).exists_critical (alpha Rg) rfl)
  let p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z := CriticalPath.ofPair rfl hzcrit
  have pair : ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    by_cases hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4
    · obtain ⟨z',s,_,d,t,q,hqt,hover,hgen,hfix⟩ :=
        borel_four_small_initial_compatible_paths h e hz hk u hR p hp
      exact ⟨z',s,d,t,q,hqt,hover,hgen,hfix⟩
    · obtain ⟨A,_,_,_,_,d,t,x,_,_,_,_,_,_,hfix,_,hgen,q,hqt,hover,_⟩ :=
        borel_four_large_adjusted_backward_selection h e hz hk u hR p (by omega)
      exact ⟨z,p,d,t,q,hqt,hover,hgen,hfix⟩
  obtain ⟨z',s,d,t,q,hqt,hover,hgen,hfix⟩ := pair
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hq3 : q.walk.getVert 3 = s.walk.getVert 1 := hover 1 (by decide)
  refine ⟨d,s.walk.getVert 2,z',q,?_⟩
  rw [hqa]
  exact ⟨s,rfl,by simpa only [hqt] using hgen,by simpa only [hqt,hq3] using hfix⟩

include h e hz hk in
/-- Initial compatibility feeds the existing normalized-selection theorem.
Thus either a genuine large critical image remains, or three overlapping
critical paths have both generating edges, both full fixed-subgroup
comparisons, an actual residual transporter and full-kernel normalization.
There is no assumed initial-path or normalization callback. -/
theorem borel_four_initial_normalized_or_large
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (∃ a z : Vertex Rg, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
    ∃ a z y, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y,
        r.walk.getVert 2 = z ∧
        Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2) ∧
        (Q Rg z).relIndex (Z Rg a) < 4 ∧
        (Z Rg (p.walk.getVert 3) ⊓ centralizer
          (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
        ∃ d t, ∃ x ∈ Ltilde Rg a,
          act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
          Adjacent Rg a t ∧ Adjacent Rg d t ∧
          Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
          (Z Rg (p.walk.getVert 1) ⊓ centralizer
            (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
            q.walk.getVert 1 = t ∧ (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            X Rg z ≤ normalizer
              (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
                Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨a,z,y,p,r,hrz,hgen,hfixed⟩ := borel_four_initial_compatible_paths h e hz hk u hR
  by_cases hp : (Q Rg z).relIndex (Z Rg a) < 4
  · exact Or.inr ⟨a,z,y,p,r,hrz,hgen,hp,hfixed,
      borel_four_normalized_backward_selection h e hz hk u hR p r hrz hgen hp hfixed⟩
  · exact Or.inl ⟨a,z,p,by omega⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
