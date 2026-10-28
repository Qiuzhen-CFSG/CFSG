module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalShifts

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors

/-!
# Compatible generating shifts on the original Borel graph

Every critical path above distance four has a generating backward shift,
including paths with a small critical image. The six-letter selector retains
both generation identities for one selected Borel and the two endpoint seeds.
Consequently either escaping seed can be used: transporting the second choice
back by the inverse conjugator preserves generation on the selected edge.
The lift uses the original cubic kernel E and its no-supplement property.

Three iterations construct the literal R4/R6 configuration of MS93 (5.10).
Both critical images and their commutators have order two; each commutator is
moved by its first edge kernel, and their join centralizes the common endpoint
radius. All path overlaps and the actual edge transporters are retained.
These facts apply to both full moving covers, with their central attachments,
and feed the literal original c.L,d.S source in OriginalSylowExceptional.
The subsequent mover comparison and terminal exclusions remain to be proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.10), printed pp.919--923.
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

private theorem generating_choices (u a : S) (ha : a.IsSwap) :
    ∃ k x : alternatingGroup (Fin 6),
      let E := D.map (MulAut.conj u).toMonoidHom
      let P := E.map (MulAut.conj k.val).toMonoidHom
      let T := (borel.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom
      (P ⊔ zpowers a) ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        T ⊔ zpowers a = ⊤ ∧
        T ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ := by
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
  refine ⟨?_,?_,?_,?_⟩
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
private theorem generating_plane_lifts (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a) :
    ∃ g ∈ K, ∃ r ∈ K,
      let F := borelPlane h e hz hk u
      let P := F.map (MulAut.conj g).toMonoidHom
      let T := (Rg).map (MulAut.conj g).toMonoidHom
      (P ⊔ A) ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        T ⊔ A = ⊤ ∧ T ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ := by
  obtain ⟨k,x,hgen,hpair,hBfirst,hBsecond⟩ := generating_choices u a ha
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
  refine ⟨g,hg,r,hr,?_,?_,?_,?_⟩
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

include h e hz hk in
private theorem generating_seed_selectors_base (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
      (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) := by
  let i := embedM Rg
  let F := borelPlane h e hz hk u
  let A := (Z Rg z).comap i
  have hAm : A.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  obtain ⟨g,hg,r,hr,hgen,hpair,hBfirst,hBsecond⟩ :=
    generating_plane_lifts h e hz hk u hR A a ha hA
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
  have chart (v : M) : edgeOffenderJoin (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) =
      (F.map (MulAut.conj v).toMonoidHom).map i := by
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
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hfirst hat
  exact ⟨t,hat,y,hy,hyt,x,fixed r,hG,hJJ,hBfirst',hBsecond'⟩


include h e hz hk in
private theorem generating_small_shift_base
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ c t y, y ∈ stabilizer Rg (alpha Rg) ∧
      act Rg y (p.walk.getVert 1) = t ∧
      act Rg y (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨t,hat,g,hg,hgt,x,hx,hgen,hpair,hgen₀,hgen₁⟩ :=
    generating_seed_selectors_base h e hz hk u hR p hp
  let c := act Rg g (p.walk.getVert 2)
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g (p.walk.getVert 2)))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact borel_forward_slice_strict h e hz hk hb u hR p
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hqs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hescape : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∨
      ¬ Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
    by_contra! hbad
    by_cases heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t
    · exact borel_equal_strict_paired_not_trapped h e hz hk u hR p x hx q hqverts
        hp hqs hat hct heq hgen hpair hbad.1 hbad.2 hstrict
    · by_cases hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
          (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
      · exact borel_central_distinct_strict_escape h e hz hk u hR p hp hat hct
          hgen₀ hsplit heq hstrict hbad.1
      · have hle := borel_trapped_slice_of_not_central_generation h e hz hk u hR
          p q hp hqs hat hct hsplit hgen hbad.1 hbad.2
        have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hle)
        omega
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧
        ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb2) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  rcases hescape with hescape | hescape
  · obtain ⟨b,hbt,hbo⟩ := extend _ p hescape
    exact ⟨c,t,g,hg,hgt,rfl,hat,hct,hgen₀,b,hbt,hbo⟩
  · obtain ⟨b,hbt,hbo⟩ := extend _ q hescape
    let y := g*x⁻¹
    have hy : y ∈ stabilizer Rg (alpha Rg) := mul_mem hg (inv_mem hx)
    have hyt : act Rg y (p.walk.getVert 1) = act Rg x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act Rg x⁻¹ c = act Rg y (p.walk.getVert 2) :=
      (act_mul Rg g x⁻¹ (p.walk.getVert 2)).symm
    have hxi : act Rg x⁻¹ (alpha Rg) = alpha Rg := (stabilizer Rg (alpha Rg)).inv_mem hx
    have hcancel (v : Vertex Rg) : act Rg x⁻¹ (act Rg x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    have hgen₂ : Q Rg (act Rg x⁻¹ t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
      have he := congrArg (Subgroup.map (MulAut.conj x⁻¹⁻¹).toMonoidHom) hgen₁
      rw [Subgroup.map_sup,←Q_act Rg x⁻¹,←Z_act Rg x⁻¹,←stabilizer_act Rg x⁻¹,
        hcancel,hxi] at he
      exact he
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act Rg x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by rw [hlen,hqverts,hcancel]
    have hex : ∃ w : CriticalPath Rg (sourceGeometry h)
        (act Rg x⁻¹ c) (act Rg x⁻¹ (q.walk.getVert (q.walk.length-2))),
        w.walk.getVert 1 = act Rg x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
      refine ⟨b.act x⁻¹,?_,?_⟩
      · simp only [CriticalPath.act,actWalk_getVert,hbt]
      · intro i hi
        have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
        simp only [CriticalPath.act,actWalk_getVert,hbo i hiq,hqverts,hcancel]
    rw [hend] at hex
    obtain ⟨w,hwt,hwo⟩ := hex
    refine ⟨act Rg x⁻¹ c,act Rg x⁻¹ t,y,hy,hyt,hstart.symm,?_,
      (adjacent_act_iff Rg x⁻¹ _ _).mpr hct,hgen₂,w,hwt,hwo⟩
    simpa only [hxi] using (adjacent_act_iff Rg x⁻¹ _ _).mpr hat


include h e hz hk in
private theorem generating_backward_step_base
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  by_cases hs : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4
  · exact generating_small_shift_base h e hz hk hb u hR p hs
  · exact borel_large_backward_step_at h e hz hk hb u hR p (by omega)

/-- Above distance four every critical image supplies a generating backward
shift. The chosen local conjugator and every shared vertex are retained. -/
theorem borel_backward_step_at
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ c t x, x ∈ stabilizer Rg a ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg a t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := generating_backward_step_base h e hz hk hb u hR
    (z := act Rg g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹)
  change act Rg x ((actWalk Rg g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex Rg) :
      act Rg y v = act Rg g (act Rg x (act Rg g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath Rg (sourceGeometry h)
      (act Rg g c)
      (act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act Rg g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act Rg g) hq1
    · intro i hi
      have he := congrArg (act Rg g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act Rg g ((actWalk Rg g⁻¹ p.walk).getVert
      ((actWalk Rg g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act Rg g c,act Rg g t,y,?_,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act Rg y a = a
    rw [hy,show act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a from hx,hcancel]
  · rw [hy]
    have hh := congrArg (act Rg g) hxt
    simpa only [CriticalPath.act,actWalk_getVert] using hh
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat
  · exact (adjacent_act_iff Rg g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


include h e hz hk in
/-- Every critical path has a generating shift with its literal edge transporter. -/
theorem borel_backwardShift
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ∃ q : BorelBackwardShift (h := h) p,
      act Rg q.transporter (p.walk.getVert 1) = q.edge := by
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hqo⟩ :=
    borel_backward_step_at h e hz hk hb u hR p
  exact ⟨⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩,hxt⟩

include h e hz hk in
/-- Three successive generating shifts realize the source R4/R6 configuration.
Both critical images are two, both lines are moved by their first edge kernels,
and the same endpoint radius centralizes both lines. -/
theorem borel_three_backward_shifts
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
      (t : BorelBackwardShift (h := h) r.path),
      act Rg q.transporter (p.walk.getVert 1) = q.edge ∧
      act Rg r.transporter (q.path.walk.getVert 1) = r.edge ∧
      act Rg t.transporter (r.path.walk.getVert 1) = t.edge ∧
      q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) ∧
      r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) ∧
      let z₄ := p.walk.getVert (p.walk.length-4)
      let z₆ := p.walk.getVert (p.walk.length-6)
      let H₄ := ⁅Z Rg r.start,Z Rg z₄⁆
      let H₆ := ⁅Z Rg t.start,Z Rg z₆⁆
      (Q Rg z₄).relIndex (Z Rg r.start) = 2 ∧
      (Q Rg z₆).relIndex (Z Rg t.start) = 2 ∧
      Nat.card H₄ = 2 ∧ Nat.card H₆ = 2 ∧
      (¬ H₄ ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) ∧
      (¬ H₆ ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg))) ∧
      (¬ Q Rg r.edge ≤ centralizer (H₄ : Set (FreeAmalgam Rg))) ∧
      (¬ Q Rg t.edge ≤ centralizer (H₆ : Set (FreeAmalgam Rg))) ∧
      H₄ ⊔ H₆ ≤ centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) := by
  obtain ⟨q,hqe⟩ := borel_backwardShift h e hz hk hb u hR p
  obtain ⟨r,hre⟩ := borel_backwardShift h e hz hk hb u hR q.path
  obtain ⟨t,hte⟩ := borel_backwardShift h e hz hk hb u hR r.path
  have hfour := two_borel_backward_shifts_small_moving h e hz hk hb p q r
  have hsix := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hp : p.walk.length = sourceDistance h := p.length_eq_b
  have hq : q.path.walk.length = sourceDistance h := q.path.length_eq_b
  have hr : r.path.walk.length = sourceDistance h := r.path.length_eq_b
  have h6 : 6 ≤ sourceDistance h := by
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he
    omega
  have he4 : q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) := by
    rw [show q.path.walk.length-2 = (p.walk.length-4)+2 by omega]
    exact q.overlap _ (by omega)
  have he6 : r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) := by
    rw [show r.path.walk.length-2 = (q.path.walk.length-4)+2 by omega,r.overlap _ (by omega)]
    rw [show q.path.walk.length-4 = (p.walk.length-6)+2 by omega]
    exact q.overlap _ (by omega)
  have hVQ : V Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q Rg (q.path.walk.getVert (q.path.walk.length-2)) :=
    V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color (by change 2 < sourceDistance h; omega)
  have hVQ₆ : V Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q Rg (r.path.walk.getVert (r.path.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) r.path.end_color
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    change r.path.walk.length-(r.path.walk.length-2)+2 < sourceDistance h
    omega
  have endpoint_commutator_le {a z : Vertex Rg}
      (w : CriticalPath Rg (sourceGeometry h) a z) : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg z := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Z_le_stabilizer_of_dist_le a _ w.critical.1.le).trans (Z_normalized Rg z))
  have hcentral : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ⊔
      ⁅Z Rg t.start,Z Rg (r.path.walk.getVert (r.path.walk.length-2))⁆ ≤
      centralizer (V Rg (q.path.walk.getVert (q.path.walk.length-2)) : Set (FreeAmalgam Rg)) := by
    apply sup_le
    · exact (endpoint_commutator_le r.path).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg _ r.path.end_color)).trans (centralizer_le hVQ))
    · exact (endpoint_commutator_le t.path).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg _ t.path.end_color)).trans (centralizer_le hVQ₆))
  dsimp only at hfour hsix ⊢
  rw [r.first,he4] at hfour
  rw [t.first,he6] at hsix
  simp only [he4,he6] at hcentral
  exact ⟨q,r,t,hqe,hre,hte,he4,he6,hfour.2.1,hsix.2.1,
    hfour.2.2.2.1,hsix.2.2.2.1,hfour.1,hsix.1,hfour.2.2.2.2,hsix.2.2.2.2,hcentral⟩


end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
