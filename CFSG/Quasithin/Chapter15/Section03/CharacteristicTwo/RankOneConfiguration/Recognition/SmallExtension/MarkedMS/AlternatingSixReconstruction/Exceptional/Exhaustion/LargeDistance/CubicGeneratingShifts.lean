module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullPointSlices

/-!
# Generating backward shifts for both cubic critical images

The full point-core branch now supplies a backward critical shift through
a generating edge for every critical walk above distance four. For a large
critical image, its controlled reverse subactor contains an actual even
involution in the original symmetric quotient. A component conjugate of
the point core generates with that involution. The no-supplement property
lifts generation across the entire cubic kernel. If the selected neighboring
seed lay in the old predecessor core, its join with the starting seed
would be normal under this generating pair and the controlled actor would
force it into the Baumann slice, contrary to the strict bound.

Combining this construction with the existing small-image shift removes
all critical-image and eligibility premises. Conjugation transports the
same edge, local transporter and complete walk overlap to every original
vertex. The whole-core and literal C.1.32 consumers retain the full
point-core equality and both moving covers. Radical-image identification,
R₄/R₆ and the terminal distance exclusions, natural exhaustion and both
full reconstruction outcomes remain required.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.11), pp.919--924.
The all-vertex transport adapts the checked walk calculation in
Natural.Exhaustion.LargeDistance.SectionFive.ShiftChain; no natural and
exceptional graph, kernel or actor is identified.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem full_point_even_actor_generating_neighbor
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (A.comap (embedM Rg)).map π)
    (ha2 : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
  let := h.relative_normal
  let A₀ := A.comap (embedM Rg)
  have hmapA : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base Rg))
  obtain ⟨k,hkgen⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
    u ⟨a,haeven⟩ (by simpa only [Subgroup.orderOf_mk] using ha2)
  have hkL : k.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hm : ((Rg).map (MulAut.conj g).toMonoidHom).map π =
      ((Rg).map π).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change π (g*x*g⁻¹) = k.val*π x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let F := (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀
  have hQF : pCore 2 M ≤ F := by
    rw [←hQ]
    exact (map_mono h.relative_radical.twoCore_le).trans le_sup_left
  have hfullF : F.map π = ⊤ := by
    rw [Subgroup.map_sup,hm,hfull]
    apply top_unique
    rw [←hkgen]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  have hFE : F ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) hfullF
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEF : extensionKernel h ≤ F := by
    have he := extensionKernel_no_supplement h F (hFE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at he
    exact he
  have hgen : (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    change F = ⊤
    rwa [sup_of_le_left hEF] at hFE
  let f := (embedM Rg g)⁻¹
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  refine ⟨act Rg f (beta Rg),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr
      (base_adjacent Rg)
  · have hh := congrArg (Subgroup.map (embedM Rg)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    have hmapR : ((Rg).map (embedM Rg)).map (MulAut.conj f⁻¹).toMonoidHom =
        ((Rg).map (MulAut.conj g).toMonoidHom).map (embedM Rg) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM Rg x*(f⁻¹)⁻¹=embedM Rg (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include h e hz hk in
/-- A large critical image supplies its actual controlled even subactor
and an incident edge generating with that same subactor. -/
theorem large_full_point_generating_actor
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ U Rg a' ∧ IsPGroup 2 A ∧
      (¬ A ≤ Q Rg (alpha Rg)) ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg) ∧
      ∃ t, Adjacent Rg (alpha Rg) t ∧ Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
  obtain ⟨A,hAU,hdisp,a,ha,ha2,heven⟩ := critical_radius_even_actor h e hz hk p hlarge
  have hAG : A ≤ stabilizer Rg (alpha Rg) :=
    (hAU.trans (DistanceEight.U_le_Z Rg a')).trans
      (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) p.critical)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg a')).to_le
    (hAU.trans (DistanceEight.U_le_Z Rg a'))
  have hAn : ¬ A ≤ Q Rg (alpha Rg) := by
    intro hn
    have hcom : A.comap (embedM Rg) ≤ pCore 2 M := by
      have hh := comap_mono (f := embedM Rg) hn
      rwa [Q_alpha_comap Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    have hm : (A.comap (embedM Rg)).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [CubicAction.projection_kernel h e hz hk]
      exact hcom.trans le_sup_right
    have ha1 : a = 1 := mem_bot.mp (hm ▸ ha)
    rw [ha1,orderOf_one] at ha2
    contradiction
  exact ⟨A,hAU,htwo,hAn,hdisp,
    full_point_even_actor_generating_neighbor h e hz hk u hfull A hAG a ha ha2 heven⟩

include h e hz in
private theorem controlled_actor_backward_not_le
    (hb : 2 < sourceDistance h)
    {a' c t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (htwo : IsPGroup 2 A) (hAn : ¬ A ≤ Q Rg (alpha Rg))
    (hdisp : ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg))
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ A = stabilizer Rg (alpha Rg))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let D := Z Rg c ⊔ Z Rg (alpha Rg)
  have hDV : D ≤ V Rg (alpha Rg) :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hct
  have hVG : V Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) :=
    (sourceGeometry h).V_local _ rfl hb
  have hDA : ⁅D,A⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) A (Z Rg (alpha Rg))
      (Z_normalized Rg _) ((le_sup_left.trans hDV).trans hVG) (Z_le_stabilizer Rg _)
    · exact (commutator_mono (le_inf (le_sup_left.trans hDV) hbad) le_rfl).trans hdisp
    · exact le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg _))
  have hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hct)
      (le_normalizer_iff_commutator_le_left.mpr (hDA.trans le_sup_right))
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb rfl D A
    hDV hDN hAG htwo hAn hDA
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans hDB)
  have hh := relIndex_eq_one.mpr hUB
  omega

include h e hz hk in
/-- The large-image backward step uses an edge generating with its
controlled subactor. Every overlap uses the same actual conjugator. -/
theorem large_full_point_backward_shift_of_two_lt_slice
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)))
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
      act Rg g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg g delta)) := by
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_full_point_generating_actor h e hz hk u hfull p hlarge
  have hAZ : A ≤ Z Rg a' := hAU.trans (DistanceEight.U_le_Z Rg a')
  have hZG : Z Rg a' ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hindexc : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    exact controlled_actor_backward_not_le h e hz hb p A (hAZ.trans hZG) htwo hAn hdisp hat hct hgen hindexc
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨t,hat,?_,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,hindexc⟩
  exact le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
    (hgen.symm.le.trans (sup_le_sup_left hAZ _))

include h e hz hk in
/-- Every critical walk above distance four in the full point-core branch
has a strict forward slice and a backward shift through a generating edge.
There is no image-size or eligibility premise. -/
theorem full_point_generating_backward_shift
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ∧
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (act Rg g (p.walk.getVert 2))) := by
  by_cases hs : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4
  · exact full_point_small_backward_shift h e hz hk hb u hfull p hs
  · have hi := full_point_forward_slice_gt_two e hz hk hb u hfull p
    refine ⟨hi,large_full_point_backward_shift_of_two_lt_slice h e hz hk
      (by omega) u hfull p (by omega) ?_ hi⟩
    apply adjacent_symm Rg
    apply (cosetGraph_adj Rg _ _).mp
    exact p.walk.adj_getVert_succ (i := 1) (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)

omit hk in
include h e hz in
/-- Whole-core application of the strict forward slice bound and its
actual backward path. Both full covers and the original odd kernel remain. -/
theorem coreExhaustion_or_cubic_full_point_generating_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,fun u hu hb4 a' p =>
      full_point_generating_backward_shift h e hz hk hb4 u hu p⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the proved strict forward slice and
backward shift. The remaining source cases and full reconstruction stay open. -/
theorem rankTwo_or_cubic_full_point_generating_shifts :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) :=
  (coreExhaustion_or_cubic_full_point_generating_shifts h e hz).imp (rankTwo_of_exhaustion h e hz) id

include h e hz hk in
private theorem full_point_generating_backward_step_base
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨_,t,hat,hgen,x,hx,hxt,q,hq,hover,_⟩ :=
    full_point_generating_backward_shift h e hz hk hb u hfull p
  refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hq,hover⟩
  rw [←hxt]
  apply (adjacent_act_iff Rg x _ _).mpr
  apply adjacent_symm Rg
  apply (cosetGraph_adj Rg _ _).mp
  exact p.walk.adj_getVert_succ (i := 1) (by
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega)

include h e hz hk in
/-- Above distance four both critical-image branches supply a backward shift.
The chosen local conjugator and every shared vertex are retained. -/
theorem full_point_generating_backward_step_at
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ c t x, x ∈ stabilizer Rg a ∧
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
  have base := full_point_generating_backward_step_base h e hz hk hb u hfull
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹)
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
  refine ⟨act Rg g c,act Rg g t,y,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act Rg y a = a
    rw [hy,show act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a from hx,hcancel]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat
  · exact (adjacent_act_iff Rg g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

omit hk in
include h e hz in
/-- Whole-core application with generating backward shifts at every vertex
of the original graph, retaining both covers and the actual point-core premise. -/
theorem coreExhaustion_or_cubic_full_point_generating_paths :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          ∃ c t x, x ∈ stabilizer Rg a ∧ act Rg x (p.walk.getVert 2) = c ∧
            Adjacent Rg a t ∧ Adjacent Rg c t ∧ Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun u hu hb4 _ _ p => full_point_generating_backward_step_at h e hz hk hb4 u hu p⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of generating backward paths at every
vertex. Terminal exclusion and both full reconstructions remain necessary. -/
theorem rankTwo_or_cubic_full_point_generating_paths :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          ∃ c t x, x ∈ stabilizer Rg a ∧ act Rg x (p.walk.getVert 2) = c ∧
            Adjacent Rg a t ∧ Adjacent Rg c t ∧ Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i :=
  (coreExhaustion_or_cubic_full_point_generating_paths h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
