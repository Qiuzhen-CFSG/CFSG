module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneDerivedCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminal

/-!
# Residual envelopes of the original cubic plane configuration

For a generating critical path with strict backward slice, let P be the
selected span, Y its intersection with the midpoint two-core, and
C = [Q_c,L̃_c] the entire residual core at that midpoint. The line
Y' = P' is noncentral at c. The envelope Y join C is normalized by the
midpoint stabilizer, so the actual cover's invariant-subspace calculation
puts all of U_c in its derived subgroup. Commutator expansion gives
|U_c| ≤ 2 |C'| |[Y,C]|. The original selector supplies such a path;
the two residual commutators cannot both have order at most two.

At the start, residual idempotence puts P' in the derived subgroup of the
entire residual core. The literal embedding then shows that the original
intrinsic blockU L is nonabelian in this branch. Separately, U ≤ Q' and
the three-subgroups lemma give U ≤ [Q,[Q,K]], of order at least sixteen,
where Q = O₂(L join R) and K = L.subgroupOf (L join R).

The whole-core and C.1.32 consumers supply the selected path and slices.
These are lower bounds, not the terminal contradiction. Distance four,
uniformly small images, the remaining plane cases and the Borel branch
remain explicit. Both full covers and their central attachments remain,
as do the original nonsylow radical and projection kernel E with odd E/Q.
No replacement graph is identified with this original cubic graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), (3.10) and (5.12), printed pp.879--881,926--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "W₀" => (⁅centralOmega L R,K⁆ : Subgroup M)

include h e hz hk in
/-- The entire residual core retains the selected nonzero derived line. -/
theorem plane_generating_residual_derived_nontrivial
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg))) :
    ⁅⁅pCore 2 M,K⁆,⁅pCore 2 M,K⁆⁆ ≠ ⊥ := by
  have hb := distance_gt_two h e hz hk
  have hd := plane_generating_midpoint_span_line h e hz hk u hR hb4 hsmall p hmid hback
  have hn := plane_generating_midpoint_span_nonabelian h e hz hk u hR hb4 hsmall p hmid hback
  have hPQ : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ Q Rg (alpha Rg) :=
    (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hPC : forwardMovedSpan Rg (p.walk.getVert 2) ≤
      ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ := commutator_mono hPQ le_rfl
  have hle : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≤
      ⁅⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆,
        ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆⁆ := by
    rw [selected_span_derived_eq_moved h hb p
      (hd.2.2.2.1.trans (centralizer_le (Ltilde_le_stabilizer _)))]
    exact commutator_mono hPC hPC
  intro he
  have hm := congrArg (Subgroup.map (embedM Rg)) he
  rw [map_commutator,map_commutator,←h.relative_residual,←Ltilde_alpha,
    ←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,Subgroup.map_bot] at hm
  exact hn (le_bot_iff.mp (hle.trans_eq hm))

include h in
private theorem moved_cover_idempotent : ⁅W₀,K⁆ = W₀ := by
  let := h.relative_normal
  exact commutator_isPPerfect_idempotent K (centralOmega L R)
    h.relative_twoPerfect (pCore_isPGroup.to_le (omegaCenter_le _))
    le_normalizer_of_normal

include h in
private theorem derived_residual_commutator_le :
    ⁅⁅pCore 2 M,pCore 2 M⁆,K⁆ ≤ ⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ := by
  let := h.relative_normal
  apply commutator_commutator_le_of_rotate_of_le_normalizer
    le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
  · rw [commutator_comm]
  · rw [commutator_comm K (pCore 2 M),commutator_comm]

include h e hz hk in
/-- The full moved cover lies in [Q,[Q,K]], including its central attachment. -/
theorem plane_four_small_images_residual_movement
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    W₀ ≤ ⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ ∧
      16 ≤ Nat.card (⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ : Subgroup M) := by
  have hd := (plane_four_small_images_derived_core h e hz hk u hR hb4 hsmall).1
  have hle : W₀ ≤ ⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ := by
    rw [←moved_cover_idempotent (h := h)]
    exact (commutator_mono hd le_rfl).trans (derived_residual_commutator_le (h := h))
  refine ⟨hle,?_⟩
  have hc := card_le_of_le hle
  rcases moved_card h e hz hk with hcU | hcU <;> rw [hcU] at hc <;> omega

private theorem normalized_commutator {F : Type*} [Group F]
    {J A B : Subgroup F} (hA : J ≤ normalizer (A : Set F))
    (hB : J ≤ normalizer (B : Set F)) :
    J ≤ normalizer ((⁅A,B⁆ : Subgroup F) : Set F) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hg),mem_normalizer_iff_map_conj_eq.mp (hB hg)]

private theorem normalized_sup_card_le {F : Type*} [Group F]
    (A B : Subgroup F) [Finite A] [Finite B]
    (hn : B ≤ normalizer (A : Set F)) :
    Nat.card (A ⊔ B : Subgroup F) ≤ Nat.card A * Nat.card B := by
  have hprod : (A : Set F) * (B : Set F) = (A ⊔ B : Subgroup F) :=
    (coe_mul_of_right_le_normalizer_left _ _ hn).symm
  let f : A × B → (A ⊔ B : Subgroup F) :=
    fun x => ⟨x.1*x.2,mul_mem (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    have hx' : x ∈ (A : Set F) * (B : Set F) := hprod.symm ▸ hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx'
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

private theorem relative_derived_sup_card_le {F : Type*} [Group F]
    (J A B : Subgroup F) [Finite J]
    (hAJ : A ≤ J) (hBJ : B ≤ J)
    (hAn : J ≤ normalizer (A : Set F)) (hBn : J ≤ normalizer (B : Set F)) :
    Nat.card (⁅A ⊔ B,A ⊔ B⁆ : Subgroup F) ≤
      Nat.card (⁅A,A⁆ : Subgroup F) * Nat.card (⁅B,B⁆ : Subgroup F) *
        Nat.card (⁅A,B⁆ : Subgroup F) := by
  let D := ⁅A,A⁆
  let E := ⁅B,B⁆
  let X := ⁅A,B⁆
  let H := (D ⊔ E) ⊔ X
  have hDJ : D ≤ J := (Subgroup.commutator_le_sup _ _).trans (sup_le hAJ hAJ)
  have hEJ : E ≤ J := (Subgroup.commutator_le_sup _ _).trans (sup_le hBJ hBJ)
  have hXJ : X ≤ J := (Subgroup.commutator_le_sup _ _).trans (sup_le hAJ hBJ)
  have hDn : J ≤ normalizer (D : Set F) := normalized_commutator hAn hAn
  have hEn : J ≤ normalizer (E : Set F) := normalized_commutator hBn hBn
  have hXn : J ≤ normalizer (X : Set F) := normalized_commutator hAn hBn
  have hDEn : J ≤ normalizer ((D ⊔ E : Subgroup F) : Set F) :=
    (le_inf hDn hEn).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHn : J ≤ normalizer (H : Set F) :=
    (le_inf hDEn hXn).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hH : ⁅A ⊔ B,A ⊔ B⁆ ≤ H := by
    apply commutator_sup_le_of_relative_normal J A B (A ⊔ B) H hHn hAJ hBJ
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal J A B A H hHn hAJ hBJ
      · exact le_sup_left.trans le_sup_left
      · rw [commutator_comm]; exact le_sup_right
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal J A B B H hHn hAJ hBJ
      · exact le_sup_right
      · exact le_sup_right.trans le_sup_left
  have hHJ : H ≤ J := sup_le (sup_le hDJ hEJ) hXJ
  let : Finite D := Finite.of_injective (inclusion hDJ) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hEJ) (inclusion_injective _)
  let : Finite X := Finite.of_injective (inclusion hXJ) (inclusion_injective _)
  let : Finite (D ⊔ E : Subgroup F) := Finite.of_injective
    (inclusion (sup_le hDJ hEJ)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHJ) (inclusion_injective _)
  exact (card_le_of_le hH).trans
    ((normalized_sup_card_le (D ⊔ E) X (hXJ.trans hDEn)).trans
      (Nat.mul_le_mul_right _ (normalized_sup_card_le D E (hEJ.trans hDn))))

include h e hz hk in
/-- The opposite residual envelope contains the full moving cover in its
derived subgroup, bounded by the two actual residual commutators. -/
theorem plane_generating_midpoint_residual_envelope
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg))) :
    let c := p.walk.getVert 2
    let Y := localZSpan Rg c (alpha Rg) ⊓ Q Rg c
    let C := ⁅Q Rg c,Ltilde Rg c⁆
    U Rg c ≤ ⁅Y ⊔ C,Y ⊔ C⁆ ∧
      Nat.card (U Rg c) ≤ 2 * Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) *
        Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  let Y := P ⊓ Q Rg c
  let C := ⁅Q Rg c,Ltilde Rg c⁆
  let N := Y ⊔ C
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hta : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have htc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have ht : color Rg t = true := by
    have hn := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hn
    cases hh : color Rg t <;> simp_all
  have hQt : Q Rg c ≤ Q Rg t := Q_le_adjacent_h Rg ht hct
  have hLn : stabilizer Rg c ≤ normalizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨⟨g,hg⟩ * v * ⟨g,hg⟩⁻¹,?_,rfl⟩
    exact (inferInstance : (pResidual 2 (stabilizer Rg c)).Normal).conj_mem v hv ⟨g,hg⟩
  have hCn : stabilizer Rg c ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    normalized_commutator (Q_normalized Rg c) hLn
  have hCQ : C ≤ Q Rg c := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer _).trans (Q_normalized Rg c))
  have hYn : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (le_inf (hta.trans (localZSpan_normalized Rg _ _))
      (htc.trans (Q_normalized Rg c))).trans inf_normalizer_le_normalizer_inf
  have hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) hcol hct]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le inf_le_right hCQ) le_rfl).trans le_sup_right
    · exact (le_inf hYn (htc.trans hCn)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hd := plane_generating_midpoint_span_line h e hz hk u hR hb4 hsmall p hmid hback
  have hs := plane_generating_midpoint_reciprocal_slice h e hz hk u hR hb4 hsmall p hmid hback
  have hn := plane_generating_midpoint_span_nonabelian h e hz hk u hR hb4 hsmall p hmid hback
  have hidentity := small_selected_span_derived h e hz hk hb p (hsmall _ _ p) hs hn
  have hlineU : ⁅P,P⁆ ≤ U Rg c := by
    rw [hidentity.1]
    apply le_normalizer_iff_commutator_le_left.mp
    exact (inf_le_left.trans (Q_le_stabilizer_of_dist_two Rg _ _ rfl
      (p.dist_start (by omega)))).trans (U_normalized _)
  have hU : U Rg c ≤ ⁅N,N⁆ := moving_cover_le_normal_of_noncentral h e hz hk hcol
    ⁅P,P⁆ ⁅N,N⁆ hlineU (by rw [←hd.2.1]; exact commutator_mono le_sup_left le_sup_left)
    (normalized_commutator hNn hNn) hd.2.2.2.2
  have hNQ : N ≤ Q Rg c := sup_le inf_le_right hCQ
  let := finite_stabilizer Rg c
  let : Finite (⁅N,N⁆ : Subgroup (FreeAmalgam Rg)) := Finite.of_injective
    (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hNQ hNQ).trans (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1))))
    (inclusion_injective _)
  let := finite_stabilizer Rg t
  let : Finite (Q Rg t) := Finite.of_injective
    (inclusion (show Q Rg t ≤ stabilizer Rg t from fun _ hx => hx.1)) (inclusion_injective _)
  have hup := relative_derived_sup_card_le (Q Rg t) Y C
    (inf_le_right.trans hQt) (hCQ.trans hQt) hYn (htc.trans hCn)
  rw [hd.2.1,hd.2.2.1] at hup
  exact ⟨hU,(card_le_of_le hU).trans hup⟩

include h e hz hk in
private theorem plane_four_small_images_generating_path
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
        stabilizer Rg (p.walk.getVert 2) ∧
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (alpha Rg)) := by
  obtain ⟨z,p,hstrict⟩ := plane_exists_strict_forward_slice h e hz hk u hR hb4
  obtain ⟨a,b,q,hqa,hmid,hback,_⟩ :=
    plane_selected_backward_small_slice h e hz hk u hR hb4 hsmall p hstrict
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg q.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ q₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ b),
      ∀ i, q₀.walk.getVert i = act Rg g⁻¹ (q.walk.getVert i) :=
    ⟨q.act g⁻¹,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨q₀,hverts⟩ := hpact
  refine ⟨_,q₀,?_,?_⟩
  · rw [hverts 1,hverts 3,hverts 2,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hmid,hqa]
  · have hU := U_act Rg g⁻¹ a
    rw [hbase] at hU
    rw [hverts 2,hqa,Escape.PairingControl.FirstPairing.B_act
      (distance_gt_two h e hz hk) g⁻¹ _ rfl,hU,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hback

include h e hz hk in
/-- The actual selector produces a residual envelope containing the full
moving cover in its derived subgroup. Its two residual commutators cannot
both have order at most two. -/
theorem plane_four_small_images_selected_residual
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      let c := p.walk.getVert 2
      let Y := localZSpan Rg c (alpha Rg) ⊓ Q Rg c
      let C := ⁅Q Rg c,Ltilde Rg c⁆
      U Rg c ≤ ⁅Y ⊔ C,Y ⊔ C⁆ ∧
        Nat.card (U Rg c) ≤ 2 * Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) *
          Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg)) ∧
        (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨
          2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg))) := by
  obtain ⟨z,p,hmid,hback⟩ := plane_four_small_images_generating_path h e hz hk u hR hb4 hsmall
  have hd := plane_generating_midpoint_residual_envelope h e hz hk u hR hb4 hsmall p hmid hback
  refine ⟨z,p,hd.1,hd.2,?_⟩
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hcol : color Rg (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  have hlo : 16 ≤ Nat.card (U Rg (p.walk.getVert 2)) := by
    rcases graph_U_card h e hz hk _ hcol with hc | hc <;> omega
  by_contra! hh
  have hup := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hh.1) hh.2
  have hbound := hd.2
  omega

include h e hz hk in
/-- The entire intrinsic block core is nonabelian in the small-image
distance-four plane branch, via the literal ambient commutator identity. -/
theorem plane_four_small_images_block_nonabelian
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ¬ IsMulCommutative (blockU L) := by
  obtain ⟨z,p,hmid,hback⟩ := plane_four_small_images_generating_path h e hz hk u hR hb4 hsmall
  have hn := plane_generating_residual_derived_nontrivial h e hz hk u hR hb4 hsmall p hmid hback
  intro hab
  have hzB : ⁅blockU L,blockU L⁆ = ⊥ := commutator_self_eq_bot_iff.mpr hab
  have hzM := congrArg (Subgroup.map L.subtype) hzB
  rw [map_commutator,Subgroup.map_bot,←h.ambient_commutator_eq_blockU,←map_commutator] at hzM
  exact hn ((map_eq_bot_iff_of_injective _ (L ⊔ R).subtype_injective).mp hzM)


omit hk in
include h e hz in
/-- Whole-core application with the original intrinsic block, residual
movement and midpoint envelope, retaining the remaining cases. -/
theorem coreExhaustion_or_cubic_plane_residual_envelope :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          (¬ IsMulCommutative (blockU L)) ∧
          W₀ ≤ ⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ ∧
          16 ≤ Nat.card (⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ : Subgroup M) ∧
          ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            let c := p.walk.getVert 2
            let Y := localZSpan Rg c (alpha Rg) ⊓ Q Rg c
            let C := ⁅Q Rg c,Ltilde Rg c⁆
            U Rg c ≤ ⁅Y ⊔ C,Y ⊔ C⁆ ∧
              Nat.card (U Rg c) ≤ 2 * Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) *
                Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg)) ∧
              (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨
                2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall
    have hm := plane_four_small_images_residual_movement h e hz hk u hplane hb4 hsmall
    exact ⟨plane_four_small_images_block_nonabelian h e hz hk u hplane hb4 hsmall,
      hm.1,hm.2,plane_four_small_images_selected_residual h e hz hk u hplane hb4 hsmall⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the entire original intrinsic block.
The remaining residual upper bounds and terminal exclusion are not assumed. -/
theorem rankTwo_or_cubic_plane_residual_envelope :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          (¬ IsMulCommutative (blockU L)) ∧
          W₀ ≤ ⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ ∧
          16 ≤ Nat.card (⁅pCore 2 M,⁅pCore 2 M,K⁆⁆ : Subgroup M) ∧
          ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            let c := p.walk.getVert 2
            let Y := localZSpan Rg c (alpha Rg) ⊓ Q Rg c
            let C := ⁅Q Rg c,Ltilde Rg c⁆
            U Rg c ≤ ⁅Y ⊔ C,Y ⊔ C⁆ ∧
              Nat.card (U Rg c) ≤ 2 * Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) *
                Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg)) ∧
              (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨
                2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam Rg))))) :=
  (coreExhaustion_or_cubic_plane_residual_envelope h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
