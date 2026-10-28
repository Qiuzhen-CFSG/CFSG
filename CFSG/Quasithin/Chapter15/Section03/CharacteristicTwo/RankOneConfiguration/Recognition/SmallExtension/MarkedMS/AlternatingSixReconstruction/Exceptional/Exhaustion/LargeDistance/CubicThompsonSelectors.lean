module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPairedSelectors
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeOffenders
public import Theory.Representation.BinaryPermutationSixCover.Movement

/-!
# Source Thompson choices on the original cubic graph

The source join J_alpha(T_beta) uses maximum-order small movers, rather
than maximum elementary abelian subgroups. In the full point-core branch
it is the whole edge kernel. Indeed, the three mixed-plane preimages inside
R have order 4|Q| and fixed index four on either permitted moving cover;
every small mover has order at most 4|Q|. The planes generate R. The literal
intersection ker(projection) ∩ R = Q is used throughout: the projection
kernel itself remains E, with nontrivial odd quotient E/Q.

Injective edge charts transport this calculation to the original graph.
The retained paired backward paths therefore satisfy both source Thompson
centralizer bounds and both residual inclusions with the same switch,
critical pair and nonzero shifted kernel line. The order-two critical
image also excludes the exceptional two-transvection marking, so the
marked opposite seed is the full X = Z already proved on this branch.

The whole-core and literal C.1.32 applications discharge these local
Thompson premises. The forward selector and the terminal comparison in
(5.12)(1), the point contradiction, the remaining image branches, natural
exhaustion and both unconditional reconstruction outcomes remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), Section 5.0 and (5.4)--(5.6), pp.912,915--919, and (5.12)(1),
pp.924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

private theorem core_plane_codim (u : S) (i : Fin 3) :
    fixedCodim (coreRepresentation (Fin 6)) (SmallImages.plane u i) = 2 := by
  rw [SmallImages.plane, fixedCodim_map_conj,
    ←CFSG.Quasithin.ChapterC.NaturalSixControl.Model.corePlane_conjugate,
    fixedCodim_map_conj]
  exact fixedCodim_plus.2.2.1

private theorem maximal_small_movers_generate
    {H : Type*} [Group H] [Finite H] (T Q₀ W : Subgroup H) (f : H →* S)
    (hQ : f.ker ⊓ T = Q₀) (u : S)
    (hT : T.map f = pointCore.map (MulAut.conj u).toMonoidHom)
    (hbounds : ∀ A ≤ T,
      2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map f) ≤
        (centralizer (A : Set H)).relIndex W ∧
      (centralizer (A : Set H)).relIndex W ≤
        2 ^ fixedCodim (coreRepresentation (Fin 6)) (A.map f)) :
    let small := fun A : Subgroup H => A ≤ T ∧
      (centralizer (A : Set H)).relIndex W ≤ Q₀.relIndex A ∧
      (centralizer (A : Set H)).relIndex W ≤ 4
    sSup {A | small A ∧ ∀ B, small B → Nat.card B ≤ Nat.card A} = T := by
  let small := fun A : Subgroup H => A ≤ T ∧
    (centralizer (A : Set H)).relIndex W ≤ Q₀.relIndex A ∧
    (centralizer (A : Set H)).relIndex W ≤ 4
  let F := fun i : Fin 3 => T ⊓ (SmallImages.plane u i).comap f
  have hTE : T.map f = CFSG.Quasithin.ChapterC.NaturalSixControl.Model.E.map
      (MulAut.conj u).toMonoidHom := hT.trans
    (congrArg (fun P : Subgroup S => P.map (MulAut.conj u).toMonoidHom)
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional)
  have hkA (A : Subgroup H) (hAT : A ≤ T) : f.ker ⊓ A = Q₀ ⊓ A := by
    rw [←hQ,inf_assoc,inf_eq_right.mpr hAT]
  have hindex (A : Subgroup H) (hAT : A ≤ T) : Q₀.relIndex A = Nat.card (A.map f) := by
    rw [←relIndex_ker,←inf_relIndex_right Q₀ A,←hkA A hAT,inf_relIndex_right]
  have hcard (A : Subgroup H) (hAT : A ≤ T) :
      Nat.card A = Nat.card (Q₀ ⊓ A : Subgroup H) * Nat.card (A.map f) := by
    rw [←hindex A hAT]
    simpa only [relIndex_bot_left,inf_relIndex_right] using
      (relIndex_mul_relIndex (⊥ : Subgroup H) (Q₀ ⊓ A) A bot_le inf_le_right).symm
  have hFmap (i : Fin 3) : (F i).map f = SmallImages.plane u i := by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := (SmallImages.plane_le u i).trans hTE.ge hy
      exact mem_map_of_mem f ⟨hx,hy⟩
  have hQF (i : Fin 3) : Q₀ ≤ F i := by
    rw [←hQ]
    exact le_inf inf_le_right (inf_le_left.trans (ker_le_comap _ _))
  have hFcard (i : Fin 3) : Nat.card (F i) = Nat.card Q₀ * 4 := by
    rw [hcard (F i) inf_le_left,inf_eq_left.mpr (hQF i),hFmap,
      SmallImages.plane_card_conjugate]
  have hFsmall (i : Fin 3) : small (F i) := by
    have hi := (hbounds (F i) inf_le_left).2
    rw [hFmap,core_plane_codim] at hi
    refine ⟨inf_le_left,?_,hi⟩
    rw [hindex (F i) inf_le_left,hFmap,SmallImages.plane_card_conjugate]
    exact hi
  have hbound (A : Subgroup H) (hA : small A) : Nat.card A ≤ Nat.card Q₀ * 4 := by
    have hb := (hbounds A hA.1).1
    have hnatural : 2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map f) ≤
        Nat.card (A.map f) ∧
        2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map f) ≤ 4 :=
      ⟨(hb.trans hA.2.1).trans_eq (hindex A hA.1), hb.trans hA.2.2⟩
    have hc : Nat.card (A.map f) ≤ 4 := by
      rcases (SmallImages.admissible_iff_conjugate u
        ((map_mono hA.1).trans_eq hTE)).mp hnatural with he | he | ⟨i,he⟩
      · rw [he,card_bot]; omega
      · rw [he,card_map_of_injective (MulAut.conj u).injective,card_last]; omega
      · rw [he,SmallImages.plane_card_conjugate]
    rw [hcard A hA.1]
    exact Nat.mul_le_mul (card_le_of_le inf_le_left) hc
  have hFmax (i : Fin 3) : F i ≤ sSup {A | small A ∧ ∀ B, small B → Nat.card B ≤ Nat.card A} := by
    apply le_sSup
    refine ⟨hFsmall i,fun B hB => ?_⟩
    rw [hFcard]
    exact hbound B hB
  have hjoin : F 0 ⊔ F 1 = T := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro y hy
    have he : (F 0 ⊔ F 1).map f = T.map f := by
      rw [Subgroup.map_sup,hFmap,hFmap,SmallImages.planes_generate,hTE]
    have hpre := congrArg (Subgroup.comap f) he
    rw [comap_map_eq,comap_map_eq] at hpre
    have hy' : y ∈ (F 0 ⊔ F 1) ⊔ f.ker := hpre.symm ▸ mem_sup_left hy
    obtain ⟨b,hb,k,hk,hbk⟩ := mem_sup_of_normal_right.mp hy'
    have hkT : k ∈ T := by
      have hbT : b ∈ T := (show F 0 ⊔ F 1 ≤ T from sup_le inf_le_left inf_le_left) hb
      have hkval : k = b⁻¹*y := by rw [←hbk]; group
      rw [hkval]
      exact T.mul_mem (T.inv_mem hbT) hy
    have hkQ : k ∈ Q₀ := hQ ▸ ⟨hk,hkT⟩
    rw [←hbk]
    exact mul_mem hb (mem_sup_left (hQF 0 hkQ))
  apply le_antisymm (sSup_le fun A hA => hA.1.1)
  exact hjoin.ge.trans (sup_le (hFmax 0) (hFmax 1))

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem cubic_cover_movement_bounds (A : Subgroup M) :
    2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤
      (centralizer (A : Set M)).relIndex W ∧
    (centralizer (A : Set M)).relIndex W ≤
      2 ^ fixedCodim (coreRepresentation (Fin 6)) (A.map π) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
  have hb := (moved_subgroup_cover_model h e hz hk).fixedCodim_bounds (A.map π)
  rw [map_id] at hb
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
  exact ⟨Nat.pow_le_pow_right (by decide) hb.1,Nat.pow_le_pow_right (by decide) hb.2⟩

include h e hz hk in
private theorem cubic_radical_projection_kernel : (π).ker ⊓ Rg = pCore 2 M := by
  rw [CubicAction.projection_kernel h e hz hk]
  apply le_antisymm
  · exact two_subgroup_le_core_of_le_extensionKernel h hz _
      (h.relative_radical.isPGroup.of_injective (inclusion inf_le_right) (inclusion_injective _)) inf_le_left
  · exact le_inf le_sup_right
      h.relative_radical.twoCore_le


include h e hz hk in
/-- The source maximum-order small movers generate every full point edge.
The two-core is only the intersection of the cubic kernel with that edge. -/
theorem point_edgeOffenderJoin_eq (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    edgeOffenderJoin c t = Q Rg t := by
  have hmax := maximal_small_movers_generate Rg (pCore 2 M) W π
    (cubic_radical_projection_kernel h e hz hk) u
    (full_point_image_of_contained h e hz hk u hR)
    (fun A _ => cubic_cover_movement_bounds h e hz hk A)
  obtain ⟨i,hi,hiR,hiQ,hiW⟩ :
      ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
        (Rg).map i = Q Rg t ∧ (pCore 2 M).map i = Q Rg c ∧
        (W).map i = U Rg c := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_⟩
      · have h := Q_act Rg g (beta Rg)
        rw [Q_beta] at h
        simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
      · have hh := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
        simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
      · have hh := U_act Rg g (alpha Rg)
        rw [←graph_U_map h e hz] at hh
        simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
    · rw [hg.1] at hc
      cases hc
  let small := fun A : Subgroup M => A ≤ Rg ∧
    (centralizer (A : Set M)).relIndex W ≤ (pCore 2 M).relIndex A ∧
    (centralizer (A : Set M)).relIndex W ≤ 4
  have hsmall (A : Subgroup M) : edgeSmallMover c t (A.map i) ↔ small A := by
    unfold edgeSmallMover
    rw [←hiR,←hiQ,←hiW,map_le_map_iff_of_injective hi,
      relIndex_map_map_of_injective _ _ hi]
    have hind : (centralizer (A.map i : Set (FreeAmalgam Rg))).relIndex ((W).map i) =
        (centralizer (A : Set M)).relIndex W := by
      rw [←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
        relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]
    rw [hind]
  have hmaxmap (A : Subgroup M)
      (hA : small A ∧ ∀ B, small B → Nat.card B ≤ Nat.card A) :
      A.map i ∈ edgeMaximalOffenders c t := by
    refine ⟨(hsmall A).mpr hA.1,?_⟩
    intro B hB
    have hBr : B ≤ i.range := hB.1.trans (hiR ▸ map_le_range i Rg)
    have hBm : (B.comap i).map i = B := map_comap_eq_self hBr
    have hBs : small (B.comap i) := (hsmall _).mp (hBm.symm ▸ hB)
    have hb := hA.2 (B.comap i) hBs
    rw [←hBm,card_map_of_injective hi,card_map_of_injective hi]
    exact hb
  apply le_antisymm (sSup_le fun A hA => hA.1.1)
  have hm := congrArg (Subgroup.map i) hmax
  rw [hiR] at hm
  rw [←hm,sSup_eq_iSup,Subgroup.map_iSup]
  apply iSup_le
  intro A
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro hA
  exact le_sSup (hmaxmap A hA)

include h e hz hk in
/-- For any chosen generating edge, the forward edge seed has no extra
fixed vectors under the literal source Thompson join. -/
theorem point_selected_thompson_centralizer (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    {t : Vertex Rg} (hat : Adjacent Rg (alpha Rg) t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg)) :
    Z Rg (p.walk.getVert 1) ⊓
      centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  rw [point_edgeOffenderJoin_eq h e hz hk u hR rfl hat]
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hvcol : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hav
    change false ≠ _ at hh
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hzv : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [(sourceGeometry h).distance_constant z p.end_color]
    change (cosetGraph Rg).dist z (p.walk.getVert 1) < sourceDistance h
    have hd := p.dist_end 1
    rw [SimpleGraph.dist_comm,hd]
    have hlen : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hZv : Z Rg (p.walk.getVert 1) ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    have hx' : x ∈ omegaCenter (Q Rg (p.walk.getVert 1)) := by
      simpa only [Z,hvcol,Bool.true_eq_false,ite_false,edgeOmega] using hx
    exact (mem_omegaCenter_iff.mp hx').2.2 y (hzv hy)
  intro x hx
  have hxT := hx.2
  have hxZ := hZv hx.1
  apply le_centralizer_iff.mp ?_ (show x ∈ zpowers x from mem_zpowers _)
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hxT))
    (le_centralizer_iff.mp (zpowers_le.mpr hxZ))


private theorem relIndex_sup_of_normalized {H : Type*} [Group H]
    (B A : Subgroup H) (hn : A ≤ normalizer (B : Set H)) :
    B.relIndex (B ⊔ A) = B.relIndex A := by
  let J := B ⊔ A
  let : (B.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hi := relIndex_sup_left (A.subgroupOf J) (B.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

include h e hz hk in
/-- The source's exceptional two-transvection definition of the marked seed
cannot occur on this same critical pair; its full omega actor is the seed. -/
theorem point_critical_marked_actor (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ Source.SplitCriticalImage a z ∧ X Rg z = Z Rg z := by
  refine ⟨?_,point_omega_eq_seed h e hz hk u hR z p.end_color⟩
  rintro ⟨A,B,hQA,hQB,hgen,hne,hAi,hBi,hAf,hBf⟩
  let T := Q Rg z ⊔ Z Rg a
  have hZT : Z Rg a ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
      (by rw [(sourceGeometry h).distance_constant z p.end_color];
          exact sourceDistance_pos h)
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) z p.end_color p.critical)
  have hidx : (Q Rg z).relIndex T = 2 := by
    rw [relIndex_sup_of_normalized _ _ (hZT.trans (Q_normalized Rg z))]
    exact (point_image_critical_indices_two h e hz hk u hR p).1
  have hAT : A ≤ T := le_sup_left.trans hgen.le
  have hBT : B ≤ T := le_sup_right.trans hgen.le
  have heq (C : Subgroup (FreeAmalgam Rg)) (hQC : Q Rg z ≤ C)
      (hCT : C ≤ T) (hi : (Q Rg z).relIndex C = 2) : C = T := by
    have hh := relIndex_mul_relIndex (Q Rg z) C T hQC hCT
    rw [hi,hidx] at hh
    have hc : C.relIndex T = 1 := by omega
    exact le_antisymm hCT (relIndex_eq_one.mp hc)
  exact hne ((heq A hQA hAT hAi).trans (heq B hQB hBT hBi).symm)

include h e hz hk in
/-- The same paired backward paths satisfy both Thompson centralizer bounds
and both residual inclusions of MS93 (5.5), with the literal source actor. -/
theorem point_paired_thompson_paths
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
      let x := (embedM Rg r)⁻¹
      let c := p.walk.getVert 2
      let d := act Rg g c
      let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
      ∃ q : CriticalPath Rg (sourceGeometry h) d c,
      ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
        act Rg g (p.walk.getVert 1) = t ∧
        q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
        q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
          centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
            Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ Ltilde Rg (alpha Rg) ∧
        x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
        ((Z Rg z).comap (embedM Rg)).map π ≤ centralizer ({π r} : Set S) ∧
        (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
        (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
        ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
        ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
        Nat.card H = 2 ∧
        H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        (¬ Source.SplitCriticalImage (alpha Rg) z ∧ X Rg z = Z Rg z) ∧
        edgeOffenderJoin (alpha Rg) t = Q Rg t ∧
        edgeOffenderJoin d t = Q Rg t ∧
        edgeOffenderJoin (alpha Rg) (act Rg x t) = Q Rg (act Rg x t) ∧
        edgeOffenderJoin (act Rg x d) (act Rg x t) = Q Rg (act Rg x t) ∧
        (Z Rg (p.walk.getVert 1) ⊓
          centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
        (Z Rg (p.walk.getVert 1) ⊓
          centralizer (edgeOffenderJoin (alpha Rg) (act Rg x t) : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
        Ltilde Rg (alpha Rg) ≤
          (edgeOffenderJoin d t ⊔ Z Rg z) ⊓
            (edgeOffenderJoin (act Rg x d) (act Rg x t) ⊔ Z Rg z) := by
  obtain ⟨t,r,hr,g,hg,q,q',hgt,hqt,hqt',hqa,hqa',hgen,hgen',hpair,hfixed,
    hxL,hxC,hxN,hactor,hdi,hdi',hline,hline',hcard,hcentral⟩ :=
    point_paired_backward_paths h e hz hk u hR p hlarge
  let x := (embedM Rg r)⁻¹
  let c := p.walk.getVert 2
  let d := act Rg g c
  have hql : q.walk.length = 4 := q.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  have hql' : q'.walk.length = 4 := q'.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  have hdt : Adjacent Rg d t := by
    have hh := (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 0) (by omega))
    simpa only [SimpleGraph.Walk.getVert_zero,hqt] using hh
  have hat : Adjacent Rg (alpha Rg) t := by
    have hh := (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega))
    rw [hqt,hqa] at hh
    exact adjacent_symm Rg hh
  have hdt' : Adjacent Rg (act Rg x d) (act Rg x t) := by
    have hh := (cosetGraph_adj Rg _ _).mp (q'.walk.adj_getVert_succ (i := 0) (by omega))
    simpa only [SimpleGraph.Walk.getVert_zero,hqt'] using hh
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    have hh := (cosetGraph_adj Rg _ _).mp (q'.walk.adj_getVert_succ (i := 1) (by omega))
    rw [hqt',hqa'] at hh
    exact adjacent_symm Rg hh
  have hj := point_edgeOffenderJoin_eq h e hz hk u hR rfl hat
  have hjd := point_edgeOffenderJoin_eq h e hz hk u hR q.start_color hdt
  have hj' := point_edgeOffenderJoin_eq h e hz hk u hR rfl hat'
  have hjd' := point_edgeOffenderJoin_eq h e hz hk u hR q'.start_color hdt'
  refine ⟨t,r,hr,g,hg,q,q',hgt,hqt,hqt',hqa,hqa',hgen,hgen',hpair,hfixed,
    hxL,hxC,hxN,hactor,hdi,hdi',hline,hline',hcard,hcentral,
    point_critical_marked_actor h e hz hk u hR p,hj,hjd,hj',hjd',
    point_selected_thompson_centralizer h e hz hk u hR p hat hgen,
    point_selected_thompson_centralizer h e hz hk u hR p hat' hgen',?_⟩
  rw [hjd,hjd',hgen,hgen',inf_idem]
  exact Ltilde_le_stabilizer _

omit hk in
include h e hz in
/-- The whole-core application uses the original selected forward path and
constructs the same-choice Thompson and marked-actor clauses. -/
theorem coreExhaustion_or_cubic_thompson_selectors :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
              ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
                let x := (embedM Rg r)⁻¹
                let c := p.walk.getVert 2
                let d := act Rg g c
                let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
                ∃ q : CriticalPath Rg (sourceGeometry h) d c,
                ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
                  act Rg g (p.walk.getVert 1) = t ∧
                  q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
                  q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
                  Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
                  (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
                    centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
                      Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  x ∈ Ltilde Rg (alpha Rg) ∧
                  x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  ((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤ centralizer ({(CubicAction.projection h e hz hk) r} : Set S) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
                  ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  Nat.card H = 2 ∧
                  H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  (¬ Source.SplitCriticalImage (alpha Rg) z ∧ X Rg z = Z Rg z) ∧
                  edgeOffenderJoin (alpha Rg) t = Q Rg t ∧
                  edgeOffenderJoin d t = Q Rg t ∧
                  edgeOffenderJoin (alpha Rg) (act Rg x t) = Q Rg (act Rg x t) ∧
                  edgeOffenderJoin (act Rg x d) (act Rg x t) = Q Rg (act Rg x t) ∧
                  (Z Rg (p.walk.getVert 1) ⊓
                    centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
                      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
                  (Z Rg (p.walk.getVert 1) ⊓
                    centralizer (edgeOffenderJoin (alpha Rg) (act Rg x t) : Set (FreeAmalgam Rg)) ≤
                      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
                  Ltilde Rg (alpha Rg) ≤
                    (edgeOffenderJoin d t ⊔ Z Rg z) ⊓
                      (edgeOffenderJoin (act Rg x d) (act Rg x t) ⊔ Z Rg z))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_shifted_full_omega h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hex
  · rcases hpoint with ⟨hpoint,hb4,hsize,z,p,hstrict,hrest⟩
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hsize,z,p,hstrict,
      point_paired_thompson_paths h e hz hk u hpoint.le p hstrict⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the simultaneous Thompson selections.
The plane and Sylow alternatives, both covers and the cubic kernel remain. -/
theorem rankTwo_or_cubic_thompson_selectors :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
              ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
                let x := (embedM Rg r)⁻¹
                let c := p.walk.getVert 2
                let d := act Rg g c
                let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
                ∃ q : CriticalPath Rg (sourceGeometry h) d c,
                ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
                  act Rg g (p.walk.getVert 1) = t ∧
                  q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
                  q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
                  Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
                  (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
                    centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
                      Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  x ∈ Ltilde Rg (alpha Rg) ∧
                  x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  ((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤ centralizer ({(CubicAction.projection h e hz hk) r} : Set S) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
                  ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  Nat.card H = 2 ∧
                  H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  (¬ Source.SplitCriticalImage (alpha Rg) z ∧ X Rg z = Z Rg z) ∧
                  edgeOffenderJoin (alpha Rg) t = Q Rg t ∧
                  edgeOffenderJoin d t = Q Rg t ∧
                  edgeOffenderJoin (alpha Rg) (act Rg x t) = Q Rg (act Rg x t) ∧
                  edgeOffenderJoin (act Rg x d) (act Rg x t) = Q Rg (act Rg x t) ∧
                  (Z Rg (p.walk.getVert 1) ⊓
                    centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
                      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
                  (Z Rg (p.walk.getVert 1) ⊓
                    centralizer (edgeOffenderJoin (alpha Rg) (act Rg x t) : Set (FreeAmalgam Rg)) ≤
                      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
                  Ltilde Rg (alpha Rg) ≤
                    (edgeOffenderJoin d t ⊔ Z Rg z) ⊓
                      (edgeOffenderJoin (act Rg x d) (act Rg x t) ⊔ Z Rg z))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_thompson_selectors h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
