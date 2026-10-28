module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedNatural
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement

/-!
# The central attachment forced by a failed shifted plane comparison

Keep the actual critical paths a--c--z and d--a--c, a strict forward
Baumann slice, and the two backward/forward edge cores generating G_a.
A failed shifted comparison gives a radius line H central in G_a. Its
alignment with the critical line T = [Z_a,Z_z] modulo Z(G_z) restricts
to the actual moving cover U_z. The order-sixteen comparison already
excludes that cover, so C = U_z intersect Z(G_z) has order two.
Since T is noncentral in G_a, H and T are distinct, and their four-group
is exactly H C. In particular C lies in the original first-edge seed.

The central factor H disappears from every commutator with a subgroup
of G_a. Thus [C,A] = [T,A] for every such A, and C is noncentral in G_a.
The opposite generating edge moves C into its own seed by a subgroup
of order at least four; that seed is disjoint from C and its core does
not normalize C. This describes the full central attachment, without
replacing a literal line by its image in the natural quotient.

The paired selector transports this conclusion on its same paths and
retains both generation equations. Whole-core and literal C.1.32
applications use the original cubic projection with kernel E and its
possibly nontrivial odd quotient E/Q. The original radical has no Sylow
assumption. The order-32 contradiction, remaining image/distance/Borel
branches, both core exhaustions and unconditional reconstruction remain.

Internal imports reuse the earlier elementary line and central-factor
calculations without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the line alignment and central comparisons in (5.12)(1),
printed pp.924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem central_join_restrict {J : Type*} [Group J]
    (A B U C : Subgroup J) (hA : A ≤ U) (hB : B ≤ U)
    (hC : C ≤ centralizer (U : Set J)) (he : A ⊔ C = B ⊔ C) :
    A ⊔ (U ⊓ C) = B ⊔ (U ⊓ C) := by
  have step (A B : Subgroup J) (hA : A ≤ U) (hB : B ≤ U)
      (he : A ⊔ C ≤ B ⊔ C) : A ≤ B ⊔ (U ⊓ C) := by
    intro x hx
    have hxc : x ∈ (B : Set J) * (C : Set J) := by
      rw [←coe_mul_of_right_le_normalizer_left B C
        ((hC.trans (centralizer_le hB)).trans (Subgroup.centralizer_le_normalizer _))]
      exact he (mem_sup_left hx)
    obtain ⟨b,hb,c,hc,rfl⟩ := hxc
    have hcU : c ∈ U := by
      have hh := U.mul_mem (U.inv_mem (hB hb)) (hA hx)
      simpa only [inv_mul_cancel_left] using hh
    exact (B ⊔ (U ⊓ C)).mul_mem (mem_sup_left hb) (mem_sup_right ⟨hcU,hc⟩)
  exact le_antisymm (sup_le (step A B hA hB he.le) le_sup_right)
    (sup_le (step B A hB hA he.ge) le_sup_right)

include h e hz hk in
/-- A strict-forward shifted failure forces the endpoint attachment to be
a noncentral first-edge line with the critical line's full starting action. -/
theorem plane_shifted_failure_attachment
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hfail : ¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
    let T := ⁅Z Rg a,Z Rg z⁆
    let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    Nat.card (U Rg z) = 32 ∧ Nat.card C = 2 ∧
      H ⊔ T = H ⊔ C ∧ Nat.card (H ⊔ T : Subgroup (FreeAmalgam Rg)) = 4 ∧
      C ≤ Z Rg (p.walk.getVert 1) ∧
      C ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ ∧
      (∀ A : Subgroup (FreeAmalgam Rg), A ≤ stabilizer Rg a → ⁅C,A⁆ = ⁅T,A⁆) ∧
      4 ≤ Nat.card (⁅C,Q Rg (q.walk.getVert 1)⁆ : Subgroup (FreeAmalgam Rg)) ∧
      ⁅C,Q Rg (q.walk.getVert 1)⁆ ≤ Z Rg (q.walk.getVert 1) ∧
      C ⊓ Z Rg (q.walk.getVert 1) = ⊥ ∧
      ¬ Q Rg (q.walk.getVert 1) ≤ normalizer (C : Set (FreeAmalgam Rg)) := by
  let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  let T := ⁅Z Rg a,Z Rg z⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let Cz := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hn : Nat.card (U Rg z) = 32 := by
    rcases graph_U_card h e hz hk z p.end_color with hn | hn
    · exact (hfail (plane_shifted_comparison_of_sixteen_strict_forward h e hz hk u hR
        hb4 hsmall p q hqa hescape K hK hgen hs hn)).elim
    · exact hn
  have hCcard : Nat.card C = 2 := by
    let A := centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    have hi := (A.subgroupOf (U Rg z)).index_mul_card
    change A.relIndex (U Rg z) * Nat.card (A.subgroupOf (U Rg z)) = Nat.card (U Rg z) at hi
    rw [moving_whole_fixed_index h e hz hk p.end_color,hn] at hi
    have hc : Nat.card (A.subgroupOf (U Rg z)) = Nat.card C := by
      change Nat.card (A.subgroupOf (U Rg z)) = Nat.card (U Rg z ⊓ A : Subgroup (FreeAmalgam Rg))
      rw [←card_map_of_injective (U Rg z).subtype_injective]
      congr 1
      rw [subgroupOf,map_comap_eq,range_subtype,inf_comm]
    rw [hc] at hi
    omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hb := distance_gt_two h e hz hk
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hct
    rw [q.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : V Rg a ⊓ Q Rg (p.walk.getVert 2) ≤
      Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2) := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb
  have hal := plane_radius_kernel_alignment h e hz hk u hR p (hsmall _ _ p)
    _ inf_le_left hYt hAY hescape
  have hHC := plane_shifted_failure_central_of_strict_forward h e hz hk u hR
    hb4 hsmall p q hqa hescape K hK hfail hgen hs
  have hHZ : H ≤ Z Rg a := hal.2.2.1
  have hHU : H ≤ U Rg z :=
    (plane_shifted_kernel_failure_reciprocal h e hz hk u hR hb4 hsmall p q hqa
      hescape K hK hfail).2.2.2.2.1.trans inf_le_right
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hTU : T ≤ U Rg z := by
    change ⁅Z Rg a,Z Rg z⁆ ≤ _
    rw [commutator_comm,←small_critical_moving_commutator_eq h e hz hk pr (hsmall _ _ pr)]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) z pr.start_color
        (by rw [(sourceGeometry h).distance_constant _ pr.start_color]; exact sourceDistance_pos h)
        pr.critical).trans (U_normalized z))
  have hTZ : T ≤ Z Rg a := by
    exact critical_seed_commutator_le h p
  have hU : U Rg z ≤ stabilizer Rg z := (DistanceEight.U_le_Z Rg z).trans (Z_le_stabilizer Rg z)
  have halign : H ⊔ C = T ⊔ C := by
    have hh := central_join_restrict H T (U Rg z) Cz hHU hTU
      (inf_le_right.trans (centralizer_le hU)) hal.2.2.2.2.2
    have he : U Rg z ⊓ Cz = C := by
      dsimp only [Cz,C]
      rw [←inf_assoc,inf_eq_left.mpr hU]
    rwa [he] at hh
  have hTnot := critical_commutator_not_central h e hz hk p
  have hne : H ≠ T := fun he => hTnot (he.ge.trans hHC)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : Finite C := Nat.finite_of_card_ne_zero (by omega)
  have hCNorm : H ≤ normalizer (C : Set (FreeAmalgam Rg)) := by
    apply (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (hHU.trans hU)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCHT : C ≤ H ⊔ T := by
    have hh := two_line_exchange T C H hCcard
      (by rw [sup_comm C,halign]; exact le_sup_left) hCNorm
      (fun he => hTnot (he.trans hHC))
    rwa [sup_comm T H] at hh
  have hjoins : H ⊔ T = H ⊔ C :=
    le_antisymm (sup_le le_sup_left (halign ▸ le_sup_left)) (sup_le le_sup_left hCHT)
  have hfour : Nat.card (H ⊔ T : Subgroup (FreeAmalgam Rg)) = 4 :=
    distinct_two_lines_card (Z Rg a) H T hHZ hTZ hal.1
      (small_critical_commutator_card h e hz hk p (hsmall _ _ p)) hne
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have has : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [hqa] using hh
  have hZz : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    change 4 - 1 < sourceDistance h
    rw [hb4]
    decide
  have hTv : T ≤ Z Rg (p.walk.getVert 1) :=
    (commutator_mono le_rfl hZz).trans (plane_edge_seed_commutator h e hz hk u hR p.start_color hav)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) := by
    rw [←(plane_edge_full_seed_fixer h e hz hk u hR p.start_color hav).1]
    exact le_inf hHZ (hHC.trans (centralizer_le
      (show Q Rg (p.walk.getVert 1) ≤ stabilizer Rg a from le_sup_right.trans_eq hgen)))
  have hCv : C ≤ Z Rg (p.walk.getVert 1) := hCHT.trans (sup_le hHv hTv)
  have hCa : C ≤ Z Rg a := hCv.trans (adjacent_Z_le Rg p.start_color hav)
  have hCnot : ¬ C ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    fun hc => hTnot ((show T ≤ H ⊔ C from halign ▸ le_sup_left).trans (sup_le hHC hc))
  have hCdis : C ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ := by
    let : Finite (C ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
        Subgroup (FreeAmalgam Rg)) :=
      Finite.of_injective (inclusion (show C ⊓ _ ≤ C from inf_le_left)) (inclusion_injective _)
    by_contra hh
    have hlo := (one_lt_card_iff_ne_bot _).mpr hh
    have he := eq_of_le_of_card_ge (show C ⊓ centralizer
      (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤ C from inf_le_left) (by omega)
    exact hCnot (he ▸ inf_le_right)
  have hmove (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg a) : ⁅C,A⁆ = ⁅T,A⁆ := by
    have hCH : H ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
      (hHC.trans (centralizer_le (hCa.trans (Z_le_stabilizer Rg a)))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hTH : H ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
      (hHC.trans (centralizer_le (hTZ.trans (Z_le_stabilizer Rg a)))).trans
        (Subgroup.centralizer_le_normalizer _)
    calc
      ⁅C,A⁆ = ⁅C ⊔ H,A⁆ := (commutator_sup_of_central_attachment C H A hCH
        (hHC.trans (centralizer_le hA))).symm
      _ = ⁅T ⊔ H,A⁆ := by rw [sup_comm C H,←hjoins,sup_comm H T]
      _ = ⁅T,A⁆ := commutator_sup_of_central_attachment T H A hTH
        (hHC.trans (centralizer_le hA))
  have hgrowth := plane_generating_edge_line_growth h e hz hk u hR p.start_color
    hav has ((sup_comm _ _).trans hgen) C hCv hCcard hCdis
  exact ⟨hn,hCcard,hjoins,hfour,hCv,hCdis,hmove,hgrowth.2.2.1,
    hgrowth.2.2.2.1,hgrowth.2.2.2.2.1,hgrowth.2.2.2.2.2.2⟩


include h e hz hk in
/-- The original paired selector retains both generation equations and the
same paths. On its chosen backward branch, every failed comparison forces
the actual endpoint attachment and its backward-edge movement. -/
theorem plane_selected_strict_forward_attachment
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hescape : ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g (p.walk.getVert 2)
          let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
            ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
              ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (v.walk.getVert 2) →
                (¬ ⁅K,Z Rg w⁆ ≤ ⁅K,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg w⁆) →
                let H := ⁅V Rg (alpha Rg) ⊓ Q Rg (v.walk.getVert 2),Z Rg w ⊓ Q Rg (alpha Rg)⁆
                let T := ⁅Z Rg (alpha Rg),Z Rg w⁆
                let C := U Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))
                Nat.card (U Rg w) = 32 ∧ Nat.card C = 2 ∧
                  H ⊔ T = H ⊔ C ∧ Nat.card (H ⊔ T : Subgroup (FreeAmalgam Rg)) = 4 ∧
                  C ≤ Z Rg (v.walk.getVert 1) ∧
                  C ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) = ⊥ ∧
                  (∀ A : Subgroup (FreeAmalgam Rg), A ≤ stabilizer Rg (alpha Rg) → ⁅C,A⁆ = ⁅T,A⁆) ∧
                  4 ≤ Nat.card (⁅C,Q Rg (q.walk.getVert 1)⁆ : Subgroup (FreeAmalgam Rg)) ∧
                  ⁅C,Q Rg (q.walk.getVert 1)⁆ ≤ Z Rg (q.walk.getVert 1) ∧
                  C ⊓ Z Rg (q.walk.getVert 1) = ⊥ ∧
                  ¬ Q Rg (q.walk.getVert 1) ≤ normalizer (C : Set (FreeAmalgam Rg))
          comparison z p ∨ comparison (act Rg x z) p' := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hc1 hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl ha1] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg ha1))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hs' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p'.walk.getVert 2)) := by
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb
        (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [hverts 2]
    change 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x (p.walk.getVert 2)))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hs
  have hescape' : ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p'.walk.getVert 2),Z Rg (act Rg x z)⁆ ≤
      Z Rg (alpha Rg) := by
    intro he
    apply hescape
    apply (map_le_map_iff_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (MulAut.conj x⁻¹).injective).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      ←V_act,←Q_act,←Z_act,←Z_act,show act Rg x (alpha Rg) = alpha Rg from hx,←hverts 2]
    exact he
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    refine Or.inl ⟨q',hq1',hqv',?_⟩
    intro K hK hfail
    apply plane_shifted_failure_attachment h e hz hk u hR hb4 hsmall
      p q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape K hK hfail
    · rw [hq1']
      exact hfirst
    · exact hs
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    refine Or.inr ⟨q',hq1',hqv',?_⟩
    intro K hK hfail
    apply plane_shifted_failure_attachment h e hz hk u hR hb4 hsmall
      p' q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape' K hK hfail
    · rw [hq1',hQfirst]
      exact hfirst
    · exact hs'

omit hk in
include h e hz in
/-- Whole-core application of the attachment and movement forced by a
failed shifted comparison on the original cubic graph. -/
theorem coreExhaustion_or_cubic_shifted_attachment :
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
          ∀ a z d (p : CriticalPath Rg (sourceGeometry h) a z)
            (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
            q.walk.getVert 2 = a →
            (¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) →
            ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
              Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
              2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) →
              (¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆) →
              let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
              let T := ⁅Z Rg a,Z Rg z⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              Nat.card (U Rg z) = 32 ∧ Nat.card C = 2 ∧
                H ⊔ T = H ⊔ C ∧ Nat.card (H ⊔ T : Subgroup (FreeAmalgam Rg)) = 4 ∧
                C ≤ Z Rg (p.walk.getVert 1) ∧
                C ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ ∧
                (∀ A : Subgroup (FreeAmalgam Rg), A ≤ stabilizer Rg a → ⁅C,A⁆ = ⁅T,A⁆) ∧
                4 ≤ Nat.card (⁅C,Q Rg (q.walk.getVert 1)⁆ : Subgroup (FreeAmalgam Rg)) ∧
                ⁅C,Q Rg (q.walk.getVert 1)⁆ ≤ Z Rg (q.walk.getVert 1) ∧
                C ⊓ Z Rg (q.walk.getVert 1) = ⊥ ∧
                ¬ Q Rg (q.walk.getVert 1) ≤ normalizer (C : Set (FreeAmalgam Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall a z d p q hqa hescape K hK hgen hstrict hfail
    exact plane_shifted_failure_attachment h e hz hk u hplane hb4 hsmall p q hqa
      hescape K hK hfail hgen hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the original projection, radical,
full central attachments and both cover alternatives. -/
theorem rankTwo_or_cubic_shifted_attachment :
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
          ∀ a z d (p : CriticalPath Rg (sourceGeometry h) a z)
            (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
            q.walk.getVert 2 = a →
            (¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) →
            ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
              Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
              2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) →
              (¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆) →
              let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
              let T := ⁅Z Rg a,Z Rg z⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              Nat.card (U Rg z) = 32 ∧ Nat.card C = 2 ∧
                H ⊔ T = H ⊔ C ∧ Nat.card (H ⊔ T : Subgroup (FreeAmalgam Rg)) = 4 ∧
                C ≤ Z Rg (p.walk.getVert 1) ∧
                C ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ ∧
                (∀ A : Subgroup (FreeAmalgam Rg), A ≤ stabilizer Rg a → ⁅C,A⁆ = ⁅T,A⁆) ∧
                4 ≤ Nat.card (⁅C,Q Rg (q.walk.getVert 1)⁆ : Subgroup (FreeAmalgam Rg)) ∧
                ⁅C,Q Rg (q.walk.getVert 1)⁆ ≤ Z Rg (q.walk.getVert 1) ∧
                C ⊓ Z Rg (q.walk.getVert 1) = ⊥ ∧
                ¬ Q Rg (q.walk.getVert 1) ≤ normalizer (C : Set (FreeAmalgam Rg)))) :=
  (coreExhaustion_or_cubic_shifted_attachment h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

