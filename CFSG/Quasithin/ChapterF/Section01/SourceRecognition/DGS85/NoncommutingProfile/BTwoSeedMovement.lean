module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedAction
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Nontrivial residual action on the central seed

The two critical centers move Q_alpha into the literal seed. Taking the
centralizer modulo that seed gives a normal subgroup with two-group
quotient, so the same displacement bound holds for O^2(L_alpha).
Commutator idempotence then shows that a trivial residual action on the
seed modulo D would centralize the full core modulo D. The residual and
the actual neighboring-core Sylow supplement would normalize the adjacent
core intersection, contradicting the earlier 6.5 obstruction.

The actor and its two-residual are literal subgroups; the ambient
completion need not be finite. Finiteness is used inside the local actor.
This proves the nontrivial-action step in 10.7, not seed saturation.
Source: DGS, Groups and Graphs (1985), proof of 10.7, printed p.158.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem residual_moves_into_layer
    (L Q J T : Subgroup G) (hQL : Q ≤ L) (hTL : T ≤ L)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G))
    (hLJ : L ≤ normalizer (J : Set G)) (hgen : T ⊔ Q = L)
    (hmove : ⁅T,Q⁆ ≤ J) :
    ⁅Q,(pResidual 2 L).map L.subtype⁆ ≤ J := by
  let C := commutatorPreimage L Q J
  have hCL : C ≤ L := commutatorPreimage_le L Q J
  have hn : L ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized L Q J L hLJ L.le_normalizer hLQ hLJ
  let : (C.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hCL).mpr hn
  have hs : C.subgroupOf L ⊔ Q.subgroupOf L = ⊤ := by
    apply top_unique
    have hg : T.subgroupOf L ⊔ Q.subgroupOf L = ⊤ := by
      rw [←subgroupOf_sup hTL hQL,hgen,subgroupOf_self]
    rw [←hg]
    exact sup_le_sup (comap_mono (le_commutatorPreimage hTL hmove)) le_rfl
  have hR : pResidual 2 L ≤ C.subgroupOf L :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top _ _ hQ.comap_subtype hs⟩
  have hr : (pResidual 2 L).map L.subtype ≤ C := by
    have hh := map_mono (f := L.subtype) hR
    rwa [map_subgroupOf_eq_of_le hCL] at hh
  rw [commutator_comm]
  exact (commutator_mono hr le_rfl).trans (commutator_commutatorPreimage_le L Q J hLJ)

private theorem residual_idempotent_in_local
    (L Q : Subgroup G) [Finite L] (hQL : Q ≤ L)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G)) :
    ⁅⁅Q,(pResidual 2 L).map L.subtype⁆,(pResidual 2 L).map L.subtype⁆ =
      ⁅Q,(pResidual 2 L).map L.subtype⁆ := by
  have hn : (Q.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQL).mpr hLQ
  let := hn
  have hh := commutator_isPPerfect_idempotent (pResidual 2 L) (Q.subgroupOf L)
    (isPPerfect_pResidual 2) hQ.comap_subtype le_normalizer_of_normal
  have hm := congrArg (map L.subtype) hh
  simpa only [map_commutator,map_subgroupOf_eq_of_le hQL] using hm

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem movement_core_normalized (x : Vertex F) :
    stabilizer F x ≤ normalizer (Q F x : Set G) :=
  (stabilizer F x).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The full core's residual displacement lies in the literal source seed. -/
theorem BTwoOppositeGeometry.core_residual_le_seed
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {t v m w z : Vertex F}
    (d : BTwoOppositeGeometry F t v m w z)
    (hactor : d.actor ≤ stabilizer F v) :
    ⁅Q F v,(pResidual 2 d.actor).map d.actor.subtype⁆ ≤ centralSeed F v m t := by
  have hnJ := d.seed_normalized h hS hb hactor
  have hQL : Q F v ≤ d.actor := d.actor_generators ▸ le_sup_right
  have hTL : Z F w ⊔ Z F z ≤ d.actor := d.actor_generators ▸ le_sup_left
  apply residual_moves_into_layer d.actor (Q F v) (centralSeed F v m t)
    (Z F w ⊔ Z F z) hQL hTL (isPGroup_pCoreIn 2 (stabilizer F v))
    (hactor.trans (movement_core_normalized v)) hnJ d.actor_generators.symm
  have hpair (x y : Vertex F) (hxy : (graph F).Adj x y)
      (hvx : (graph F).Adj v x) (hyl : Z F y ≤ d.actor) :
      ⁅Z F y,Q F v⁆ ≤ V F x 1 ⊓ Q F v := by
    have hyV : Z F y ≤ V F x 1 :=
      le_iSup_of_le y (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hxy)) le_rfl)
    have hQx : Q F v ≤ stabilizer F x :=
      (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F hvx).trans inf_le_right)
    apply le_inf
    · exact (commutator_mono hyV le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hQx.trans (graph_stabilizer_normalizes_V h x 1)))
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp
        (hyl.trans (hactor.trans (movement_core_normalized v)))
  exact commutator_sup_le_of_relative_normal d.actor (Z F w) (Z F z) (Q F v)
    (centralSeed F v m t) hnJ (le_sup_left.trans hTL) (le_sup_right.trans hTL)
    ((hpair m w d.terminal d.middle (le_sup_left.trans hTL)).trans
      (le_sup_left.trans le_sup_left))
    ((hpair t z d.opposite d.previous.symm (le_sup_right.trans hTL)).trans
      (le_sup_right.trans le_sup_left))

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The local residual and the two adjacent cores generate the original actor. -/
theorem BTwoCenterActionData.residual_core_supplement
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) :
    (pResidual 2 c.actor).map c.actor.subtype ⊔ (Q F m ⊔ Q F v) = c.actor := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hk : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype
  let T := c.imageSylow.comapOfKerIsPGroup c.quotient hk
    (by rw [MonoidHom.range_eq_top.mpr c.onto]; exact le_top)
  have hT : (T : Subgroup c.actor) = (Q F m ⊔ Q F v).subgroupOf c.actor := by
    change (c.imageSylow : Subgroup _).comap c.quotient = _
    rw [←c.neighbor_image,comap_map_eq,c.kernel,
      subgroupOf_sup c.neighbor_core_le c.core_le]
  have hh := congrArg (map c.actor.subtype) (pResidual_sup_sylow_eq_top T)
  simpa only [Subgroup.map_sup,hT,map_subgroupOf_eq_of_le
    (sup_le c.neighbor_core_le c.core_le),←MonoidHom.range_eq_map,range_subtype] using hh

/-- Nontrivial residual action on the seed quotient, the first contradiction
in 10.7. Triviality would make the actual adjacent-core intersection normal
in the full vertex stabilizer, contrary to the earlier 6.5 obstruction. -/
theorem BTwoCenterActionData.seed_residual_not_le_D
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G)) :
    ¬ ⁅centralSeed F v m t,(pResidual 2 c.actor).map c.actor.subtype⁆ ≤ D F m t := by
  intro htriv
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hmove := d.core_residual_le_seed h hS hb (hd.symm ▸ c.actor_le)
  rw [hd] at hmove
  let R := (pResidual 2 c.actor).map c.actor.subtype
  have hRD : ⁅Q F v,R⁆ ≤ D F m t := by
    rw [←residual_idempotent_in_local c.actor (Q F v) c.core_le
      (isPGroup_pCoreIn 2 (stabilizer F v))
      (c.actor_le.trans (movement_core_normalized v))]
    exact (commutator_mono hmove le_rfl).trans htriv
  let I := Q F m ⊓ Q F v
  have hDQ : D F m t ≤ I := le_inf inf_le_left d.separated
  have hRI : R ≤ normalizer (I : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_right le_rfl).trans hRD).trans hDQ)
  have hQv_m : Q F v ≤ stabilizer F m :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F c.middle).trans inf_le_right)
  have hQm_v : Q F m ≤ stabilizer F v :=
    (source_Z_Q_U h m).2.trans ((ballKernel_one_le_edge F c.middle.symm).trans inf_le_right)
  have hEI : stabilizer F v ⊓ stabilizer F m ≤ normalizer (I : Set G) :=
    (le_inf (inf_le_right.trans (movement_core_normalized m))
      (inf_le_left.trans (movement_core_normalized v))).trans inf_normalizer_le_normalizer_inf
  have hLI : c.actor ≤ normalizer (I : Set G) := by
    rw [←c.residual_core_supplement h]
    exact sup_le hRI ((sup_le (le_inf hQm_v (Q_le_stabilizer F m))
      (le_inf (Q_le_stabilizer F v) hQv_m)).trans hEI)
  apply hnot
  intro x hx
  obtain ⟨l,hl,b,hb,rfl⟩ := c.factor x hx
  exact (normalizer (I : Set G)).mul_mem (hLI hl) (hEI hb)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
