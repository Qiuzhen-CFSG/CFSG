module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.CharacteristicAction

/-!
# The two factors in the original star's center action

Let C be the full center of the minimum replacement and V its intersection
with the intrinsic moving core. In the field-sized branch, the full core
factorization gives C = V A, where A = C intersect C_H(K). The whole A is
normal in H and centralizes the minimum overgroup M. No fixed attachment is
removed in this decomposition.

For the actual original star T, write B = R intersect M and Q₀ = T intersect
O₂(H). The factorization T = B Q₀ and the preceding center decomposition
show that [C,Q₀] = [A,Q₀]. They also identify the full kernel on V:
C_T(V) = Q₀ C_T(C). Thus the possible extra center action occurs precisely
on the retained component-fixed factor.

The actions of B and Q₀ on C have disjoint images: their displacements lie
in the disjoint original overlap and fixed-core displacement. Both images
are normal in the star image, so they commute. Their product is the entire
star action, of order q squared times the order of the Q₀ image. The final
consumer constructs the same marked, saturated source star from Input and
the supplied distance-two replacement in the proper nonsylow branch.

This controls the extra factor without asserting that it vanishes. The
characteristic comparison, minimum marked preservation and saturation,
Sylow branch, field restriction and final block assembly remain open.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7), printed pp.872--875, with the separate minimum characteristic
cut from Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem replacement_center_split
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let C := d.radical ⊓ centralizer (d.radical : Set d.overgroup)
    let U := ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆
    C = (U ⊓ centralizer (d.radical : Set d.overgroup)) ⊔
      (C ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hab : Adjacent d.radical (alpha d.radical) (beta d.radical) :=
    (adjacent_iff_exists_common d.radical _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hab hat
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hmT : d.radical.map f=Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f =
      U d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl,←U_act,hv]
  have hmK : (K.subgroupOf d.overgroup).map f = Ltilde d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←replacement_residual h d,←Ltilde_alpha,←Ltilde_act,hv]
  obtain ⟨he,hfixed⟩ := replacement_field_sized_center_decomposition h d path hb hat hzt hsize
  let C := Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
  have he' : C = (U d.radical (alpha d.radical) ⊓
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical))) ⊔
      (C ⊓ centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) := by
    apply le_antisymm
    · conv_lhs => dsimp only [C]; rw [he]
      exact sup_le le_sup_left ((le_inf (le_sup_right.trans_eq he.symm)
        (hfixed.trans (centralizer_le (Ltilde_le_stabilizer _)))).trans le_sup_right)
    · exact sup_le (le_sup_left.trans_eq he.symm) inf_le_left
  dsimp only
  apply map_injective hf
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective f hf,
    ←map_inf_centralizer_of_injective f hf,
    ←map_inf_centralizer_of_injective f hf,
    ←map_inf_centralizer_of_injective f hf,hmT,hmU,hmK]
  exact he'

/-- The full minimum center splits into the root-fixed intrinsic core and
its complete component-fixed part, in the ORIGINAL ambient group. -/
theorem minimum_center_decomposition
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let C := d.ambient ⊓ centralizer (d.ambient : Set H)
    let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
    let A := C ⊓ centralizer (K : Set H)
    C = V ⊔ A ∧ A ≤ centralizer (d.overgroup : Set H) ∧ A.Normal := by
  let := h.component_normal
  let := replacement_normal h d
  let := d.characteristic
  have hp : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hp
  have hmT : d.radical.map d.overgroup.subtype=d.ambient := map_subgroupOf_eq_of_le le_sup_right
  have hmK : (K.subgroupOf d.overgroup).map d.overgroup.subtype=K :=
    map_subgroupOf_eq_of_le le_sup_left
  have he := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype)
    (replacement_center_split h d g hb hsize)
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,hmT,hmU,hmK] at he
  let C := d.ambient ⊓ centralizer (d.ambient : Set H)
  let A := C ⊓ centralizer (K : Set H)
  have hAM : A ≤ centralizer (d.overgroup : Set H) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
  have hRA : R ≤ normalizer (A : Set H) := by
    intro r hr
    have hrd : r ∈ normalizer (d.ambient : Set H) :=
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)) hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp only [A,C]
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
      ←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
      mem_normalizer_iff_map_conj_eq.mp hrd,
      mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (K : Set H) by
        rw [normalizer_eq_top]; trivial)]
  refine ⟨he,hAM,?_⟩
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [←original_sup h]
  exact sup_le ((le_centralizer_iff.mp (show A ≤ centralizer (K : Set H) from inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _)) hRA


/-- The full fixed part accounts for precisely the extra two-core movement.
The kernel of the star action on the moving part is the product of the
original two-core intersection and the kernel on the WHOLE center. -/
theorem star_center_fixed_factor_control
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let T := (starCentralizer R Y).map R.subtype
    let C := d.ambient ⊓ centralizer (d.ambient : Set H)
    let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
    let A := C ⊓ centralizer (K : Set H)
    let Q₀ := T ⊓ pCore 2 H
    ⁅C,Q₀⁆ = ⁅A,Q₀⁆ ∧ ⁅C,Q₀⁆ ≤ A ∧
      T ⊓ centralizer (V : Set H) = Q₀ ⊔ (T ⊓ centralizer (C : Set H)) := by
  let T := (starCentralizer R Y).map R.subtype
  let C := d.ambient ⊓ centralizer (d.ambient : Set H)
  let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
  let A := C ⊓ centralizer (K : Set H)
  let Q₀ := T ⊓ pCore 2 H
  obtain ⟨he,hAM,hAn⟩ := minimum_center_decomposition h d g hb hsize
  change C = V ⊔ A at he
  let := hAn
  have hVC : V ≤ C := le_sup_left.trans_eq he.symm
  have hQV : Q₀ ≤ centralizer (V : Set H) :=
    inf_le_right.trans ((original_whole_core_centralizer h d g hb).ge.trans
      (centralizer_le (show V ≤ (blockU K).map K.subtype from inf_le_left)))
  have hmove : ⁅C,Q₀⁆ = ⁅A,Q₀⁆ := by
    apply le_antisymm _ (commutator_mono inf_le_left le_rfl)
    apply commutator_le.mpr
    intro c hc q hq
    change c ∈ C at hc
    rw [he,sup_comm] at hc
    obtain ⟨a,ha,v,hv,rfl⟩ := mem_sup_of_normal_left.mp hc
    have hvq : Commute v q := hQV hq v hv
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hvq,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator ha hq
  refine ⟨hmove,hmove.trans_le (commutator_le_left _ _),le_antisymm ?_ ?_⟩
  · rintro x ⟨hx,hxv⟩
    obtain ⟨hf,hfactor⟩ := star_factorization_over_minimum h d P Y hY hmin hrest
    obtain ⟨b,hb,q,hq,heq⟩ := hf x hx
    have hbT : b ∈ T := (le_sup_left.trans_eq hfactor.symm) hb
    have hbV : b ∈ centralizer (V : Set H) := by
      have hh := (centralizer (V : Set H)).mul_mem hxv
        ((centralizer (V : Set H)).inv_mem (hQV hq))
      simpa only [←heq,mul_inv_cancel_right] using hh
    have hbC : b ∈ centralizer (C : Set H) := by
      have hCb : C ≤ centralizer ({b} : Set H) := by
        rw [he]
        apply sup_le
        · intro v hv b' hb'
          have hbb : b' = b := Set.mem_singleton_iff.mp hb'
          subst b'
          exact (hbV v hv).symm
        · intro a ha b' hb'
          have hbb : b' = b := Set.mem_singleton_iff.mp hb'
          subst b'
          exact hAM ha b hb.2
      intro c hc
      exact (hCb hc b (by simp)).symm
    rw [←heq]
    exact (Q₀ ⊔ (T ⊓ centralizer (C : Set H))).mul_mem
      (mem_sup_right ⟨hbT,hbC⟩) (mem_sup_left hq)
  · apply sup_le
    · exact le_inf inf_le_left hQV
    · exact inf_le_inf_left T (centralizer_le hVC)

omit h [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem disjoint_center_action_images
    {G : Type*} [Group G] (C B Q₀ : Subgroup G) [C.Normal]
    (hd : Disjoint ⁅C,B⁆ ⁅C,Q₀⁆) :
    Disjoint (B.map (MulAut.conjNormal (H := C)))
      (Q₀.map (MulAut.conjNormal (H := C))) := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨⟨b,hb,he⟩,⟨q,hq,he'⟩⟩
  change x=1
  rw [←he]
  apply MulEquiv.ext
  intro c
  apply Subtype.ext
  change b*(c:G)*b⁻¹=(c:G)
  have heq := congrArg (fun a : MulAut C => (a c : G)) (he.trans he'.symm)
  change b*(c:G)*b⁻¹=q*(c:G)*q⁻¹ at heq
  have hec : ⁅b,(c:G)⁆=⁅q,(c:G)⁆ := by
    simpa only [commutatorElement_def,mul_assoc] using
      congrArg (fun y : G => y*(c:G)⁻¹) heq
  have hz : ⁅b,(c:G)⁆=1 := disjoint_iff_inf_le.mp hd
    ⟨commutator_comm B C ▸ commutator_mem_commutator hb c.property,
      hec ▸ (commutator_comm Q₀ C ▸ commutator_mem_commutator hq c.property)⟩
  rw [(commutatorElement_eq_one_iff_commute.mp hz).eq,mul_inv_cancel_right]

/-- On the same full characteristic center, the original intersection and
the star's original two-core intersection have disjoint action images.
Their product is the whole star action, with its exact order retained. -/
theorem star_center_action_direct_factors
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let T := starCentralizer R Y
    let B := d.overgroup.subgroupOf R
    let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
    let θ := minimumCenterAction d
    T.map θ = B.map θ ⊔ Q₀.map θ ∧ Disjoint (B.map θ) (Q₀.map θ) ∧
      B.map θ ≤ centralizer (Q₀.map θ : Set (MulAut (minimumCenter d))) ∧
      Nat.card (T.map θ) = 2^(2*n) * Nat.card (Q₀.map θ) := by
  let T := starCentralizer R Y
  let B := d.overgroup.subgroupOf R
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let C := minimumCenter d
  let θ := minimumCenterAction d
  have hmC : C.map R.subtype=d.ambient ⊓ centralizer (d.ambient : Set H) := by
    dsimp only [C,minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
  have hmB : B.map R.subtype=R ⊓ d.overgroup :=
    (subgroupOf_map_subtype _ _).trans (inf_comm _ _)
  have hmQ : Q₀.map R.subtype=T.map R.subtype ⊓ pCore 2 H := by
    rw [map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype]
    rw [←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
  have hfactor : T=B ⊔ Q₀ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmB,hmQ]
    exact (star_factorization_over_minimum h d P Y hY hmin hrest).2
  obtain ⟨hdis,hcard,hDU,hjoin⟩ := original_proper_nonsylow_center_overlap h d g hb hnsyl hne
  have hEC := minimum_center_core_displacement_centralizes h d g hb
    (T.map R.subtype ⊓ pCore 2 H) inf_le_right
  let := h.component_normal
  have hDU' := hDU.trans (commutator_le_left _ _)
  have hd : Disjoint ⁅C,B⁆ ⁅C,Q₀⁆ := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply R.subtype_injective
    have hD : (x:H) ∈ ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆ := by
      rw [←hmC,←hmB,←map_commutator]
      exact mem_map_of_mem _ hx.1
    have hE : (x:H) ∈ ⁅d.ambient ⊓ centralizer (d.ambient : Set H),T.map R.subtype ⊓ pCore 2 H⁆ := by
      rw [←hmC,←hmQ,←map_commutator]
      exact mem_map_of_mem _ hx.2
    exact disjoint_iff_inf_le.mp hdis ⟨hD,⟨hDU' hD,hEC hE⟩⟩
  have hactdis : Disjoint (B.map θ) (Q₀.map θ) := disjoint_center_action_images C B Q₀ hd
  have hact : T.map θ=B.map θ ⊔ Q₀.map θ := by rw [hfactor,Subgroup.map_sup]
  have hBn : B.Normal := by
    let := replacement_normal h d
    dsimp only [B]
    infer_instance
  let := hBn
  have hQn : Q₀.Normal := by
    dsimp only [Q₀,T]
    infer_instance
  let := hQn
  have hc : B.map θ ≤ centralizer (Q₀.map θ : Set (MulAut C)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply le_trans ?_ (disjoint_iff_inf_le.mp hactdis)
    rw [←map_commutator]
    exact le_inf (map_mono (commutator_le_left _ _))
      (map_mono (commutator_le_right _ _))
  have hn : Q₀.map θ ≤ normalizer (B.map θ : Set (MulAut C)) :=
    (map_mono (show Q₀ ≤ normalizer (B : Set R) from by
      rw [normalizer_eq_top]; exact le_top)).trans (B.le_normalizer_map θ)
  refine ⟨hact,hactdis,hc,?_⟩
  rw [hact,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hactdis,
    original_minimum_center_action_card h d g hb hnsyl hne]

/-- The actual selected source star has the full fixed-factor kernel and
the exact two-factor center action. The proper nonsylow hypotheses supply
the field-sized minimum image; no extra action or saturation premise remains. -/
theorem exists_source_star_center_action_factors
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let C := d.ambient ⊓ centralizer (d.ambient : Set H)
       let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
       let A := C ⊓ centralizer (K : Set H)
       let Q₀ := T ⊓ pCore 2 H
       ⁅C,Q₀⁆ = ⁅A,Q₀⁆ ∧ ⁅C,Q₀⁆ ≤ A ∧
         T ⊓ centralizer (V : Set H) = Q₀ ⊔ (T ⊓ centralizer (C : Set H))) ∧
      (let T := starCentralizer R Y
       let B := d.overgroup.subgroupOf R
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let θ := minimumCenterAction d
       T.map θ = B.map θ ⊔ Q₀.map θ ∧ Disjoint (B.map θ) (Q₀.map θ) ∧
         B.map θ ≤ centralizer (Q₀.map θ : Set (MulAut (minimumCenter d))) ∧
         Nat.card (T.map θ) = 2^(2*n) * Nat.card (Q₀.map θ)) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl⟩ :=
    exists_source_star_intrinsic_reduction h d
  exact ⟨P,Y,hY,hn,hmin,hmark,hsat,
    star_center_fixed_factor_control h d g hb P Y hY hmin hrest
      (replacement_proper_nonsylow_card h d g hb hnsyl hne),
    star_center_action_direct_factors h d g hb P Y hY hmin hrest hnsyl hne⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
