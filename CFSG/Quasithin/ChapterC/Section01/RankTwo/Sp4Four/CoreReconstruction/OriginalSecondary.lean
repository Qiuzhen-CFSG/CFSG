module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.NonFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.PairedOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalXDecomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.LiteralInitialCover

/-!
# Original non-Frattini secondary seeds

The faithful simple quotient forces a maximal secondary seed into the opposite
local two-core. A normal subgroup in both critical Z-layers is fixed by the
component; it vanishes when the entire X-layer has trivial fixed subgroup.
Consequently the source secondary commutator identity forces its whole orbit
back into X in this center-free case.

The original critical-index theorem also supplies the X-decomposition, and
literal natural-cover coordinates give order 256 when the central kernel is
trivial. These statements preserve the original graph, quotient and kernels.
The Chapter10 extension constructs their hypotheses on the tensor overgroup.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (3.6), printed pp.867 and870--871. The critical-distance
reduction and the secondary commutator and movement claims remain separate.
-/

public section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {M J : Type*} [Group M] [Finite M] [Group J]
  {R : Subgroup M} {geometry : Geometry R} {a t z : Vertex R}

private theorem centralizes_of_simple_image {H : Type*} [Group H]
    (q : H →* J) (hq : Function.Surjective q) (P E K : Subgroup H) [P.Normal]
    [(K.map q).Normal] [IsSimpleGroup (K.map q)]
    (hna : ¬ IsMulCommutative (K.map q))
    (hc : centralizer (K.map q : Set J) = ⊥)
    (hk : q.ker ≤ centralizer (P : Set H))
    (hE : ¬ E ≤ q.ker) (hEP : E ≤ centralizer (P : Set H)) :
    K ≤ centralizer (P : Set H) := by
  let C := centralizer (P : Set H)
  let : (C.map q).Normal := Normal.map inferInstance q hq
  have hCne : C.map q ≠ ⊥ := by
    intro hz
    exact hE (hEP.trans ((map_eq_bot_iff C).mp hz))
  have hKC := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    (K.map q) hna hc (C.map q) hCne
  have h := comap_mono (f := q) hKC
  rw [comap_map_eq,comap_map_eq,sup_of_le_left hk] at h
  exact le_sup_left.trans h

omit [Finite M] in
theorem normal_critical_intersection_eq_bot
    (N : Subgroup (FreeAmalgam R)) (hNa : N ≤ Z R a) (hNz : N ≤ Z R z)
    (hn : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)))
    (haX : Z R a ≤ X R a) (hzS : Z R z ≤ stabilizer R a)
    (hzQ : ¬ Z R z ≤ Q R a) [IsElementaryAbelian 2 (Z R z)]
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hfixed : X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥) : N = ⊥ := by
  let S := stabilizer R a
  let P := N.subgroupOf S
  let E := (Z R z).subgroupOf S
  let K := (Ltilde R a).subgroupOf S
  let : P.Normal := normal_subgroupOf_of_le_normalizer hn
  have hQP : κ.ker ≤ centralizer (P : Set S) := by
    intro x hx n hn
    have hxQ : (x : FreeAmalgam R) ∈ Q R a := hk ▸ mem_map_of_mem S.subtype hx
    exact Subtype.ext (Q_le_centralizer_X R a hxQ n (haX (hNa hn)))
  have hE : ¬ E ≤ κ.ker := by
    intro h
    apply hzQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype (h (show (⟨x,hzS hx⟩ : S) ∈ E from hx))
  have hEP : E ≤ centralizer (P : Set S) := by
    intro x hx n hn
    apply Subtype.ext
    have hh := (IsMulCommutative.is_comm (M := Z R z)).comm ⟨n,hNz hn⟩ ⟨x,hx⟩
    exact congrArg (fun v : Z R z => (v : FreeAmalgam R)) hh
  have hKP := centralizes_of_simple_image κ hκ P E K hna hc hQP hE hEP
  apply le_bot_iff.mp
  rw [←hfixed]
  refine le_inf (hNa.trans haX) ?_
  intro n hn k hk
  have hnS : n ∈ S := (hNa.trans (haX.trans ((omegaCenter_le _).trans (fun _ hx => hx.1)))) hn
  have hh := hKP (show (⟨k,Ltilde_le_stabilizer a hk⟩ : S) ∈ K from hk)
    ⟨n,hnS⟩ (show (⟨n,hnS⟩ : S) ∈ P from hn)
  exact (congrArg Subtype.val hh).symm

theorem secondarySeed_le_kernel_of_nonfrattini
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hp : IsPGroup 2 (Q R a))
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    secondarySeed R a t z ≤ Q R a := by
  have hpos : 0 < geometry.b R := by omega
  have hZa : Z R a ≤ X R a := geometry.omega_bound a path.start_color
    (lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm)
  have hZz : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  by_contra hnot
  apply hlarge
  apply core_le_frattini_of_local_commutator_le a (secondarySeed R a t z)
    ((secondarySeed_le R a t z).trans hZz) hnot hp κ hκ hk hna hc
  rw [commutator_comm]
  exact (secondarySeed_greatest R geometry path.end_color hzt hpos).2.1.trans
    (((edge_Z_le_endpoint R path.start_color hat).trans hZa).trans le_sup_right)

theorem secondary_orbit_le_X_of_seed_commutator
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hC : EdgeCentralizerCondition R)
    (hYQ : secondarySeed R a t z ≤ Q R a)
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hfixed : X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (hcomm : ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ ≤
      ⁅secondarySeed R a t z,Q R a⁆) :
    secondaryOrbit R a (secondarySeed R a t z) ≤ X R a := by
  let Y := secondarySeed R a t z
  let A := secondaryOrbit R a Y
  let S := stabilizer R a
  have hpos : 0 < geometry.b R := by omega
  have hZaX : Z R a ≤ X R a := geometry.omega_bound a path.start_color
    (lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm)
  have hzS : Z R z ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hzQ : ¬ Z R z ≤ Q R a := (critical_reverse R geometry hC a path.start_color
    (lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm)
    z path.end_color path.critical).2
  let := Z_elementary_of_positive R geometry z path.end_color
    (lt_of_lt_of_eq hpos (geometry.distance_constant z path.end_color).symm)
  have hAQ : A ≤ Q R a := conjugatesIn_le_of_normalized Y S _ hYQ (Q_normalized R a)
  have hAS : A ≤ S := hAQ.trans (fun _ hx => hx.1)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  let : (A.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer (conjugatesIn_normalized Y S)
  let : ((Q R a).subgroupOf S).Normal := Q_normal R a
  let N := ⁅A.subgroupOf S,(Q R a).subgroupOf S⁆
  have hNm : N.map S.subtype = ⁅A,Q R a⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS]
  have hn : S ≤ normalizer ((⁅A,Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    have h := N.le_normalizer_map S.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype,hNm] at h
    exact h
  have hNt : ⁅A,Q R a⁆ ≤ Z R t := hcomm.trans
    (secondarySeed_greatest R geometry path.end_color hzt hpos).2.1
  have hzero : ⁅A,Q R a⁆ = ⊥ := normal_critical_intersection_eq_bot _
    (hNt.trans (edge_Z_le_endpoint R path.start_color hat))
    (hNt.trans (edge_Z_le_endpoint R path.end_color hzt)) hn hZaX hzS hzQ
    κ hκ hk hna hc hfixed
  have hYA : Y ≤ A := by
    change Y ≤ conjugatesIn Y S
    rw [conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy Y S
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hzero
  let : IsElementaryAbelian 2 Y := secondarySeed_elementary R geometry path.end_color hpos
  have hYX : Y ≤ X R a := by
    intro y hy
    exact mem_omegaCenter_iff.mpr
      ⟨hYQ hy,elemPow_eq_one_of_isElementaryAbelian y hy,hcentral (hYA hy)⟩
  exact conjugatesIn_le_of_normalized Y S _ hYX (X_normalized R a)

theorem original_secondarySeed_le_kernel
    (R : Subgroup M) (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (q : M →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 M)
    [((pResidual 2 M).map q).Normal]
    [IsSimpleGroup ((pResidual 2 M).map q)] [IsQuasisimple ((pResidual 2 M).map q)]
    (hC : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    {geometry : Geometry R} {a t z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    secondarySeed R a t z ≤ Q R a := by
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := vertex_coordinates_with_kernel R hp hQR path.start_color
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hκ : Function.Surjective κ :=
    ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,hcore]
    exact hiQ
  have hL : ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = (pResidual 2 M).map q := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  let : (((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal := hL ▸ inferInstance
  let : IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := hL ▸ inferInstance
  have hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := by
    rw [hL]
    exact Group.IsPerfect.not_isMulCommutative _
  have hcent : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥ := by
    rw [hL]; exact hC
  exact secondarySeed_le_kernel_of_nonfrattini path hb hat hzt
    (Q_isPGroup R hp hQR a path.start_color) κ hκ hkQ hna hcent hlarge

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_nonfrattini_X_decomposition
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  have hind := original_critical_indices_eq_four_of_nonfrattini R hms hp hne hQR
    hself hfaith q hq hcore hc hC hsq path hb hlarge
  exact SourceComparison.original_small_critical_X_decomposition R hms hp hne hQR
    hself hfaith q hq hcore hc hC hsq path (by omega) (by omega)

theorem original_initial_card_of_fixed_eq_bot
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false) [IsElementaryAbelian 2 (U R a)]
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥) :
    Nat.card (U R a) = 256 := by
  obtain ⟨F,hF,σ,p,hp',f,hf,hact,hker⟩ :=
    LocalPackage.initial_subgroup_cover_at_vertex R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq ha
  have hinj : Function.Injective p := by
    change Function.Injective p.toLinearMap
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    have hv' : v.toMul ∈ p.toLinearMap.ker.toAddSubgroup.toSubgroup' := hv
    have hz := mem_map_of_mem (U R a).subtype hv'
    rw [hker,hfixed] at hz
    exact Additive.toMul.injective (Subtype.ext (mem_bot.mp hz))
  change Nat.card (Additive (U R a)) = 256
  rw [Nat.card_congr (Equiv.ofBijective p ⟨hinj,hp'.1⟩)]
  change Nat.card ((Fin 2 ⊕ Fin 2) → F.Carrier) = 256
  rw [Nat.card_fun,Nat.card_sum,Nat.card_fin,F.card_eq,hF]
  decide

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
