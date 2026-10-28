module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.WholeSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.FullRadical

/-!
# The contained-core branch of MS93 (3.7)(3)

Assume the actual critical image Z_alpha Q_alpha' / Q_alpha' has order q
and Q_alpha lies in Z_alpha Q_alpha'. The opposite core centralizes its
Z-layer, so the centralizer index on Q_alpha is at most q. The four-root
whole-section argument then gives Q_alpha = U_alpha C_Q_alpha(L_alpha).
Its central omega subgroup is Z_alpha: factoring an involution into its
moving and fixed parts puts the fixed involution in the actual incident
omega-center, without deleting the fixed attachment.

These are the core decomposition and X = Z conclusions in the first
subcase of (3.7)(3). The noncontained-core exclusion, the separate overlap
index calculation and the selection of an order-q critical pair remain
source obligations. No order-q premise is imposed on the saturated radical.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h d in
private theorem centralizer_index_of_fixed_supplement {G : Type*} [Group G]
    (T A B C : Subgroup G) [Finite T]
    (hAB : A ⊔ B = T) (hTC : T ≤ normalizer (C : Set G))
    (hAC : A ≤ centralizer (C : Set G)) :
    (centralizer (C : Set G)).relIndex T =
      (centralizer (C : Set G)).relIndex B := by
  let N := (centralizer (C : Set G)).subgroupOf T
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hTC.trans (normalizer_le_normalizer_centralizer C))
  have hBT : B ≤ T := le_sup_right.trans_eq hAB
  have htop : B.subgroupOf T ⊔ N = ⊤ := by
    apply top_unique
    have hAT : A ≤ T := le_sup_left.trans_eq hAB
    have hjoin : A.subgroupOf T ⊔ B.subgroupOf T = ⊤ := by
      rw [←subgroupOf_sup hAT hBT,hAB,subgroupOf_self]
    rw [←hjoin]
    exact sup_le (fun x hx => mem_sup_right (hAC hx)) le_sup_left
  calc
    _ = N.relIndex (⊤ : Subgroup T) := by rw [relIndex_top_right]; rfl
    _ = N.relIndex (B.subgroupOf T) := by rw [←htop,relIndex_sup_right]
    _ = _ := relIndex_subgroupOf hBT

/-- The first subcase of MS93 (3.7)(3) bounds movement of the full core.
The order-q premise concerns the critical Z-image, and Q is contained in
the product of that Z-layer with the opposite core. -/
theorem core_centralizer_index_of_contained_core
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Q d.radical a) ≤ 2^n := by
  have hZaS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hQS : Q d.radical z ≤ stabilizer d.radical z := fun _ hx => hx.1
  let T := Q d.radical z ⊔ Z d.radical a
  have hTS : T ≤ stabilizer d.radical z := sup_le hQS hZaS
  let := finite_stabilizer d.radical z
  let : Finite T := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  have he := centralizer_index_of_fixed_supplement T (Q d.radical z)
    (Z d.radical a) (Z d.radical z) rfl (hTS.trans (Z_normalized d.radical z))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color)))
  have hCZ : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a) = (Q d.radical z).subgroupOf (Z d.radical a) := by
    rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color]
    ext x
    exact ⟨fun hx => ⟨hZaS x.property,hx⟩,fun hx => hx.2⟩
  have hi : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = 2^n := by
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a)).index = _
    rw [hCZ]
    exact hcritical
  have hQT : Q d.radical a ≤ T := by simpa only [T,sup_comm] using hinside
  exact (relIndex_le_of_le_right hQT index_ne_zero_of_finite).trans_eq (he.trans hi)

/-- A decomposition of the full core identifies X with the source-generated
Z-layer. Its fixed factor is kept: each fixed involution centralizes the
whole endpoint stabilizer and belongs to the actual incident omega-center. -/
theorem X_eq_Z_of_core_decomposition
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (hcore : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a) :
    X d.radical a = Z d.radical a := by
  have hZX : Z d.radical a ≤ X d.radical a := g.omega_bound a ha (by
    rw [g.distance_constant a ha]; exact hb)
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    (hZX.trans (omegaCenter_le _))
  have hUD : U d.radical a ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha))).trans (centralizer_le inf_le_left)
  apply le_antisymm ?_ hZX
  intro x hx
  have hxQ : x ∈ Q d.radical a := omegaCenter_le _ hx
  rw [hcore,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hxQ
  obtain ⟨u,hu,v,hv,rfl⟩ := hxQ
  have hvX : v ∈ X d.radical a := by
    have hh := (X d.radical a).mul_mem
      ((X d.radical a).inv_mem (hZX (U_le_Z a hu))) hx
    simpa only [inv_mul_cancel_left] using hh
  have hvS : v ∈ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hL : Ltilde d.radical a ≤ centralizer ({v} : Set (FreeAmalgam d.radical)) :=
      fun l hl => mem_centralizer_singleton_iff.mpr (hv.2 l hl)
    have hQ : Q d.radical a ≤ centralizer ({v} : Set (FreeAmalgam d.radical)) :=
      fun q hq => mem_centralizer_singleton_iff.mpr ((mem_omegaCenter_iff.mp hvX).2.2 q hq)
    have hh := sup_le hL hQ
    rw [c.residual_sup_core g hb] at hh
    exact fun y hy => mem_centralizer_singleton_iff.mp (hh hy)
  have hvE : v ∈ edgeOmega d.radical t := mem_omegaCenter_iff.mpr
    ⟨c.core_le_edge hv.1,(mem_omegaCenter_iff.mp hvX).2.1,
      fun y hy => hvS y (c.edge_le hy)⟩
  have hvZ : v ∈ Z d.radical a := by
    rw [Z,if_pos ha]
    have hle : edgeOmega d.radical t ≤
        ⨆ b, ⨆ (_ : Adjacent d.radical a b), edgeOmega d.radical b :=
      le_iSup_of_le t (le_iSup_of_le hat le_rfl)
    exact hle hvE
  exact (Z d.radical a).mul_mem (U_le_Z a hu) hvZ

/-- The contained-core subcase of source (3.7)(3), with its literal critical
image and complete fixed attachment. The other source subcase, which excludes
failure of the containment, remains a separate obligation. -/
theorem source_three_contained_core
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    Q d.radical a = U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a = Z d.radical a := by
  have hc := core_eq_moving_sup_fixed_of_critical_centralizer_index h d path hb hcritical
    (core_centralizer_index_of_contained_core h d path hcritical hinside)
  exact ⟨hc,X_eq_Z_of_core_decomposition h d g (by omega) path.start_color hat c hc⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
