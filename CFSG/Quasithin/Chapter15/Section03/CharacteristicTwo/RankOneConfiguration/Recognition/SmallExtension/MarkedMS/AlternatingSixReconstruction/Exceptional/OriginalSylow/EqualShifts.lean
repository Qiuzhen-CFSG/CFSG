module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EqualKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.CentralStrict
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
/-!
# Strict-slice backward shifts for every Borel mover comparison

Transport the second selected seed back before combining the two actors.
The common reverse-kernel line is fixed by both selected movers, hence by
their generated stabilizer and by the same transporter. This identifies
the two full-kernel displacements on the whole original seed.

The join of those two kernels would therefore move at most a line of the
whole moving cover. Its common fixed subgroup is preserved by the common
quadratic mover and by both critical endpoints modulo the starting seed.
Their generation identity puts this common fixer in the Baumann slice,
contradicting the strict index. This estimates the whole-seed common fixer;
no equality of fixed subgroups is inferred from restricted hyperplanes.

The resulting equal-mover backward path combines with CentralStrict's
distinct-mover result. All path overlaps, the proper Borel movers, original
cubic kernel and both full covers remain. Paths applies the shift to obtain
unconditional radius escape; terminal distance exclusions remain separate.

Source: Meierfrankenfeld--Stellmacher (1993), (5.6)--(5.8), printed
pp.917--920; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e hz hk in
/-- Both trapped critical seeds normalize the common-fixer product with the
starting seed. Their actual generation identity puts the common fixer in the
starting Baumann slice, retaining the full central attachments. -/
theorem borel_equal_paired_trapped_fixer_le_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    Z Rg c ⊓ centralizer
      ((Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let A := Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg)
  let F := Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  let Y := F ⊔ Z Rg (alpha Rg)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  let J := edgeOffenderJoin c t
  have hJT : J ≤ Q Rg t :=
    (remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct).2.2.1
  have hAJ : A ≤ J := (sup_le inf_le_right inf_le_right).trans
    ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.1.trans heq.le)
  have hquad : ⁅⁅Z Rg c,J⁆,J⁆ = ⊥ :=
    remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hc hct
  have hab : ⁅J,J⁆ ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm J (Z Rg c)] using hquad
    · exact hquad
  have hFt : J ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    abelian_action_preserves_fixed J (Z Rg c) A
      ((hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c))
      hAJ hab
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hr : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4)
      (hrbad : Z Rg c ≤ Q Rg (r.walk.getVert (r.walk.length-2)))
      (hA : Z Rg w ⊓ Q Rg (alpha Rg) ≤ A) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    have hFmove := small_critical_predecessor_commutator h e hz hk hb r hr F
      (inf_le_left.trans hrbad) (inf_le_right.trans (centralizer_le hA))
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      F (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) ((inf_le_left.trans hZV).trans
        ((sourceGeometry h).V_local _ rfl hb)) (Z_le_stabilizer Rg _) hFmove
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hp hbad le_sup_left
  have hqY := hmove q hq hbad' le_sup_right
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    rw [heq]
    exact (le_inf hFt ((hJT.trans (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat))).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
    (sup_le (inf_le_left.trans hZV) (Z_le_VBall Rg _ 2)) hYN hpY)

include h e hz hk in
/-- With the strict source slice, the two full reverse omega kernels move
the entire moving cover by more than a line. The two kernels are taken on
the same trapped paths used in the generation identity. -/
theorem borel_equal_paired_trapped_joint_movement_gt_two
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    2 < Nat.card (⁅U Rg c,
      Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg)⁆ :
        Subgroup (FreeAmalgam Rg)) := by
  by_contra! hcard
  let A := Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hAG : A ≤ stabilizer Rg c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hi := moving_small_commutator_fixed_index h e hz hk hc A hAG hcard
  have hFB : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    borel_equal_paired_trapped_fixer_le_slice h e hz hk u hR p q hp hq hat hct heq hgen hbad hbad'
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z Rg c)).trans hFB)
    (index_ne_zero_of_finite (H := (U Rg c ⊓ centralizer
      (A : Set (FreeAmalgam Rg))).subgroupOf (U Rg c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hs) (hh.trans hi)
include h e hz hk in
/-- Transporting the second trapped seed back gives two actors against the
same reverse kernel. Strictness excludes the zero case. Their combined line
is fixed by the actual stabilizer and by the retained transporter, yielding
equal displacements of the whole original seed by the two full kernels. -/
theorem borel_equal_strict_paired_kernel_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z))
    (hqverts : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg))
    (hpair : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg)) :
    let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆
    Nat.card H = 2 ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      H.map (MulAut.conj x).toMonoidHom = H ∧
      ⁅Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg),Z Rg c⁆ = H := by
  let f := (MulAut.conj x).toMonoidHom
  have hi : Function.Injective f := (MulAut.conj x).injective
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hya : act Rg x⁻¹ (alpha Rg) = alpha Rg :=
    (stabilizer Rg (alpha Rg)).inv_mem hx
  have back (v : Vertex Rg) : act Rg x⁻¹ (act Rg x v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  have hZ (v : Vertex Rg) : (Z Rg v).map f = Z Rg (act Rg x⁻¹ v) := by
    simpa only [inv_inv] using (Z_act Rg x⁻¹ v).symm
  have hQ (v : Vertex Rg) : (Q Rg v).map f = Q Rg (act Rg x⁻¹ v) := by
    simpa only [inv_inv] using (Q_act Rg x⁻¹ v).symm
  have hG : (stabilizer Rg (alpha Rg)).map f = stabilizer Rg (alpha Rg) := by
    simpa only [inv_inv,hya] using (stabilizer_act Rg x⁻¹ (alpha Rg)).symm
  have ht' : Adjacent Rg (alpha Rg) (act Rg x⁻¹ t) := by
    rw [←hya]
    exact (adjacent_act_iff Rg x⁻¹ _ _).mpr hat
  have hc' : Adjacent Rg (act Rg x⁻¹ c) (act Rg x⁻¹ t) :=
    (adjacent_act_iff Rg x⁻¹ _ _).mpr hct
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  have hJ : (edgeOffenderJoin (alpha Rg) t).map f =
      edgeOffenderJoin (alpha Rg) (act Rg x⁻¹ t) := by
    simpa only [inv_inv,hya] using
      (remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hat x⁻¹).symm
  have heq' : edgeOffenderJoin (alpha Rg) (act Rg x⁻¹ t) =
      edgeOffenderJoin (act Rg x⁻¹ c) (act Rg x⁻¹ t) := by
    have hh := congrArg (Subgroup.map f) heq
    rw [hJ] at hh
    have hjc : (edgeOffenderJoin c t).map f =
        edgeOffenderJoin (act Rg x⁻¹ c) (act Rg x⁻¹ t) := by
      simpa only [inv_inv] using
        (remaining_edge_join_act h e hz hk u (Or.inr hR) hcol hct x⁻¹).symm
    rwa [hjc] at hh
  have hxt : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hJ' : (edgeOffenderJoin (alpha Rg) (act Rg x t)).map f =
      edgeOffenderJoin (alpha Rg) t := by
    simpa only [inv_inv,hya,back] using
      (remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hxt x⁻¹).symm
  have hpair' : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x⁻¹ t) = stabilizer Rg (alpha Rg) := by
    have hh := congrArg (Subgroup.map f) hpair
    rw [Subgroup.map_sup,hJ,hJ',hG] at hh
    exact (sup_comm _ _).trans hh
  have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hbad₂ : Z Rg (act Rg x⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    have hh := map_mono (f := f) hbad'
    rwa [hZ,hQ,hlen,hqverts,back] at hh
  let A := Z Rg z ⊓ Q Rg (alpha Rg)
  let A' := Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)
  let H := ⁅A,Z Rg c⁆
  have hA' : A'.map f = A := by
    rw [Subgroup.map_inf _ _ _ hi,hZ,hQ,back,hya]
  have hcomm : (⁅A',Z Rg c⁆).map f = ⁅A,Z Rg (act Rg x⁻¹ c)⁆ := by
    rw [map_commutator,hA',hZ]
  have hne := borel_equal_strict_other_kernel_ne_bot h e hz hk u hR
    p q hp hq hat hct heq hgen hbad hbad' hstrict hescape
  have hne₂ : ⁅A,Z Rg (act Rg x⁻¹ c)⁆ ≠ ⊥ := by
    rw [←hcomm]
    intro hh
    apply hne
    exact (map_injective hi) (hh.trans (Subgroup.map_bot f).symm)
  obtain ⟨hcard,hfirst,hsecond⟩ := borel_equal_paired_kernel_line h e hz hk u hR p hp
    hat hct ht' hc' heq heq' hpair' hbad hbad₂ hescape
  rcases hsecond with hzero | ⟨hsecond,hcent⟩
  · exact (hne₂ hzero).elim
  have hHcent : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    hfirst.le.trans hcent
  have hHfixed : H.map f = H := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      have he := hHcent hv x hx
      change x*v*x⁻¹ ∈ H
      rw [he,mul_inv_cancel_right]
      exact hv
    · intro v hv
      refine ⟨v,hv,?_⟩
      have he := hHcent hv x hx
      change x*v*x⁻¹ = v
      rw [he,mul_inv_cancel_right]
  refine ⟨hfirst.symm ▸ hcard,hHcent,hHfixed,?_⟩
  apply map_injective hi
  rw [hcomm,hHfixed]
  exact hsecond.trans hfirst.symm
include h e hz hk in
/-- A trapped equal-mover selector at a strict slice controls its first
endpoint. The common fixed subgroup of the joint kernel is estimated on
the whole moving cover, without replacing a full seed by a hyperplane. -/
theorem borel_equal_strict_paired_endpoint_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z))
    (hqverts : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg))
    (hpair : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    :
    ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) := by
  by_contra hescape
  obtain ⟨hcard,hcentral,_,hother⟩ := borel_equal_strict_paired_kernel_line h e hz hk
    u hR p x hx q hqverts hp hq hat hct heq hgen hpair hbad hbad' hstrict hescape
  let A := Z Rg z ⊓ Q Rg (alpha Rg)
  let A' := Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)
  let H := ⁅A,Z Rg c⁆
  have hAG : A ≤ stabilizer Rg (alpha Rg) := inf_le_right.trans (fun _ hv => hv.1)
  have hA'G : A' ≤ stabilizer Rg (alpha Rg) := inf_le_right.trans (fun _ hv => hv.1)
  have hnormal : stabilizer Rg (alpha Rg) ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hjoint : ⁅A ⊔ A',Z Rg c⁆ ≤ H :=
    commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg)) A A'
      (Z Rg c) H hnormal hAG hA'G le_rfl hother.le
  have hHc : H ≤ Z Rg c := by
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      change false ≠ color Rg t at hh
      cases he : color Rg t <;> simp_all
    exact le_normalizer_iff_commutator_le_right.mp
      (((inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
        (fun _ hv => hv.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c))
  let := finite_Z Rg c
  let : Finite H := Finite.of_injective (inclusion hHc) (inclusion_injective _)
  have hmove : ⁅U Rg c,A ⊔ A'⁆ ≤ H := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg c)).trans hjoint
  have hbound := (card_le_of_le hmove).trans hcard.le
  have hlarge := borel_equal_paired_trapped_joint_movement_gt_two h e hz hk
    u hR p q hp hq hat hct heq hgen hbad hbad' hstrict
  exact (Nat.not_le_of_gt hlarge) hbound
include h e hz hk in
/-- The two actual equal-mover backward candidates cannot both be trapped
at a strict Baumann slice. The second endpoint is transported with the
inverse of the same selected element. -/
theorem borel_equal_strict_paired_not_trapped
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z))
    (hqverts : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg))
    (hpair : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    :
    False := by
  have hfirst := borel_equal_strict_paired_endpoint_control h e hz hk u hR
    p x hx q hqverts hp hq hat hct heq hgen hpair hbad hbad' hstrict
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hxi : x⁻¹ ∈ stabilizer Rg (alpha Rg) := (stabilizer Rg (alpha Rg)).inv_mem hx
  have hya : act Rg x⁻¹ (alpha Rg) = alpha Rg := hxi
  have back (v : Vertex Rg) : act Rg x⁻¹ (act Rg x v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  have hxt : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hpair' : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x⁻¹ t) = stabilizer Rg (alpha Rg) := by
    let f := (MulAut.conj x).toMonoidHom
    have hJ : (edgeOffenderJoin (alpha Rg) t).map f =
        edgeOffenderJoin (alpha Rg) (act Rg x⁻¹ t) := by
      simpa only [inv_inv,hya] using
        (remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hat x⁻¹).symm
    have hJ' : (edgeOffenderJoin (alpha Rg) (act Rg x t)).map f =
        edgeOffenderJoin (alpha Rg) t := by
      simpa only [inv_inv,hya,back] using
        (remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hxt x⁻¹).symm
    have hG : (stabilizer Rg (alpha Rg)).map f = stabilizer Rg (alpha Rg) := by
      simpa only [inv_inv,hya] using (stabilizer_act Rg x⁻¹ (alpha Rg)).symm
    have hh := congrArg (Subgroup.map f) hpair
    rw [Subgroup.map_sup,hJ,hJ',hG] at hh
    exact (sup_comm _ _).trans hh
  have hgen' : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg (act Rg x z)) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
    simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen
  have hsecond : ⁅Z Rg c,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) := by
    have hh := borel_equal_strict_paired_endpoint_control h e hz hk u hR (c := c) (t := t) q x⁻¹ hxi
    rw [back] at hh
    exact hh p (fun i => by rw [hqverts,back]) hq hp hat hct heq hgen'
      hpair' hbad' hbad hstrict
  have hb := distance_gt_two h e hz hk
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hfirst
  have hqY := hmove q hsecond
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    apply le_trans (remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hv => hv.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hv => hv.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  have hi := relIndex_eq_one.mpr hUB
  omega
include h e hz hk in
/-- Equal Borel movers give a compatible backward path at every strict
slice, including central generation. Every chosen overlap and the same
component transporter are retained. -/
theorem borel_equal_thompson_small_shift
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (heq : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) =
      edgeOffenderJoin delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,_,_,_,_,hnorm,hinside,_,g,hg,hgt,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  let c := act Rg g delta
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hxG
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hqs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hdcol : color Rg delta = false := by
    simpa only [c,action_preserves_color] using hc
  have heqc : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) heq
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hfirst g,
      ←remaining_edge_join_act h e hz hk u (Or.inr hR) hdcol hd g,hgt,
      show act Rg g (alpha Rg) = alpha Rg from hg] at hh
    exact hh
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧ ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  by_cases hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))
  · by_cases hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))
    · exact (borel_equal_strict_paired_not_trapped h e hz hk u hR
        p x hxG q hqverts hp hqs hat hct heqc hgen hpair hbad hbad' hstrict).elim
    · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
        hstrict,Or.inr (extend _ q hbad')⟩
  · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
      hstrict,Or.inl (extend _ p hbad)⟩

include h e hz hk in
/-- Every Borel mover comparison gives the same compatible strict-slice
backward shift, without a central-generation alternative. -/
theorem borel_strict_small_shift
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  by_cases heq : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) =
      edgeOffenderJoin delta (p.walk.getVert 1)
  · exact borel_equal_thompson_small_shift h e hz hk u hR p hp hd heq hs
  · exact borel_distinct_small_shift h e hz hk u hR p hp hd heq hs

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
