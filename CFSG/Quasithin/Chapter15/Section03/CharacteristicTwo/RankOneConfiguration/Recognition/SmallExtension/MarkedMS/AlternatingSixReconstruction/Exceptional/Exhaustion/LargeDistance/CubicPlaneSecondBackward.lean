module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneTripleControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedKernelSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusLine

/-!
# The same second backward kernel under both cubic endpoint actors

Two critical paths with common starting vertex and midpoint retain their
actual transporters and central triple intersections. Transport the strict
slice to a second backward neighbor along an edge generating with the old
edge. The two strict edge-seed intersections give the second central triple.
The preceding comparison then controls one full second backward kernel under
both endpoint seeds. Their joint generation makes its join with the starting
seed invariant, so the original normal-radius theorem puts it in the Baumann
subgroup. Its actual raw critical index is at most two, contradicting the
transported strict slice.

No extra criticality of the second backward candidate is assumed. Both full
moving covers and the original cubic extension kernel E are retained.

Source: MS93 (5.12)(1),(3), printed pp.924--927.
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


include h e hz hk in
/-- Both retained endpoint actors control the same second backward kernel. -/
theorem plane_paired_second_backward_strict_false
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a c v w t t' : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c v)
    (r : CriticalPath Rg (sourceGeometry h) c w)
    (hq2 : q.walk.getVert 2 = a) (hr2 : r.walk.getVert 2 = a)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hct' : Adjacent Rg c t')
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c))
    (hfirst : Q Rg t ⊔ Q Rg t' = stabilizer Rg c)
    (hactors : Q Rg t' ⊔ Z Rg v ⊔ Z Rg w = stabilizer Rg c)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgv : act Rg g v = c)
    (k : FreeAmalgam Rg) (hkG : k ∈ stabilizer Rg a)
    (hkw : act Rg k w = c)
    (htripleV : Z Rg c ⊓ Z Rg a ⊓ Z Rg v ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))
    (htripleW : Z Rg c ⊓ Z Rg a ⊓ Z Rg w ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) : False := by
  have hb2 : 2 < sourceDistance h := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color Rg a = false := by
    rw [←hq2]
    exact (q.vertex_color (by omega)).mpr (by decide)
  obtain ⟨j,hj,hja⟩ := stabilizer_transitive_neighbors Rg t
    (adjacent_symm Rg hat) (adjacent_symm Rg hct)
  have hjt : act Rg j t = t := hj
  have hdelta : Adjacent Rg (act Rg j c) t := by
    simpa only [hjt] using (adjacent_act_iff Rg j _ _).mpr hct
  have hdeltaStrict : 2 < (B Rg c ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg j c)) := by
    have hi : 2 < (B Rg (act Rg j a)
        ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg j c)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j a ha,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hstrict
    simpa only [hja] using hi
  obtain ⟨l,hl,hlt⟩ := stabilizer_transitive_neighbors Rg c hct hct'
  let b := act Rg l (act Rg j c)
  have hbt' : Adjacent Rg b t' := by
    rw [←hlt]
    exact (adjacent_act_iff Rg l _ _).mpr hdelta
  have hbcol : color Rg b = false := by
    simpa only [b,action_preserves_color] using q.start_color
  have hbstrict : 2 < (B Rg c ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg b) := by
    have hBl := Escape.PairingControl.FirstPairing.B_act
      (geometry := sourceGeometry h) hb2 l c q.start_color
    rw [show act Rg l c = c from hl] at hBl
    change 2 < (B Rg c _).relIndex (U Rg (act Rg l _))
    rw [hBl,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hdeltaStrict
  have hbc : (cosetGraph Rg).dist b c ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hbt')
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hct'))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
      (u := b) (v := t') (w := c)
  have hAc : Z Rg a ⊓ Z Rg c = Z Rg t := by
    rw [inf_comm]
    exact (plane_strict_slice_eq_edge h e hz hk u hR ha q.start_color hat hct hstrict).2.1
  have hBc : Z Rg c ⊓ Z Rg b = Z Rg t' := by
    rw [inf_comm]
    exact (plane_strict_slice_eq_edge h e hz hk u hR q.start_color hbcol hct' hbt' hbstrict).2.1
  have hedgeCent {t₀ : Vertex Rg} (hc₀ : Adjacent Rg c t₀) :
      Z Rg t₀ ≤ centralizer (Q Rg t₀ : Set (FreeAmalgam Rg)) := by
    have ht₀ : color Rg t₀ = true := by
      have hh := adjacent_color_ne Rg hc₀
      rw [q.start_color] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    intro x hx
    rw [Z,if_neg (by simp [ht₀])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have htripleB : Z Rg b ⊓ Z Rg c ⊓ Z Rg a ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hfirst]
    apply sup_le
    · apply le_centralizer_iff.mp
      exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans
        (hAc.le.trans (hedgeCent hct))
    · apply le_centralizer_iff.mp
      exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
        (hBc.le.trans (hedgeCent hct'))
  have hvcontrol := plane_two_central_triples_kernel_control h e hz hk u hR hb
    q hq2 (hsmall _ _ q) hbc hbcol g hg hgv htripleV htripleB
  have hwcontrol := plane_two_central_triples_kernel_control h e hz hk u hR hb
    r hr2 (hsmall _ _ r) hbc hbcol k hkG hkw htripleW htripleB
  let K := Z Rg b ⊓ Q Rg a
  let N := K ⊔ Z Rg c
  have hraw := raw_preceding_kernel_normalized h e hz hk u hR hb hsmall q hct' hbt'
  rw [hq2] at hraw
  have hcore : Q Rg t' ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hraw.1
      ((show Q Rg t' ≤ stabilizer Rg c from
        fun _ hx => hx.2 _ (adjacent_symm Rg hct')).trans (Z_normalized Rg c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hactors]
    exact sup_le (sup_le hcore hvcontrol.2.2) hwcontrol.2.2
  have hKV : K ≤ V Rg c := inf_le_left.trans
    (le_iSup_of_le b (le_iSup_of_le hbc le_rfl))
  have hNV : N ≤ V Rg c := sup_le hKV (Z_le_VBall Rg _ 2)
  have hNG : N ≤ stabilizer Rg c := hNV.trans
    ((sourceGeometry h).V_local c q.start_color (by
      rw [(sourceGeometry h).distance_constant _ q.start_color]
      exact hb2))
  have hmove : ⁅N,Z Rg v⁆ ≤ Z Rg c := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg c)
      K (Z Rg c) (Z Rg v) (Z Rg c) (Z_normalized Rg c)
      (le_sup_left.trans hNG) (Z_le_stabilizer Rg c)
    · exact hvcontrol.2.1.trans (critical_seed_commutator_le h q)
    · exact critical_seed_commutator_le h q
  have hKB : K ≤ B Rg c ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (shifted_normalized_radius_le_slice
      h e hz hb2 q N hNV hNn hmove)
  let := finite_Z Rg b
  let : Finite (U Rg b) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg b)) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hKB
    (index_ne_zero_of_finite (H := K.subgroupOf (Z Rg b)))
  change (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg b) ≤
    (Z Rg b ⊓ Q Rg a).relIndex (Z Rg b) at hi
  rw [inf_relIndex_left] at hi
  have hUi := ((relIndex_le_of_le_right (DistanceEight.U_le_Z Rg b)
    index_ne_zero_of_finite).trans hi).trans hraw.2
  exact (Nat.not_le_of_gt hbstrict) hUi

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
