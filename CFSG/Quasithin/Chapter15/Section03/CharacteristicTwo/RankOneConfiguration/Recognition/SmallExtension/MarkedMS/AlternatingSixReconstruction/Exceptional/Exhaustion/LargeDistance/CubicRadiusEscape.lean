module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPredecessorSlice

/-!
# Radius escape and backward critical paths in the full point-core branch

Failure of radius escape gives a uniform bound of two on every two-edge
Baumann slice. The predecessor-slice theorem now identifies the full
reverse kernel with its predecessor slice, discharging the premise of
the actual residual-shift construction. That construction has image order
at least four, whereas the same uniform slice bound forces its image
order to be two. This excludes radius failure.

The same original cubic marking transports escape to every component
vertex. An escaping radius seed then gives an actual backward critical
walk with every overlap vertex retained. The whole-core and literal
C.1.32 applications also include the strict reciprocal slices for a large
critical image. Both full covers and the odd quotient E/Q remain intact.

Point-core equality is still a hypothesis on the literal radical image.
The other edge-image choices, small-image strict slices, R4/R6 and
MS93 (5.11)--(5.12) remain with this reconstruction task. Independent
natural exhaustion and final assembly of both outcomes remain necessary.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed pp.919--920.
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
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- Uniform small two-edge slices place the full reverse critical kernel
in its predecessor slice on every actual critical path. -/
private theorem predecessor_small_slice_of_uniform
    (hb : 2 < sourceDistance h)
    (hall : ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t → Adjacent Rg c t →
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    Z Rg a' ⊓ Q Rg a ≤ B Rg (p.walk.getVert (p.walk.length-2))
        ((sourceGeometry h).Z_normal _) ∧
      (Q Rg a').relIndex (Z Rg a) = 2 := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hat : Adjacent Rg a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hct : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hs := critical_predecessor_small_slice h e hz hk hb p (hall _ _ _ hc hct hat)
  exact ⟨hs.1 ▸ inf_le_right,hs.2.2⟩

include h e hz hk in
/-- Radius failure in the full point-core branch supplies the predecessor
slice required by the residual shift, for the whole reverse kernel. -/
theorem radius_failure_predecessor_slice
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    Z Rg a' ⊓ Q Rg (alpha Rg) ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) := by
  have hall := (radius_failure_backward_slices h e hz hk hb u hfull p hbad).1
  exact (predecessor_small_slice_of_uniform h e hz hk hb hall p).1

include h e hz hk in
/-- The full point-core branch has radius escape. Assuming failure makes
every two-edge slice small, while the actual residual shift constructs a
critical path whose image has order at least four. Its own predecessor
slice then forces that same image to have order two. -/
theorem full_point_critical_radius_escape
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  have hall := (radius_failure_backward_slices h e hz hk hb u hfull p hbad).1
  have hs := (predecessor_small_slice_of_uniform h e hz hk hb hall p).1
  have hslice : U Rg a' ⊓ Q Rg (alpha Rg) ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) :=
    (inf_le_inf_right _ (DistanceEight.U_le_Z Rg a')).trans hs
  obtain ⟨t,c,k,hat,hct,hkm,hkt,q,hlarge,_⟩ :=
    radius_failure_residual_critical_shift h e hz hk hb u hfull p hbad hslice
  have hsmall := (predecessor_small_slice_of_uniform h e hz hk hb hall q).2
  omega

include h e hz hk in
/-- Radius escape transports to every component vertex using the same
original cubic marking and the actual transformed walk. -/
theorem full_point_critical_radius_escape_at
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ a'),
      (∀ n, p₀.walk.getVert n = act Rg g⁻¹ (p.walk.getVert n)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act g⁻¹,fun n => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg g⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert,hlen⟩ := hpact
  have he := full_point_critical_radius_escape h e hz hk hb u hfull p₀
  rw [hlen,hvert,←hbase,V_act,Q_act] at he
  exact fun hn => he (map_mono hn)

include h e hz hk in
/-- Every critical walk in the full point-core branch has a backward
critical shift with its entire overlap fixed. The new starting vertex is
chosen from the actual radius, without assuming a slice placement. -/
theorem full_point_backward_critical_path
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have he := full_point_critical_radius_escape_at h e hz hk hb u hfull p
  have hd : (cosetGraph Rg).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (sourceGeometry h).b Rg := by
    rw [p.dist_start (Nat.sub_le _ _),←p.length_eq_b]
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    omega
  obtain ⟨d,hdc,hda,hn⟩ := exists_critical_shift Rg p.start_color hd he
  obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist d a
  have hw2 : w.length = 2 := hw.trans hda
  have hb2 : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  exact ⟨d,w,p.prepend_two hb2 hdc w hw2 hn.2,hw2,rfl,
    fun _ hi => p.prepend_two_overlap hb2 hdc w hw2 hn.2 hi⟩

omit hk in
include h e hz in
/-- Whole-core application of the full-point radius escape, retaining the
original cubic projection and both full central covers. -/
theorem coreExhaustion_or_cubic_full_point_radius_escape :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
      (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
        4 ≤ (Q Rg a').relIndex (Z Rg a) →
        2 < (B Rg (p.walk.getVert (p.walk.length-2))
          ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ∧
        2 < (B Rg (p.walk.getVert 2)
          ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun u hfull _ _ p => full_point_critical_radius_escape_at h e hz hk hb u hfull p,
      fun _ _ p hlarge => large_critical_slices_gt_two h e hz hk hb p hlarge⟩

omit hk in
include h e hz in
/-- The literal C.1.32 consumer uses radius escape without a
predecessor-slice premise. Other radical-image cases and terminal
exhaustion remain separate mathematical obligations. -/
theorem rankTwo_or_cubic_full_point_radius_escape :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
      (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
        4 ≤ (Q Rg a').relIndex (Z Rg a) →
        2 < (B Rg (p.walk.getVert (p.walk.length-2))
          ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ∧
        2 < (B Rg (p.walk.getVert 2)
          ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) :=
  (coreExhaustion_or_cubic_full_point_radius_escape h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
