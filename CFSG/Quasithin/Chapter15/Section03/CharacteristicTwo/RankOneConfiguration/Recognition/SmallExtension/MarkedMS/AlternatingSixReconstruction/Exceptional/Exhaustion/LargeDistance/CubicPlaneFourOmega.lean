module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration

/-!
# Full omega generation in the cubic plane branch at distance four

Assume that every critical image is small. A strict slice supplies two
backward critical paths with different endpoints but the same midpoint.
The original selector also supplies an edge which generates with their
joined endpoint seeds. Transport the strict slice to this edge using the
actual graph action, and apply the paired-kernel comparison a second time.
Unless full omega is centrally generated, it would give distinct kernels
in the same midpoint core. This contradiction forces central generation
at every component vertex, and hence X_v = Z_v there.

A strict slice need not be supplied: if every slice were small, the existing
two-end-slice theorem would construct a strict reciprocal slice on the same
selected span. Thus distance four and uniformly small critical images suffice
for full omega generation. The first application retains the distinct switched
midpoints; only the midpoints of the resulting backward paths coincide.

The whole-core and literal C.1.32 applications preserve the original radical,
the cubic projection with kernel E rather than Q, and both full moving covers.
The centrally generated case, small-image proof, larger-distance and Borel
exclusions, and both core exhaustions remain necessary for reconstruction.
This result does not assert the unconditional terminal contradiction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the paired comparison in (5.12)(1),(3), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
private theorem shared_midpoint_strict_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z z' d t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (hmid : p.walk.getVert 2 = p'.walk.getVert 2)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen : (Q Rg t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    (∀ v : Vertex Rg, color Rg v = false →
  (X Rg v = U Rg v ⊔
    (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
  X Rg v = Z Rg v) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color Rg p.start_color
  have hback : act Rg g⁻¹ a = alpha Rg := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_paired_backward_configuration h e hz hk u hR hb4 hsmall
    (z := act Rg g⁻¹ z) (z' := act Rg g⁻¹ z')
    (d := act Rg g⁻¹ d) (t := act Rg g⁻¹ t)
  rw [←hback] at base
  have hgen' : (Q Rg (act Rg g⁻¹ t) ⊔ Z Rg (act Rg g⁻¹ z)) ⊔
      Z Rg (act Rg g⁻¹ z') = stabilizer Rg (act Rg g⁻¹ a) := by
    rw [Q_act,Z_act,Z_act,stabilizer_act,←Subgroup.map_sup,←Subgroup.map_sup,hgen]
  have hs' : 2 < (B Rg (act Rg g⁻¹ a) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg g⁻¹ d)) := by
    rw [Escape.PairingControl.FirstPairing.B_act
      (geometry := sourceGeometry h) (distance_gt_two h e hz hk) _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hs
  rcases base (p.act g⁻¹) (p'.act g⁻¹)
    ((adjacent_act_iff Rg g⁻¹ _ _).mpr hat)
    ((adjacent_act_iff Rg g⁻¹ _ _).mpr hdt) hgen' hs' with
      hc | ⟨q,q',_,_,_,_,hne,_⟩
  · exact hc
  · simp only [CriticalPath.act,actWalk_getVert,hmid] at hne
    exact (hne rfl).elim

include h e hz hk in
private theorem plane_selected_strict_slice_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    (∀ v : Vertex Rg, color Rg v = false →
  (X Rg v = U Rg v ⊔
    (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
  X Rg v = Z Rg v) := by
  rcases plane_small_critical_shifted_configuration h e hz hk u hR hb4 hsmall p hd hs
    with hc | ⟨t,hat,r,hr,p',hverts,hgen,hpair,hlarge,hnorm,hinside,g,hg,hgt,
      hstrict,q,q',hqt,hqt',hqv,hqv',hne,hindex,hlarge',s,hds,hpair',hgen'⟩
  · exact hc
  have hmid : q.walk.getVert 2 = q'.walk.getVert 2 := by
    calc
      q.walk.getVert 2 = alpha Rg := by simpa using hqv 0 (by omega)
      _ = q'.walk.getVert 2 := by simpa using (hqv' 0 (by omega)).symm
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨j,hj | hj⟩ := edge_transitive Rg hat₀ hds
  · have hdelta : Adjacent Rg (act Rg j delta) s := by
      rw [←hj.2]
      exact (adjacent_act_iff Rg j _ _).mpr hd
    have hstrict' : 2 < (B Rg (act Rg g delta) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg j delta)) := by
      rw [←hj.1,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) (distance_gt_two h e hz hk) _ _ rfl,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hs
    exact shared_midpoint_strict_omega h e hz hk u hR hb4 hsmall q q' hmid hds hdelta
      (by simpa only [sup_assoc] using hgen') hstrict'
  · have hsc : color Rg s = false := by
      rw [←hj.1,action_preserves_color]
      rfl
    exact ((adjacent_color_ne Rg hds) (q.start_color.trans hsc.symm)).elim

include h e hz hk in
/-- At distance four with small critical images, any strict plane slice
forces central generation of full omega at every component vertex. -/
theorem plane_strict_slice_omega_generated
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a d t : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    (∀ v : Vertex Rg, color Rg v = false →
  (X Rg v = U Rg v ⊔
    (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
  X Rg v = Z Rg v) := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := Rg) (geometry := sourceGeometry h)
    (a := alpha Rg) rfl
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨j,hj | hj⟩ := edge_transitive Rg hat hat₀
  · have hdelta : Adjacent Rg (act Rg j d) (p.walk.getVert 1) := by
      rw [←hj.2]
      exact (adjacent_act_iff Rg j _ _).mpr hdt
    have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg j d)) := by
      rw [←hj.1,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) (distance_gt_two h e hz hk) _ _ ha,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hs
    exact plane_selected_strict_slice_omega h e hz hk u hR hb4 hsmall p hdelta hstrict
  · have htc : color Rg (p.walk.getVert 1) = false := by
      rw [←hj.1,action_preserves_color]
      exact ha
    exact ((adjacent_color_ne Rg hat₀) htc.symm).elim

include h e hz hk in
/-- The plane branch at distance four with uniformly small critical images
has centrally generated full omega. The proof constructs its own strict slice
using the terminal two-slice theorem if no strict slice was supplied. -/
theorem plane_small_four_omega_generated
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    (∀ v : Vertex Rg, color Rg v = false →
  (X Rg v = U Rg v ⊔
    (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
  X Rg v = Z Rg v) := by
  by_contra hn
  have hslice {a d t : Vertex Rg} (ha : color Rg a = false)
      (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t) :
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    by_contra! hs
    exact hn (plane_strict_slice_omega_generated h e hz hk u hR hb4 hsmall ha hat hdt hs)
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := Rg) (geometry := sourceGeometry h)
    (a := alpha Rg) rfl
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hcs : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzs : Adjacent Rg z (p.walk.getVert 3) := by
    apply adjacent_symm Rg
    apply (cosetGraph_adj Rg _ _).mp
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    simpa only [show 3+1=p.walk.length by omega,SimpleGraph.Walk.getVert_length] using hh
  have hterminal := plane_four_selected_configuration_of_slices h e hz hk u hR hb4 p
    (hslice rfl hat hct) (hslice hc hcs hzs)
  exact (Nat.not_lt_of_ge (hslice hc hct hat)) hterminal.2.2.2.1

omit hk in
include h e hz in
/-- Whole-core application eliminates the noncentral omega extension in the
plane branch at distance four with small critical images. The original cubic
projection and both full moving covers are retained. -/
theorem coreExhaustion_or_cubic_plane_four_omega :
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
          ∀ v : Vertex Rg, color Rg v = false →
            (X Rg v = U Rg v ⊔
              (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
            X Rg v = Z Rg v)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_omega_generated h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of plane full-omega generation. Distance four
and small critical images remain source premises; core exhaustion remains open. -/
theorem rankTwo_or_cubic_plane_four_omega :
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
          ∀ v : Vertex Rg, color Rg v = false →
            (X Rg v = U Rg v ⊔
              (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
            X Rg v = Z Rg v)) :=
  (coreExhaustion_or_cubic_plane_four_omega h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
