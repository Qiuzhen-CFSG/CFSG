module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAugmentationLines

/-!
# A common attachment plane on the original cubic critical paths

Retain the strict path a--z, its generating backward path d--c, and the
actual element of G_a carrying the midpoint c to d. Write
H = [U_d intersect Q_c, X_z intersect Q_a] and D = [Z_d,Z_c].
The reverse-path augmentation comparison gives H intersect D = 1 and
H join D = D join C_d, where C_d = C_{U_d}(G_d). The generating edge makes
both H and D central in G_a, so C_d is central there too. Transport by the
retained element now proves C_d = C_c. Thus H join D is a central four-group
in G_a contained in both full moving covers U_d and U_c.

This comparison uses the same shifted kernel and literal graph actions.
The whole-core and C.1.32 consumers retain its noncentrality at d and z,
the moving attachment at z, the full midpoint core/radius gaps, and the
original augmentation marking. The cubic projection kernel remains E,
including the nontrivial odd E/Q, and the other radical images retain
both cover sizes. The new central four-group does not by itself give the
full-X control or the terminal contradiction, which remain source duties.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the shifted commutator and attachment comparison in (5.12)(1),
printed pp.924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
/-- The backward endpoint attachment is central at the original midpoint.
Both commutator lines used here belong to the same selected configuration. -/
theorem point_generating_backward_attachment_central
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hne : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥) :
    let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
    let D := ⁅Z Rg d,Z Rg c⁆
    let C := U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))
    H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧
      H ⊔ D ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        c q.end_color q.critical⟩
  have hqr : qr.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = alpha Rg
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hqa
  have hH := (point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa).2.2.1.resolve_left hne
  have hplane := point_critical_midpoint_attachment_plane h e hz hk u hR qr
  dsimp only at hplane ⊢
  rw [hqr,←hH,commutator_comm (Z Rg c) (Z Rg d)] at hplane
  have hD := selected_critical_commutator_central h e hz hk u hR q p
    (by rw [←hqa,q.dist_start (by omega)])
    (by rw [←hpc,SimpleGraph.dist_comm,p.dist_start (by omega)])
    (by rw [←hpc,p.dist_end,hl,hb]; decide) hgen
  have hHC := (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.1
  have hsum := sup_le hHC hD
  exact ⟨hplane.1,hplane.2.1,hsum,le_sup_right.trans (hplane.2.1.symm.le.trans hsum)⟩

include h e hz hk in
/-- With the original midpoint conjugator retained, the two backward
attachments coincide. The shifted line and backward critical line span a
central four-group contained in both full moving covers. -/
theorem point_generating_conjugate_common_plane
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (hxc : act Rg x c = d)
    (hne : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥) :
    let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
    let D := ⁅Z Rg d,Z Rg c⁆
    let C := fun v => U Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))
    C d = C c ∧
      H ⊔ D = D ⊔ C c ∧ Nat.card (H ⊔ D : Subgroup (FreeAmalgam Rg)) = 4 ∧
      H ⊔ D ≤ U Rg d ⊓ U Rg c ⊓
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
  let D := ⁅Z Rg d,Z Rg c⁆
  let C := fun v => U Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))
  obtain ⟨hdis,heq,hcent,hCd⟩ := point_generating_backward_attachment_central h e hz hk u hR p q hpc hqa hgen hne
  have hmap : C d = (C c).map (MulAut.conj x⁻¹).toMonoidHom := by
    dsimp only [C]
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj x⁻¹).injective,
      ←U_act,←stabilizer_act,hxc]
  have hfixed : (C d).map (MulAut.conj x).toMonoidHom = C d :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hCd hx))
  have hsame : C d = C c := by
    rw [hmap,map_map] at hfixed
    have hi : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
        MonoidHom.id (FreeAmalgam Rg) := by
      apply MonoidHom.ext
      intro y
      change x*(x⁻¹*y*(x⁻¹)⁻¹)*x⁻¹ = y
      group
    rw [hi,Subgroup.map_id] at hfixed
    exact hmap.trans hfixed.symm
  have hDc : D ≤ U Rg c := by
    let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        c q.end_color q.critical)
    have hs : (Q Rg d).relIndex (Z Rg c) < 4 := by
      rw [(point_image_critical_indices_two h e hz hk u hR q).2.1]
      decide
    change ⁅Z Rg d,Z Rg c⁆ ≤ U Rg c
    rw [commutator_comm,←small_critical_moving_commutator_eq h e hz hk qr hs]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) c q.end_color (by
        rw [(sourceGeometry h).distance_constant _ q.end_color]
        exact sourceDistance_pos h) qr.critical).trans (U_normalized c))
  have hDd : D ≤ U Rg d := by
    have hs : (Q Rg c).relIndex (Z Rg d) < 4 := by
      rw [(point_image_critical_indices_two h e hz hk u hR q).1]
      decide
    change ⁅Z Rg d,Z Rg c⁆ ≤ U Rg d
    rw [←small_critical_moving_commutator_eq h e hz hk q hs]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) d q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) q.critical).trans (U_normalized d))
  have hHd : H ≤ U Rg d :=
    (point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa).2.2.2.1.trans inf_le_left
  have hHGa : H ≤ stabilizer Rg (alpha Rg) :=
    (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.2.trans
      (Z_le_stabilizer Rg (alpha Rg))
  have hDN : D ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    ((le_sup_right.trans hcent).trans (centralizer_le hHGa)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hHcard : Nat.card H = 2 := by
    have hh := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
    dsimp only [H]
    rw [hh.2.2.1.resolve_left hne]
    exact hh.1
  have hDcard : Nat.card D = 2 := (point_image_critical_indices_two h e hz hk u hR q).2.2
  have hcard : Nat.card (H ⊔ D : Subgroup (FreeAmalgam Rg)) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint H D hDN (disjoint_iff.mpr hdis),hHcard,hDcard]
  refine ⟨hsame,heq.trans (congrArg (fun K => D ⊔ K) hsame),hcard,le_inf (le_inf (sup_le hHd hDd) ?_) hcent⟩
  rw [heq]
  change D ⊔ C d ≤ U Rg c
  rw [hsame]
  exact sup_le hDc inf_le_left

omit hk in
include h e hz in
/-- Whole-core application retaining the actual conjugator and the central four-group in both backward moving covers. -/
theorem coreExhaustion_or_cubic_common_attachment :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg) ∧
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C₀ := U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
              (U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))) = C₀ ∧
              H ⊔ D₀ = D₀ ⊔ C₀ ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_augmentation_lines h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · rcases hpoint with ⟨hpoint,hb4,hmodel,hsize,hX,hplanes,z,p,hstrict,_⟩
    obtain ⟨d,t,x,hx,hxd,hat,hdt,hgen,q,hq1,hover⟩ :=
      full_point_backward_step_of_strict_forward h e hz hk u hpoint p hstrict
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
    have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by rwa [hq1]
    have hlarge : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
      have hBmap : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
          (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          (geometry := sourceGeometry h) hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
      rw [←hxd,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
      exact hstrict
    obtain ⟨hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove⟩ :=
      point_strict_shifted_attachment h e hz hk u hpoint.le p q hpc hqa hgen' hlarge
    have hne : ⁅U Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),
        X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    have hcommon := point_generating_conjugate_common_plane h e hz hk u hpoint.le
      p q hpc hqa hgen' x hx (by rwa [←hpc]) hne
    have hdnon := point_shifted_kernel_noncentral_at_backward_endpoint h e hz hk u
      hpoint.le p q hpc hqa hne
    have hpb := point_critical_midpoint_core_bounds h e hz hk u hpoint.le p
    have hqb := point_critical_midpoint_core_bounds h e hz hk u hpoint.le q
    dsimp only at hpb hqb
    rw [hpc] at hpb
    rw [hqa] at hqb
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hmodel,hsize,hX,hplanes,
      z,p,hstrict,d,q,x,hx,hxd,hqa,hgen',hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove,
      hdnon,hpb.2.1,hqb.1,hpb.2.2.2.1,hqb.2.2.1,hpb.2.2.2.2.2,hqb.2.2.2.2.1,hcommon⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the common attachment and the same nonzero shifted line. -/
theorem rankTwo_or_cubic_common_attachment :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg) ∧
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C₀ := U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
              (U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))) = C₀ ∧
              H ⊔ D₀ = D₀ ⊔ C₀ ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_common_attachment h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
