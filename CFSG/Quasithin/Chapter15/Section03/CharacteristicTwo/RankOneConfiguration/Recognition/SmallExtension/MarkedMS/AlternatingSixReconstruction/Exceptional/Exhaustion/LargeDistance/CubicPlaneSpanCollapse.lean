module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullSeed
public import Theory.GroupTheory.ConjugateSpanNilpotent

/-!
# Whole-stabilizer section control on the original cubic graph

The image of a small critical seed is a transposition. A normal section fixed
by the original two-core and that seed is therefore fixed by the entire local
stabilizer: its action kernel has full symmetric image. The no-supplement
property then lifts this equality through the actual cubic kernel E, retaining
its odd E/Q of order three.

This supplies the nilpotent displacement bound that collapses an invariant
centralizer orbit of a nearby local span. The statement uses the same original
critical path, whole seeds and original graph. It does not assume or assert
that the cubic projection kernel equals the two-core. The source comparison
and orbit invariance remain explicit inputs to this algebraic step; strict
forward slices and the terminal distance exclusions are not claimed here.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.9), printed
pp.866--867,920--922. Adapts the normal-section argument of natural
CubeSpanCollapse using the original cubic no-supplement theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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

private theorem section_control_of_swap
    (D N A : Subgroup M) [D.Normal] [N.Normal]
    (hQ : ⁅D,pCore 2 M⁆ ≤ N) (hA : ⁅D,A⁆ ≤ N)
    (hswap : ∃ t ∈ A.map π, t.IsSwap) :
    ⁅D,⊤⁆ ≤ N := by
  let C := commutatorPreimage ⊤ D N
  have hCN : (⊤ : Subgroup M) ≤ normalizer (C : Set M) :=
    commutatorPreimage_normalized ⊤ D N ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
  let : C.Normal := ⟨by
    intro x hx g
    exact (mem_normalizer_iff.mp (hCN (mem_top g)) x).mp hx⟩
  have hQC : pCore 2 M ≤ C :=
    le_commutatorPreimage le_top (by rwa [commutator_comm])
  have hAC : A ≤ C := le_commutatorPreimage le_top (by rwa [commutator_comm])
  let : (C.map π).Normal := Subgroup.Normal.map inferInstance _ (CubicEven.projection_surjective h e hz hk)
  obtain ⟨t,ht,hs⟩ := hswap
  have htC : t ∈ C.map π := map_mono hAC ht
  have htop : C.map π = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.closure_isSwap]
    apply (closure_le _).mpr
    rintro v hv
    obtain ⟨a,b,hab,rfl⟩ := hs
    obtain ⟨c,e,hce,rfl⟩ := hv
    obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hce)
    exact hg ▸ Subgroup.Normal.conj_mem inferInstance _ htC g
  have hC : C = ⊤ := by
    have hCE : C ⊔ extensionKernel h = ⊤ := by
      have he := congrArg (Subgroup.comap π) htop
      rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
    have hEC : extensionKernel h ≤ C := by
      have he := extensionKernel_no_supplement h C (hCE ▸ le_top)
      rwa [extensionKernel_twoCore h,sup_of_le_left hQC] at he
    rwa [sup_of_le_left hEC] at hCE
  rw [commutator_comm,←hC]
  exact commutator_commutatorPreimage_le ⊤ D N le_normalizer_of_normal

include h e hz hk in
private theorem cubic_small_critical_section_control_base
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (W N : Subgroup (FreeAmalgam Rg))
    (hWG : W ≤ stabilizer Rg (alpha Rg))
    (hWN : stabilizer Rg (alpha Rg) ≤ normalizer (W : Set (FreeAmalgam Rg)))
    (hNN : stabilizer Rg (alpha Rg) ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hQ : ⁅W,Q Rg (alpha Rg)⁆ ≤ N)
    (hA : ⁅W,Z Rg z⁆ ≤ N) :
    ⁅W,stabilizer Rg (alpha Rg)⁆ ≤ N := by
  let W₀ := W.comap (embedM Rg)
  let N₀ := N.comap (embedM Rg)
  let A := (Z Rg z).comap (embedM Rg)
  have hWm : W₀.map (embedM Rg) = W :=
    map_comap_eq_self (hWG.trans_eq (stabilizer_m_base Rg))
  have hAm : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg)
      rfl (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hg (m : M) : embedM Rg m ∈ stabilizer Rg (alpha Rg) := by
    change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : W₀.Normal := ⟨by
    intro w hw m
    change embedM Rg (m*w*m⁻¹) ∈ W
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hWN (hg m)) _).mp hw⟩
  let : N₀.Normal := ⟨by
    intro n hn m
    change embedM Rg (m*n*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNN (hg m)) _).mp hn⟩
  have hQ₀ : ⁅W₀,pCore 2 M⁆ ≤ N₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hWm,
      ←Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)]
    exact hQ
  have hA₀ : ⁅W₀,A⁆ ≤ N₀ := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator,hWm,hAm]
  obtain ⟨t,ht,him⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hswap : ∃ t ∈ A.map π, t.IsSwap := ⟨t,him ▸ mem_zpowers t,ht⟩
  have hh := map_mono (f := embedM Rg)
    (section_control_of_swap h e hz hk W₀ N₀ A hQ₀ hA₀ hswap)
  rw [map_commutator,hWm,←MonoidHom.range_eq_map] at hh
  have hstab : stabilizer Rg (alpha Rg) = (embedM Rg).range :=
    stabilizer_m_base Rg
  rw [←hstab] at hh
  exact hh.trans (map_comap_le _ _)

include h e hz hk in
/-- The full critical transposition controls every local displacement on a
normal section already fixed by the two-core. This retains the full S₆ actor. -/
theorem cubic_small_critical_section_control
    {c z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) c z)
    (hsmall : (Q Rg z).relIndex (Z Rg c) < 4)
    (W N : Subgroup (FreeAmalgam Rg))
    (hWG : W ≤ stabilizer Rg c)
    (hWN : stabilizer Rg c ≤ normalizer (W : Set (FreeAmalgam Rg)))
    (hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hQ : ⁅W,Q Rg c⁆ ≤ N) (hA : ⁅W,Z Rg z⁆ ≤ N) :
    ⁅W,stabilizer Rg c⁆ ≤ N := by
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ c = alpha Rg := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj g).toMonoidHom
  have base := cubic_small_critical_section_control_base h e hz hk
    (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  have hh := base (p.act g⁻¹)
    (by simpa only [Q_act,Z_act,inv_inv,relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _ (MulAut.conj g).injective] using hsmall)
    (W.map f) (N.map f)
    (by simpa only [stabilizer_act,inv_inv] using map_mono (f := f) hWG)
    (by rw [stabilizer_act,inv_inv]; exact (map_mono hWN).trans (W.le_normalizer_map f))
    (by rw [stabilizer_act,inv_inv]; exact (map_mono hNN).trans (N.le_normalizer_map f))
    (by simpa only [Q_act,inv_inv,f,map_commutator] using map_mono (f := f) hQ)
    (by simpa only [Z_act,inv_inv,f,map_commutator] using map_mono (f := f) hA)
  rw [stabilizer_act,inv_inv,←map_commutator] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh

include h e hz hk in
/-- In the actual small critical branch, the endpoint comparison collapses
an escaping local span's centralizer orbit once that orbit is invariant. -/
theorem cubic_small_critical_span_collapse
    (hb : 4 < sourceDistance h)
    {c z a : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) c z)
    (hsmall : (Q Rg z).relIndex (Z Rg c) < 4)
    (ha : color Rg a = false) (hca : (cosetGraph Rg).dist c a ≤ 2)
    (Y P : Subgroup (FreeAmalgam Rg))
    (hYV : Y ≤ V Rg a)
    (hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hZY : Z Rg c ≤ Y) (hPG : P ≤ stabilizer Rg c)
    (hWN : stabilizer Rg c ≤ normalizer (conjugateSpanBy Y P : Set (FreeAmalgam Rg)))
    (hcontrol : ⁅conjugateSpanBy Y P,Z Rg z⁆ ≤
      ⁅conjugateSpanBy Y P,Z Rg z ⊓ Q Rg c⁆ ⊔ ⁅Z Rg c,Z Rg z⁆) :
    conjugateSpanBy Y P = Y := by
  let W := conjugateSpanBy Y P
  let N := ⁅W,Q Rg c⁆ ⊔ Z Rg c
  have hYQ : Y ≤ Q Rg c := hYV.trans
    (V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) ha (by
      change (cosetGraph Rg).dist a c + 2 < sourceDistance h
      rw [SimpleGraph.dist_comm]
      omega))
  have hWQ : W ≤ Q Rg c := conjugateSpanBy_le hYQ (hPG.trans (Q_normalized Rg c))
  have hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [N]
    rw [Subgroup.map_sup,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hWN hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c hg)]
  have hcrit : ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg c := by
    apply le_normalizer_iff_commutator_le_left.mp
    exact (critical_Z_le_stabilizer Rg (sourceGeometry h) c p.start_color
      (by rw [(sourceGeometry h).distance_constant c p.start_color]
          exact sourceDistance_pos h) p.critical).trans (Z_normalized Rg c)
  have hcomm : ⁅W,stabilizer Rg c⁆ ≤ N :=
    cubic_small_critical_section_control h e hz hk p hsmall W N
      (hWQ.trans (fun _ hx => hx.1)) hWN hNN le_sup_left
      (hcontrol.trans (sup_le_sup (commutator_mono le_rfl inf_le_right) hcrit))
  let := finite_stabilizer Rg c
  let : Finite (Q Rg c) := Finite.of_injective
    (inclusion (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1))
    (inclusion_injective _)
  exact conjugateSpanBy_eq_of_nilpotent_commutator_bound Y P (Q Rg c) (Z Rg c)
    (Q_isPGroup Rg h.relative_radical.isPGroup
      h.relative_radical.twoCore_le c p.start_color).isNilpotent hWQ
    ((Q_le_stabilizer_of_dist_le_two c a p.start_color ha hca).trans hYN) hZY
    ((commutator_mono le_rfl hPG).trans hcomm)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
