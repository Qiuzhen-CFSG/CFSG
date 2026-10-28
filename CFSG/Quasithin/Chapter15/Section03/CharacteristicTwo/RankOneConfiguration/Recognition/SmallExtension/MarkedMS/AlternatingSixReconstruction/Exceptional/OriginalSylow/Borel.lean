module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes

/-!
# Critical generation and Thompson comparison for original Borel edges

A conjugate point core inside the Borel generates the symmetric quotient
with any prescribed critical transposition. The existing even-actor theorem
covers large critical images. Lifting these generators through the literal
cubic kernel, using its no-supplement property, produces an incident edge
that generates the full local stabilizer with the opposite critical seed.
For small critical images, this edge supplies an actual element moving
both the entire critical kernel and its line along the same critical path.

The full Borel edge is nonquadratic on both permitted moving covers:
quadraticity would descend to a conjugate point core, contradicting its
proved quadratic bound. Distinct quadratic Thompson choices across one
edge generate that edge and meet in index four. Maximality of the actual
small-mover family also forces cross-fixed indices greater than four.
These supply the distinct-choice premise in MS93 (5.5).

The source shifted-path estimates and the distance-four and larger-distance
contradictions remain necessary. In particular the selected small path is
not asserted to have distance four, and its full critical kernel is not
replaced by its moving part. The kernel remains E, with |E/Q| = 3.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; Meierfrankenfeld--
Stellmacher, Pushing up weak BN-pairs of rank two (1993), (5.4)--(5.8),
pp.915--920. The point-core and edge-chart calculations are reused from
the cited project modules; no new finite Borel enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull

private theorem borel_conjugate_generates_swap (u a : S) (ha : a.IsSwap) :
    ∃ k : alternatingGroup (Fin 6),
      (borel.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom ⊔
        zpowers a = ⊤ := by
  let c := NaturalHyperplanes.coordinateSwap
  have hC : pointCore.map (MulAut.conj c).toMonoidHom ≤ Theory.SpecificGroups.SymmetricSix.borel := by
    rw [←NaturalHyperplanes.map_flag_borel]
    exact map_mono pointCore_le_flag
  obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates_swap
    (u*c) a ha
  refine ⟨k,top_unique ?_⟩
  rw [←hk]
  apply sup_le_sup _ le_rfl
  apply map_mono
  have hh := map_mono (f := (MulAut.conj u).toMonoidHom) hC
  rw [map_map] at hh
  exact hh

private theorem borel_not_quadratic (u : S) :
    ¬ QuadraticPointCore.Quadratic
      (Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom) := by
  intro hquad
  let c := NaturalHyperplanes.coordinateSwap
  have hC : pointCore.map (MulAut.conj c).toMonoidHom ≤
      Theory.SpecificGroups.SymmetricSix.borel := by
    rw [←NaturalHyperplanes.map_flag_borel]
    exact map_mono pointCore_le_flag
  have hP : pointCore.map (MulAut.conj (u*c)).toMonoidHom ≤
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj u).toMonoidHom) hC
    rw [map_map] at hh
    exact hh
  have hbound := QuadraticPointCore.conjugate_core_bound
    (pointCore.map (MulAut.conj (u*c)).toMonoidHom) (u*c) le_rfl
    (fun a ha b hb v => hquad a (hP ha) b (hP hb) v)
  rw [card_map_of_injective (MulAut.conj (u*c)).injective,pointCore_card] at hbound
  omega

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_swap_generating_neighbor
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (A.comap (embedM Rg)).map π)
    (haswap : a.IsSwap) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
  let := h.relative_normal
  let A₀ := A.comap (embedM Rg)
  have hmapA : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base Rg))
  obtain ⟨k,hkgen⟩ := borel_conjugate_generates_swap u a haswap
  have hkL : k.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hm : ((Rg).map (MulAut.conj g).toMonoidHom).map π =
      ((Rg).map π).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change π (g*x*g⁻¹) = k.val*π x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let F := (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀
  have hQF : pCore 2 M ≤ F := by
    rw [←hQ]
    exact (map_mono h.relative_radical.twoCore_le).trans le_sup_left
  have hfullF : F.map π = ⊤ := by
    rw [Subgroup.map_sup,hm]
    apply top_unique
    rw [←hkgen]
    exact sup_le_sup (by rw [hR]) (zpowers_le.mpr ha)
  have hFE : F ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) hfullF
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEF : extensionKernel h ≤ F := by
    have he := extensionKernel_no_supplement h F (hFE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at he
    exact he
  have hgen : (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    change F = ⊤
    rwa [sup_of_le_left hEF] at hFE
  let f := (embedM Rg g)⁻¹
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  refine ⟨act Rg f (beta Rg),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr
      (base_adjacent Rg)
  · have hh := congrArg (Subgroup.map (embedM Rg)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    have hmapR : ((Rg).map (embedM Rg)).map (MulAut.conj f⁻¹).toMonoidHom =
        ((Rg).map (MulAut.conj g).toMonoidHom).map (embedM Rg) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM Rg x*(f⁻¹)⁻¹=embedM Rg (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include h e hz hk in
/-- Small critical images generate with a single actual Borel edge. -/
private theorem borel_small_critical_generating_neighbor_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  exact borel_swap_generating_neighbor h e hz hk u hR _
    (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical) a (hA.symm ▸ mem_zpowers a) ha

include h e hz hk in
/-- Every critical image, small or large, generates with a single Borel edge. -/
private theorem borel_critical_generating_neighbor_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
  by_cases hs : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4
  · exact borel_small_critical_generating_neighbor_base h e hz hk u hR p hs
  · obtain ⟨A,hAU,_,_,_,t,hat,hgen⟩ :=
      large_remaining_generating_actor h e hz hk u (Or.inr hR) p (by omega)
    refine ⟨t,hat,le_antisymm ?_ ?_⟩
    · exact sup_le (le_sup_left.trans hgen.le)
        (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
          (sourceDistance_pos h) p.critical)
    · rw [←hgen]
      exact sup_le_sup le_rfl (hAU.trans (DistanceEight.U_le_Z Rg z))

include h e hz hk in
/-- Single-edge generation holds at every component vertex, in both critical-image cases. -/
theorem borel_critical_generating_neighbor
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ∃ t, Adjacent Rg a t ∧ Q Rg t ⊔ Z Rg z = stabilizer Rg a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hga : act Rg g (alpha Rg) = a := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hback : act Rg g⁻¹ a = alpha Rg := by
    rw [←hga,←act_mul,mul_inv_cancel,act_one]
  have hp : Nonempty (CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg g⁻¹ z)) := by
    rw [←hback]
    exact ⟨p.act g⁻¹⟩
  obtain ⟨q⟩ := hp
  obtain ⟨t,hat,hgen⟩ := borel_critical_generating_neighbor_base h e hz hk u hR q
  have hzback : act Rg g (act Rg g⁻¹ z) = z := by
    rw [←act_mul,inv_mul_cancel,act_one]
  refine ⟨act Rg g t,?_,?_⟩
  · rw [←hga]
    exact (adjacent_act_iff Rg g _ _).mpr hat
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rwa [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hga,hzback] at hh

include h e hz hk in
/-- Every generating Borel edge moves the full small critical kernel.
The opposite seed centralizes that kernel, so normalization by the edge
would imply normalization by the entire component stabilizer. -/
theorem generating_edge_not_normalizes_kernel
    {a z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg a) :
    ¬ Q Rg t ≤ normalizer ((Z Rg a ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  intro hn
  apply small_critical_kernel_not_normalized h e hz hk p hsmall
  rw [←hgen]
  apply sup_le hn
  apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
  rw [←critical_seed_centralizer_intersection h e p]
  exact inf_le_right

include h e hz hk in
/-- A selected Sylow edge supplies a single element moving both the full
critical kernel and the critical line. Its action carries the complete path
and fixes the selected edge vertex. Both possible full covers are retained. -/
theorem borel_small_critical_edge_displacement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ t, Adjacent Rg a t ∧ Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      ∃ g ∈ Q Rg t, act Rg g t = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) a (act Rg g z),
        (∀ i, q.walk.getVert i = act Rg g (p.walk.getVert i)) ∧
        (Q Rg (act Rg g z)).relIndex (Z Rg a) = 2 ∧
        Z Rg a ⊓ Q Rg (act Rg g z) ≠ Z Rg a ⊓ Q Rg z ∧
        ⁅Z Rg a,Z Rg (act Rg g z)⁆ ≠ ⁅Z Rg a,Z Rg z⁆ := by
  obtain ⟨t,hat,hgen⟩ := borel_critical_generating_neighbor h e hz hk u hR p
  have hn := generating_edge_not_normalizes_kernel h e hz hk p hsmall hgen
  obtain ⟨r,hr,hrn⟩ := SetLike.not_le_iff_exists.mp hn
  let g := r⁻¹
  have hgT : g ∈ Q Rg t := (Q Rg t).inv_mem hr
  have hgG : g ∈ stabilizer Rg a := (le_sup_left.trans hgen.le) hgT
  have hga : act Rg g a = a := hgG
  have hpath : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg g a) (act Rg g z),
      ∀ i, q.walk.getVert i = act Rg g (p.walk.getVert i) :=
    ⟨p.act g,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hga] at hpath
  obtain ⟨q,hwalk⟩ := hpath
  have hs : (Q Rg (act Rg g z)).relIndex (Z Rg a) < 4 := by
    rw [←hga,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hsmall
  have hkernel : Z Rg a ⊓ Q Rg (act Rg g z) ≠ Z Rg a ⊓ Q Rg z := by
    intro he
    apply hrn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Z Rg a ⊓ Q Rg z).map (MulAut.conj r).toMonoidHom = Z Rg a ⊓ Q Rg z
    rw [Subgroup.map_inf _ _ _ (MulAut.conj r).injective]
    have hZ : (Z Rg a).map (MulAut.conj r).toMonoidHom = Z Rg a := by
      simpa only [g,inv_inv,hga] using (Z_act Rg g a).symm
    rw [hZ]
    simpa only [Q_act,g,inv_inv] using he
  refine ⟨t,hat,hgen,g,hgT,hgT.1,q,hwalk,
    (small_critical_indices h e hz hk q hs).1,hkernel,?_⟩
  exact fun he => hkernel (small_critical_equal_lines_kernels h e hz hk q p hs hsmall he)

include h e hz hk in
/-- The entire Borel edge is nonquadratic on each full moving cover. -/
theorem borel_edge_not_quadratic
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    ⁅⁅U Rg a,Q Rg t⁆,Q Rg t⁆ ≠ ⊥ := by
  intro hzero
  obtain ⟨i,hi,_,hiR,_,hiW⟩ := remaining_edge_coordinates h e hz ha hat
  let W := (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
  have hmap : (⁅⁅W,Rg⁆,Rg⁆ : Subgroup M).map i = ⊥ := by
    rw [map_commutator,map_commutator,hiW,hiR]
    exact hzero
  have hcomm : ⁅⁅W,Rg⁆,Rg⁆ = ⊥ := by
    apply (map_injective hi)
    rw [hmap,Subgroup.map_bot]
  have hquad := image_quadratic_of_commutator h e hz hk Rg
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  rw [hR] at hquad
  exact borel_not_quadratic u hquad

private theorem distinct_index_two_join {H : Type*} [Group H]
    (A B T : Subgroup H) (hAT : A ≤ T) (hBT : B ≤ T)
    (hA : A.relIndex T = 2) (hB : B.relIndex T = 2) (hne : A ≠ B) :
    A ⊔ B = T ∧ (A ⊓ B).relIndex A = 2 ∧ (A ⊓ B).relIndex B = 2 ∧
      (A ⊓ B).relIndex T = 4 := by
  have hBA : ¬ B ≤ A := by
    intro hle
    have hh := relIndex_mul_relIndex B A T hle hAT
    rw [hA,hB] at hh
    have he : B.relIndex A = 1 := by omega
    exact hne (le_antisymm (relIndex_eq_one.mp he) hle)
  have hAB : ¬ A ≤ B := by
    intro hle
    have hh := relIndex_mul_relIndex A B T hle hBT
    rw [hA,hB] at hh
    have he : A.relIndex B = 1 := by omega
    exact hne (le_antisymm hle (relIndex_eq_one.mp he))
  have index (P N : Subgroup H) (hNT : N ≤ T)
      (hP : P.relIndex T = 2) (hNP : ¬ N ≤ P) : (P ⊓ N).relIndex N = 2 := by
    have hi : P.relIndex N ≤ 2 := by
      have hh := relIndex_le_of_le_right (H := P) hNT (by omega : P.relIndex T ≠ 0)
      rwa [hP] at hh
    have hn : P.relIndex N ≠ 1 := fun hh => hNP (relIndex_eq_one.mp hh)
    have hz : P.relIndex N ≠ 0 := fun hh => by
      have he := relIndex_eq_zero_of_le_right hNT hh
      omega
    rw [inf_relIndex_right]
    omega
  have hiA : (A ⊓ B).relIndex A = 2 := by
    rw [inf_comm]
    exact index B A hAT hB hAB
  have hiB : (A ⊓ B).relIndex B = 2 := index A B hBT hA hBA
  have hiT : (A ⊓ B).relIndex T = 4 := by
    rw [←relIndex_mul_relIndex (A ⊓ B) A T inf_le_left hAT,hiA,hA]
  have hm := relIndex_mul_relIndex A (A ⊔ B) T le_sup_left (sup_le hAT hBT)
  rw [hA] at hm
  have hd : A.relIndex (A ⊔ B) ∣ 2 := ⟨(A ⊔ B).relIndex T,hm.symm⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
  · exact (hBA (le_sup_right.trans (relIndex_eq_one.mp he))).elim
  · rw [he] at hm
    have hi : (A ⊔ B).relIndex T = 1 := by omega
    exact ⟨le_antisymm (sup_le hAT hBT) (relIndex_eq_one.mp hi),hiA,hiB,hiT⟩

include h e hz hk in
/-- A distinct Thompson choice across the same Borel edge moves the full
cover with index greater than four. The argument uses maximality in the
literal small-mover family, including its relative-index inequality. -/
theorem borel_cross_thompson_fixed_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
    4 < (centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg))).relIndex (U Rg a) := by
  obtain ⟨Ja,hfamily,hJa,hQa,hAT,hAi,hQAi,_,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR ha hat
  obtain ⟨Jc,_,hJc,_,hCT,hCi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
  rw [hJa,hJc] at hne
  rw [hJc]
  have hQAT : (Q Rg a).relIndex (Q Rg t) = 16 := by
    rw [←relIndex_mul_relIndex (Q Rg a) Ja (Q Rg t) hQa hAT,hQAi,hAi]
  have hm := relIndex_inf_mul_relIndex (Q Rg a) Jc (Q Rg t)
  rw [inf_eq_left.mpr hCT,hCi] at hm
  have hnn : (Q Rg a ⊓ Jc).relIndex (Q Rg t) ≠ 0 :=
    relIndex_inf_ne_zero (by rw [hQAT]; decide) (by rw [hCi]; decide)
  have hlo := relIndex_le_of_le_left (H := Q Rg a ⊓ Jc) (K := Q Rg a) inf_le_left hnn
  rw [hQAT,←hm] at hlo
  have hlarge : 8 ≤ (Q Rg a).relIndex Jc := by omega
  have hcard : Nat.card Ja = Nat.card Jc := by
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) Ja (Q Rg t) bot_le hAT
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) Jc (Q Rg t) bot_le hCT
    rw [relIndex_bot_left,relIndex_bot_left,hAi] at h1
    rw [relIndex_bot_left,relIndex_bot_left,hCi] at h2
    omega
  by_contra! hsmall
  have hJasmall : Ja ∈ edgeMaximalOffenders a t := hfamily.symm ▸ Set.mem_singleton Ja
  have hJcsmall : edgeSmallMover a t Jc := ⟨hCT,by omega,hsmall⟩
  have hJcmax : Jc ∈ edgeMaximalOffenders a t := by
    refine ⟨hJcsmall,fun A hA => ?_⟩
    rw [←hcard]
    exact hJasmall.2 A hA
  rw [hfamily,Set.mem_singleton_iff] at hJcmax
  exact hne hJcmax.symm

include h e hz hk in
/-- The two quadratic Thompson choices on one Borel edge either coincide,
or generate that full edge, which is nonquadratic on both full covers.
In the latter case their intersection has index four in the edge. -/
theorem borel_adjacent_thompson_comparison
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    let Ja := edgeOffenderJoin a t
    let Jc := edgeOffenderJoin c t
    Ja = Jc ∨ (Ja ⊔ Jc = Q Rg t ∧
      (Ja ⊓ Jc).relIndex Ja = 2 ∧ (Ja ⊓ Jc).relIndex Jc = 2 ∧
      (Ja ⊓ Jc).relIndex (Q Rg t) = 4 ∧
      ⁅⁅U Rg a,Ja ⊔ Jc⁆,Ja ⊔ Jc⁆ ≠ ⊥ ∧
      ⁅⁅U Rg c,Ja ⊔ Jc⁆,Ja ⊔ Jc⁆ ≠ ⊥ ∧
      4 < (centralizer (Jc : Set (FreeAmalgam Rg))).relIndex (U Rg a) ∧
      4 < (centralizer (Ja : Set (FreeAmalgam Rg))).relIndex (U Rg c)) := by
  dsimp only
  by_cases he : edgeOffenderJoin a t = edgeOffenderJoin c t
  · exact Or.inl he
  · have hca := borel_cross_thompson_fixed_index h e hz hk u hR ha hc hat hct he
    have hac := borel_cross_thompson_fixed_index h e hz hk u hR hc ha hct hat (Ne.symm he)
    obtain ⟨Ja,_,hJa,_,hAT,hAi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR ha hat
    obtain ⟨Jc,_,hJc,_,hCT,hCi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
    simp only [hJa,hJc] at he hca hac ⊢
    obtain ⟨hgen,hintA,hintC,hintT⟩ := distinct_index_two_join Ja Jc (Q Rg t) hAT hCT hAi hCi he
    refine Or.inr ⟨hgen,hintA,hintC,hintT,?_,?_,hca,hac⟩ <;> rw [hgen]
    · exact borel_edge_not_quadratic h e hz hk u hR ha hat
    · exact borel_edge_not_quadratic h e hz hk u hR hc hct

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
