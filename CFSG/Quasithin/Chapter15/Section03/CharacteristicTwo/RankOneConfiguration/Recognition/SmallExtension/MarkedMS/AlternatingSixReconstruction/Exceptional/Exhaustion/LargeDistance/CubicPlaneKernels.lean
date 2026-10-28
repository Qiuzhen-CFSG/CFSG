module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicThompsonSelectors
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Shared kernels of normalized plane selectors in the cubic graph

The two small critical paths selected in the plane and Borel branches have
distinct critical lines. Equal lines would make their actions agree modulo
the full cubic kernel E. A Thompson mover has fixed index four on the moving
cover, and one small seed has fixed index at most two. Their common fixed
subgroup would therefore have index at most eight, whereas the whole local
stabilizer has fixed index sixteen. This contradicts the retained generation
identity. The argument works for both cover orders sixteen and thirty-two.

The full seed is the moving cover joined to the incident edge seed, which
centralizes the mover. Thus the mover has fixed index four on the full seed
as well. Two distinct critical kernels of index two intersect in exactly this
fixed subgroup. The two critical lines generate a four-group; quadraticity
puts this entire commutator in that common kernel. The original component
switch normalizes the common kernel, without an order assumption on its lift.

The same paired configuration excludes simultaneous backward containment with
both full reverse omega-kernel commutators central at the chosen eligible
vertex. Central movement forces each reverse kernel into that vertex's
actual two-core. The predecessor commutator bounds then make the seed product
normal under the two endpoint seeds and the selected Thompson mover. Their
join is the full original stabilizer, so the product lies in its Baumann
slice, contrary to eligibility. This uses X at each endpoint, not an
identification of X with the central-omega orbit defining U or with Z.

The final consumer constructs the normalized pair, records every vertex of
the switched path, and transports any strict slice using one neighbor
conjugator. It supplies the kernel identities and applies the backward
exclusion on exactly those paths. Noncentral reverse-kernel movement still
has to be excluded to obtain a backward critical path in all cases. The
R4/R6 and terminal plane/Borel contradictions, both core exhaustions and
final reconstruction remain open; this is not the complete source (5.7).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)(b--d) and the paired fixed-subgroup argument of (5.7), printed
pp.917--919; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
private theorem moving_whole_fixed_index {a : Vertex Rg} (ha : color Rg a = false) :
    (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg a) = 16 := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,f,hf,hker,hact⟩ := graph_cover h e hz hk a ha
  change ((centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).subgroupOf (U Rg a)).index = 16
  rw [←hker,index_ker,MonoidHom.range_eq_top.mpr hf,Nat.card_congr topEquiv.toEquiv]
  change Nat.card (natural (Fin 6)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    finrank_natural_even (Fin 6) (by decide)]
  decide

include h e hz hk in
private theorem small_critical_moving_fixed_index {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hs : (Q Rg z).relIndex (Z Rg a) < 4) :
    (centralizer (Z Rg z : Set (FreeAmalgam Rg))).relIndex (U Rg a) ≤ 2 := by
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  have hQ : Q Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z p.end_color))
  exact ((relIndex_le_of_le_left hQ index_ne_zero_of_finite).trans
    (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices h e hz hk p hs).1

include h e hz hk in
private theorem paired_small_lines_ne
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z z' t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) a z')
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t)
    (hgen : (edgeOffenderJoin a t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a) :
    ⁅Z Rg a,Z Rg z⁆ ≠ ⁅Z Rg a,Z Rg z'⁆ := by
  intro he
  let C := (U Rg a ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg))) ⊓
    centralizer (Z Rg z : Set (FreeAmalgam Rg))
  have hE : U Rg a ≤ centralizer
      (stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le
      ((DistanceEight.U_le_Z Rg a).trans ((sourceGeometry h).omega_bound a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h)))))
  have hj := small_critical_equal_lines_image h e hz hk p q hp hq he
  have hCz' : C ≤ centralizer (Z Rg z' : Set (FreeAmalgam Rg)) := by
    have hCE : C ≤ centralizer
        (((stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg))) ⊔ Z Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
      apply le_centralizer_iff.mp
      exact sup_le (le_centralizer_iff.mp ((inf_le_left.trans inf_le_left).trans hE))
        (le_centralizer_iff.mp inf_le_right)
    rw [hj] at hCE
    exact hCE.trans (centralizer_le (show Z Rg z' ≤
      (stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg))) ⊔ Z Rg z' from le_sup_right))
  have hCG : C ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (sup_le (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
      (le_centralizer_iff.mp inf_le_right)) (le_centralizer_iff.mp hCz')
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  have hl : 16 ≤ C.relIndex (U Rg a) := by
    rw [←moving_whole_fixed_index h e hz hk p.start_color]
    exact relIndex_le_of_le_left hCG index_ne_zero_of_finite
  have hu : C.relIndex (U Rg a) ≤ 4*2 := by
    have hh := relIndex_inf_le (H := centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)))
      (K := centralizer (Z Rg z : Set (FreeAmalgam Rg))) (L := U Rg a)
    have hj4 := (remaining_edge_thompson h e hz hk u hR p.start_color hat).2.2.2.2.2.2.1
    have hs := small_critical_moving_fixed_index h e hz hk p hp
    have hc : C = U Rg a ⊓ (centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ⊓
        centralizer (Z Rg z : Set (FreeAmalgam Rg))) := inf_assoc _ _ _
    rw [hc,inf_relIndex_left]
    exact hh.trans (Nat.mul_le_mul hj4.le hs)
  omega

private theorem fixed_index_central_supplement {F : Type*} [Group F]
    (Z U E A : Subgroup F) [IsMulCommutative Z]
    (hZ : Z = U ⊔ E) (hE : E ≤ centralizer (A : Set F)) :
    (centralizer (A : Set F)).relIndex Z = (centralizer (A : Set F)).relIndex U := by
  let C := Z ⊓ centralizer (A : Set F)
  have hUZ : U ≤ Z := hZ ▸ le_sup_left
  have hEC : E ≤ C := le_inf (hZ ▸ le_sup_right) hE
  have hCU : C ⊔ U = Z := by
    apply le_antisymm (sup_le inf_le_left hUZ)
    calc
      Z = U ⊔ E := hZ
      _ ≤ C ⊔ U := sup_le le_sup_right (hEC.trans le_sup_left)
  have hn : U ≤ normalizer (C : Set F) :=
    ((hUZ.trans (le_centralizer Z)).trans (centralizer_le inf_le_left)).trans
      (centralizer_le_normalizer C)
  rw [←inf_relIndex_left Z (centralizer (A : Set F))]
  change C.relIndex Z = _
  rw [←hCU,relIndex_sup_of_normalized C U hn]
  change (Z ⊓ centralizer (A : Set F)).relIndex U = _
  have hh := relIndex_inf_mul_relIndex (centralizer (A : Set F)) Z U
  rw [relIndex_eq_one.mpr hUZ,inf_of_le_right hUZ,mul_one] at hh
  simpa only [inf_comm Z] using hh.symm

include h e hz hk in
private theorem remaining_edge_full_seed_fixed_index
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    (centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg))).relIndex (Z Rg a) = 4 := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hj := remaining_edge_thompson h e hz hk u hR ha hat
  have he : Z Rg t ≤ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) := by
    apply le_trans ?_ (centralizer_le hj.2.2.1)
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a ha
  rw [fixed_index_central_supplement (Z Rg a) (U Rg a) (Z Rg t)
    (edgeOffenderJoin a t) (vertex_seed_eq_moving_sup_edge h e hz ha hat) he]
  exact hj.2.2.2.2.2.2.1

private theorem intersection_index_four {F : Type*} [Group F]
    (Z A B : Subgroup F) [Finite Z] (hAZ : A ≤ Z) (hBZ : B ≤ Z)
    (hA : A.relIndex Z = 2) (hB : B.relIndex Z = 2) (hne : A ≠ B) :
    (A ⊓ B).relIndex Z = 4 := by
  have hBA : ¬ B ≤ A := by
    intro hh
    have ht := relIndex_mul_relIndex B A Z hh hAZ
    rw [hA,hB] at ht
    have hi : B.relIndex A = 1 := by omega
    exact hne (le_antisymm (relIndex_eq_one.mp hi) hh)
  let : Finite B := Finite.of_injective (inclusion hBZ) (inclusion_injective _)
  have hpos : 0 < A.relIndex B := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi : A.relIndex B ≤ 2 := by
    exact (relIndex_le_of_le_right hBZ index_ne_zero_of_finite).trans_eq hA
  have hn : A.relIndex B ≠ 1 := fun he => hBA (relIndex_eq_one.mp he)
  have ht := relIndex_inf_mul_relIndex A B Z
  rw [inf_of_le_left hBZ,hB,show A.relIndex B = 2 from by omega] at ht
  omega

include h e hz hk in
/-- On the same pair of small critical paths, the full seed kernels have
intersection exactly the first-edge Thompson fixed subgroup. The two critical
lines are distinct and the common kernel has index four in the entire seed. -/
theorem remaining_paired_small_kernel_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z z' t t₀ : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) a z')
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hat₀ : Adjacent Rg a t₀)
    (hgen : (edgeOffenderJoin a t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hinside : Z Rg z ⊔ Z Rg z' ≤ edgeOffenderJoin a t₀) :
    ⁅Z Rg a,Z Rg z⁆ ≠ ⁅Z Rg a,Z Rg z'⁆ ∧
      Z Rg a ⊓ Q Rg z ≠ Z Rg a ⊓ Q Rg z' ∧
      (Z Rg a ⊓ Q Rg z) ⊓ (Z Rg a ⊓ Q Rg z') =
        Z Rg a ⊓ centralizer (edgeOffenderJoin a t₀ : Set (FreeAmalgam Rg)) ∧
      ((Z Rg a ⊓ Q Rg z) ⊓ (Z Rg a ⊓ Q Rg z')).relIndex (Z Rg a) = 4 := by
  have hline := paired_small_lines_ne h e hz hk u hR p q hp hq hat hgen
  have hkernel : Z Rg a ⊓ Q Rg z ≠ Z Rg a ⊓ Q Rg z' := by
    intro he
    exact hline (small_critical_equal_kernels h e hz hk p q hp hq he).2
  let A := Z Rg a ⊓ Q Rg z
  let B' := Z Rg a ⊓ Q Rg z'
  let C := Z Rg a ⊓ centralizer (edgeOffenderJoin a t₀ : Set (FreeAmalgam Rg))
  let := finite_Z Rg a
  have hA : A.relIndex (Z Rg a) = 2 := by
    rw [inf_relIndex_left]
    exact (small_critical_indices h e hz hk p hp).1
  have hB : B'.relIndex (Z Rg a) = 2 := by
    rw [inf_relIndex_left]
    exact (small_critical_indices h e hz hk q hq).1
  have hidx := intersection_index_four (Z Rg a) A B' inf_le_left inf_le_left hA hB hkernel
  have hC : C ≤ A ⊓ B' := by
    have hCa : C ≤ Z Rg a ⊓ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
      le_inf inf_le_left (inf_le_right.trans (centralizer_le (show Z Rg z ≤ edgeOffenderJoin a t₀ from le_sup_left.trans hinside)))
    have hCb : C ≤ Z Rg a ⊓ centralizer (Z Rg z' : Set (FreeAmalgam Rg)) :=
      le_inf inf_le_left (inf_le_right.trans (centralizer_le (show Z Rg z' ≤ edgeOffenderJoin a t₀ from le_sup_right.trans hinside)))
    rw [critical_seed_centralizer_intersection h e p] at hCa
    rw [critical_seed_centralizer_intersection h e q] at hCb
    exact le_inf hCa hCb
  have hCidx : C.relIndex (Z Rg a) = 4 := by
    rw [inf_relIndex_left]
    exact remaining_edge_full_seed_fixed_index h e hz hk u hR p.start_color hat₀
  have ht := relIndex_mul_relIndex C (A ⊓ B') (Z Rg a) hC (inf_le_left.trans inf_le_left)
  rw [hidx,hCidx] at ht
  have he : A ⊓ B' = C := le_antisymm (relIndex_eq_one.mp (by omega)) hC
  exact ⟨hline,hkernel,he,hidx⟩

private theorem distinct_two_lines_card {F : Type*} [Group F]
    (Z A B : Subgroup F) [IsMulCommutative Z]
    (hAZ : A ≤ Z) (hBZ : B ≤ Z)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) (hne : A ≠ B) :
    Nat.card (A ⊔ B : Subgroup F) = 4 := by
  let : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have hn : B ≤ normalizer (A : Set F) :=
    ((hBZ.trans (le_centralizer (H := Z))).trans (centralizer_le hAZ)).trans
      (centralizer_le_normalizer A)
  let : Finite (A ⊓ B : Subgroup F) := Finite.of_injective (inclusion (show A ⊓ B ≤ A from inf_le_left)) (inclusion_injective _)
  have hab : Disjoint A B := by
    rw [disjoint_iff]
    have hc : Nat.card (A ⊓ B : Subgroup F) ≤ 2 := (card_le_of_le inf_le_left).trans_eq hA
    have hcne : Nat.card (A ⊓ B : Subgroup F) ≠ 2 := by
      intro he
      have ha : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by omega)
      have hb : A ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by omega)
      exact hne (ha.symm.trans hb)
    exact eq_bot_of_card_le _ (by omega)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A B hn hab,hA,hB]

include h e hz hk in
/-- The two source-selected critical lines generate a four-group fixed by the
literal first-edge mover. This is a full-seed commutator calculation. -/
theorem remaining_paired_small_commutator_plane
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z z' t t₀ : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) a z')
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hat₀ : Adjacent Rg a t₀)
    (hgen : (edgeOffenderJoin a t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hinside : Z Rg z ⊔ Z Rg z' ≤ edgeOffenderJoin a t₀) :
    ⁅Z Rg a,Z Rg z ⊔ Z Rg z'⁆ = ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg a,Z Rg z'⁆ ∧
      Nat.card (⁅Z Rg a,Z Rg z ⊔ Z Rg z'⁆ : Subgroup (FreeAmalgam Rg)) = 4 ∧
      ⁅Z Rg a,Z Rg z ⊔ Z Rg z'⁆ ≤
        Z Rg a ⊓ centralizer (edgeOffenderJoin a t₀ : Set (FreeAmalgam Rg)) := by
  let J₀ := edgeOffenderJoin a t₀
  let A := ⁅Z Rg a,Z Rg z⁆
  let B' := ⁅Z Rg a,Z Rg z'⁆
  have hzG : Z Rg z ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) p.critical
  have hz'G : Z Rg z' ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a q.start_color
      (by rw [(sourceGeometry h).distance_constant a q.start_color]; exact sourceDistance_pos h) q.critical
  have hAZ : A ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    (hzG.trans (Z_normalized Rg a))
  have hBZ : B' ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    (hz'G.trans (Z_normalized Rg a))
  have hJ : ⁅Z Rg a,J₀⁆ ≤ centralizer (J₀ : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (remaining_edge_full_seed_quadratic h e hz hk u hR p.start_color hat₀)
  have hAC : A ≤ centralizer (J₀ : Set (FreeAmalgam Rg)) :=
    (commutator_mono le_rfl (le_sup_left.trans hinside)).trans hJ
  have hBC : B' ≤ centralizer (J₀ : Set (FreeAmalgam Rg)) :=
    (commutator_mono le_rfl (le_sup_right.trans hinside)).trans hJ
  have hn : J₀ ≤ normalizer ((A ⊔ B' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (sup_le hAC hBC)).trans (centralizer_le_normalizer (A ⊔ B'))
  have he : ⁅Z Rg a,Z Rg z ⊔ Z Rg z'⁆ = A ⊔ B' := by
    apply le_antisymm
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal J₀ (Z Rg z) (Z Rg z')
        (Z Rg a) (A ⊔ B') hn (le_sup_left.trans hinside) (le_sup_right.trans hinside)
      · rw [commutator_comm]; exact le_sup_left
      · rw [commutator_comm]; exact le_sup_right
    · exact sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  refine ⟨he,?_,?_⟩
  · rw [he]
    exact distinct_two_lines_card (Z Rg a) A B' hAZ hBZ
      (small_critical_commutator_card h e hz hk p hp)
      (small_critical_commutator_card h e hz hk q hq)
      (paired_small_lines_ne h e hz hk u hR p q hp hq hat hgen)
  · rw [he]
    exact le_inf (sup_le hAZ hBZ) (sup_le hAC hBC)

include h e hz hk in
/-- In the literal paired-selector configuration, simultaneous backward
containment forces a noncentral full reverse-omega-kernel commutator at the
same eligible vertex. No equality between X and Z is used. -/
theorem paired_backward_reverse_kernels_not_both_central
    (hb : 2 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    ¬ (⁅X Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) ∧
      ⁅X Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) := by
  rintro ⟨hcentral,hcentral'⟩
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hQtGc : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hQaQt : Q Rg (alpha Rg) ≤ Q Rg t := Q_le_adjacent_h Rg ht hat
  have kill (A : Subgroup (FreeAmalgam Rg)) (hAQ : A ≤ Q Rg (alpha Rg))
      (hcentral : ⁅A,Z Rg c⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) :
      A ≤ Q Rg c := by
    obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk c hc
    let A₀ := A.comap i
    have hm : A₀.map i = A := map_comap_eq_self ((hAQ.trans hQaQt).trans (hQtGc.trans hir.symm.le))
    have hcomm : ⁅(⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M),A₀⁆ ≤ center M := by
      intro v hv
      apply mem_center_iff.mpr
      intro m
      apply hi
      simp only [map_mul]
      apply hcentral
      · have hh := mem_map_of_mem i hv
        rw [map_commutator,hiU,hm,commutator_comm] at hh
        exact commutator_mono le_rfl (DistanceEight.U_le_Z Rg c) hh
      · rw [←hir]
        exact ⟨m,rfl⟩
    have hh := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk A₀
      (((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        (alpha Rg) rfl).to_le hAQ).comap_of_injective i hi) hcomm)
    rwa [hm,hiQ] at hh
  have hfix (v : Vertex Rg) (hv : color Rg v = false)
      (hK : X Rg v ⊓ Q Rg (alpha Rg) ≤ Q Rg c) :
      Z Rg c ≤ centralizer (Z Rg v ⊓ Q Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    have hseed : Z Rg v ≤ X Rg v := (sourceGeometry h).omega_bound v hv (by
      rw [(sourceGeometry h).distance_constant v hv]
      exact sourceDistance_pos h)
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc)).trans
      (centralizer_le ((inf_le_inf_right _ hseed).trans hK))
  have hm := small_critical_predecessor_commutator h e hz hk hb p hp (Z Rg c) hbad
    (hfix z p.end_color (kill _ inf_le_right hcentral))
  have hm' := small_critical_predecessor_commutator h e hz hk hb q hq (Z Rg c) hbad'
    (hfix z' q.end_color (kill _ inf_le_right hcentral'))
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hd)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove (v : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) v)
      (hm : ⁅Z Rg c,Z Rg v⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg v⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg v) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    apply le_normalizer_iff_commutator_le_left.mp
    exact (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) s.critical).trans (Z_normalized Rg _)
  have hYn : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · have hJ := (remaining_edge_thompson h e hz hk u hR rfl hat).2.2.1
      exact (le_inf ((hJ.trans hQtGc).trans (Z_normalized Rg c))
        ((hJ.trans (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
          fun _ hx => hx.2 _ (adjacent_symm Rg hat))).trans (Z_normalized Rg _))).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hmove z p hm).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hmove z' q hm').trans le_sup_right)
  exact hel ((DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
    (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
      (sup_le hZV (Z_le_VBall Rg _ 2)) hYn (hmove z p hm))))

include h e hz hk in
/-- The normalized selectors on the original critical path have distinct
full kernels, a common kernel of index four, and a four-group commutator.
The same switch normalizes this common kernel. Every vertex of the switched
critical path is retained explicitly. -/
theorem remaining_small_critical_paired_kernel_selectors
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      let J₀ := edgeOffenderJoin (alpha Rg) (p.walk.getVert 1)
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      let C := (Z Rg (alpha Rg) ⊓ Q Rg z) ⊓ (Z Rg (alpha Rg) ⊓ Q Rg (act Rg x z))
      let H := ⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (J₀ : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ J₀ ∧
        Z Rg (alpha Rg) ⊓ Q Rg z ≠ Z Rg (alpha Rg) ⊓ Q Rg (act Rg x z) ∧
        C = Z Rg (alpha Rg) ⊓ centralizer (J₀ : Set (FreeAmalgam Rg)) ∧
        C.relIndex (Z Rg (alpha Rg)) = 4 ∧
        x ∈ normalizer (C : Set (FreeAmalgam Rg)) ∧
        H = ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg (act Rg x z)⁆ ∧
        Nat.card H = 4 ∧ H ≤ C ∧
        ∀ delta, Adjacent Rg delta (p.walk.getVert 1) →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
          ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
            let c := act Rg g delta
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
            (Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
              Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) →
              ¬ (⁅X Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
                  centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) ∧
                ⁅X Rg (act Rg x z) ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
                  centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)))) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,hfixed,hnorm,hinside,hquad⟩ :=
    remaining_small_critical_normalized_plane_selectors h e hz hk u hR p hsmall
  let x := (embedM Rg r)⁻¹
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
    exact hsmall
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨hlines,hkernels,hcommon,hidx⟩ :=
    remaining_paired_small_kernel_comparison h e hz hk u hR p q hsmall hqs hat hat₀ hgen hinside
  obtain ⟨hH,hcard,hHle⟩ :=
    remaining_paired_small_commutator_plane h e hz hk u hR p q hsmall hqs hat hat₀ hgen hinside
  refine ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,hkernels,hcommon,hidx,?_,hH,hcard,?_,?_⟩
  · rw [hcommon]
    apply inf_normalizer_le_normalizer_inf
    exact ⟨Z_normalized Rg _ hxG,
      normalizer_le_normalizer_centralizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1)) hnorm⟩
  · rw [hcommon]
    exact hHle
  · intro delta hd hs
    have hb := distance_gt_two h e hz hk
    obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat₀ hat
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
    have hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg g delta)) := by
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hs
    have hct : Adjacent Rg (act Rg g delta) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hd
    refine ⟨g,hg,hgt,hindex,?_⟩
    intro hbad hbad'
    apply paired_backward_reverse_kernels_not_both_central h e hz hk hb u hR
      p q hsmall hqs hat hct hgen _ hbad hbad'
    intro hel
    have he := relIndex_eq_one.mpr hel
    omega

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
