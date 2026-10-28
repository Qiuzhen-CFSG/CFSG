module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Action
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Coordinates

/-!
# The actual noncentral order-four orbit in the HS core

Three elements of the alternating preimage suffice: a core element, a square
in the full local group, and a commutator in that group. The latter two are
packed permutations proved equal to explicit words in the existing ATLAS
carrier. Their membership in the alternating preimage follows from the sign
homomorphism, without a residual-identification assumption.

A rooted tree of 30 coordinate representatives is certified one conjugation
edge at a time. The faithful two-letter encoding checks every edge and the
exhaustive coverage of noncentral elements of order four. Induction on the
tree constructs actual conjugators; composing two such conjugators proves
transitivity with the literal inclusions into `localGroup 0`.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
The cycle word is the word of the existing `CentralNormalizerThreePart.PairQuotient`
certificate. ATLAS attribution is inherited from the exact degree-100 carrier;
`source/discover.py` and `source/README.md` record the reproducible data.
-/

public section
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
namespace OrbitCertificate
open scoped commutatorElement

private def letterA : Carrier := ⟨ab0, by
  rw [ab0_eq]
  exact subset_closure (by simp)⟩
private def letterB : Carrier := ⟨ab1, by
  rw [ab1_eq]
  exact subset_closure (by simp)⟩
private def seed : Carrier := letterB ^ 2 * letterA * letterB
private def cycleWord : Carrier := seed * (e0 * seed⁻¹ * e0 * seed) ^ 2

private theorem cycle_commutes : cycleWord * e0 = e0 * cycleWord := by
  decide +kernel
private theorem swap_commutes : s1 * e0 = e0 * s1 := by
  decide +kernel
private def cycleLocal : localGroup 0 := ⟨cycleWord, by
  rw [localGroup_zero_eq_centralizer]
  exact mem_centralizer_singleton_iff.mpr cycle_commutes⟩
private def swapLocal : localGroup 0 := ⟨s1, by
  rw [localGroup_zero_eq_centralizer]
  exact mem_centralizer_singleton_iff.mpr swap_commutes⟩

private def squareMap (i : Fin 100) : Fin 100 :=
  ⟨(3754953860512535420521588074120066152212330283153308474767878009608598772321952716592162120107999643926759932392851348847112283756537374007110723771904401743346619367125857549474760448405491565051441613203046963 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def squareInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3338198519254972805247037538353432714687100092073136879381295492119113207051424888923924201508195214366605351998285339887678723379427418572909248005340444444433904544265181488544432574732895932000485506596758570 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem square_left : ∀ i, squareInvMap (squareMap i) = i := by
  decide +kernel
private def squarePerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm squareMap squareInvMap square_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin square_left)
private theorem square_word : squarePerm = (cycleLocal ^ 2).val.val := by
  decide +kernel
private def squareLocal : localGroup 0 :=
  ⟨⟨squarePerm, by rw [square_word]; exact (cycleLocal ^ 2).val.property⟩, by
    have he : (⟨squarePerm, by rw [square_word]; exact (cycleLocal ^ 2).val.property⟩ : Carrier) =
        (cycleLocal ^ 2).val := Subtype.ext square_word
    rw [he]
    exact (cycleLocal ^ 2).property⟩
private theorem squareLocal_eq : squareLocal = cycleLocal ^ 2 :=
  Subtype.ext (Subtype.ext square_word)

private def commMap (i : Fin 100) : Fin 100 :=
  ⟨(688896060197443674835727279297159121620645697142152065859258310506247248619472746891083247362819188477422606797580674581871091993745193960735904237429865803688861246566857699803430015629390750908946270899408512 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def commInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3337594035021132897827968689418550622769490317754302824330933447690389552488377418567922101591269809400366943771492477670303823509536710150615269806109012480850656004638293862750920792446580674865903903304980480 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem comm_left : ∀ i, commInvMap (commMap i) = i := by
  decide +kernel
private def commPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm commMap commInvMap comm_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin comm_left)
private theorem comm_word : commPerm = (⁅cycleLocal, swapLocal⁆).val.val := by
  decide +kernel
private def commLocal : localGroup 0 :=
  ⟨⟨commPerm, by rw [comm_word]; exact (⁅cycleLocal, swapLocal⁆).val.property⟩, by
    have he : (⟨commPerm, by rw [comm_word]; exact (⁅cycleLocal, swapLocal⁆).val.property⟩ : Carrier) =
        (⁅cycleLocal, swapLocal⁆).val := Subtype.ext comm_word
    rw [he]
    exact (⁅cycleLocal, swapLocal⁆).property⟩
private theorem commLocal_eq : commLocal = ⁅cycleLocal, swapLocal⁆ :=
  Subtype.ext (Subtype.ext comm_word)

private theorem square_mem_residual : squareLocal ∈ modelResidual := by
  rw [squareLocal_eq]
  change CentralNormalizerThreePart.PairQuotient.fiveHom (cycleLocal ^ 2) ∈
    alternatingGroup (Fin 5)
  rw [Equiv.Perm.mem_alternatingGroup, map_pow, map_pow, pow_two]
  exact Int.units_mul_self _
private theorem comm_mem_residual : commLocal ∈ modelResidual := by
  rw [commLocal_eq]
  change CentralNormalizerThreePart.PairQuotient.fiveHom ⁅cycleLocal,swapLocal⁆ ∈
    alternatingGroup (Fin 5)
  rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private def stepElement : Fin 3 → localGroup 0 :=
  ![(qElement 0).val, squareLocal, commLocal]
private theorem step_mem : ∀ i, stepElement i ∈ modelResidual := by
  intro i
  fin_cases i
  · exact model_core_le_residual (qElement 0).property
  · exact square_mem_residual
  · exact comm_mem_residual

open ModelOrbitCoordinates

private def vertex (i : Fin 30) : core := coordinate (![1, 33, 2, 25, 34, 57, 59, 4, 27, 36, 31, 35, 8, 62, 63, 3, 40, 30, 55, 61, 22, 53, 23, 29, 54, 21, 12, 44, 58, 26] i)
private def parent : Fin 30 → Fin 30 := ![0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 12, 13, 14, 14, 16, 17, 19, 20, 21, 25]
private def step : Fin 30 → Fin 3 := ![0, 0, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1]
private theorem parent_lt : ∀ i : Fin 30, i ≠ 0 → parent i < i := by
  decide +kernel

private def conjugate (g : localGroup 0) (x : core) : core :=
  ⟨g * x.val * g⁻¹, core_normal.conj_mem x.val x.property g⟩
private theorem edge_code : ∀ i : Fin 30, i ≠ 0 →
    encode (conjugate (stepElement (step i)) (vertex (parent i))) = encode (vertex i) := by
  decide +kernel
private theorem edge (i : Fin 30) (hi : i ≠ 0) :
    stepElement (step i) * (vertex (parent i)).val * (stepElement (step i))⁻¹ =
      (vertex i).val := congrArg Subtype.val (encode_injective (edge_code i hi))

private def index : Fin 64 → Fin 30 :=
  ![0, 0, 2, 15, 7, 0, 0, 0, 12, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 25, 20, 22, 0, 3, 29, 8, 0, 23, 17, 10, 0, 1, 4, 11, 9, 0, 0, 0, 16, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 21, 24, 18, 0, 5, 28, 6, 0, 19, 13, 14]
private theorem coverage : ∀ i : Fin 64,
    encode (coordinate i ^ 2) = encode 1 ∨
      (∃ d : C4, encode (cyclicEmbedding d) = encode (coordinate i)) ∨
      encode (vertex (index i)) = encode (coordinate i) := by
  decide +kernel

private theorem root : vertex 0 = leftI := by
  apply encode_injective
  decide +kernel

private theorem vertex_reached (i : Fin 30) :
    ∃ g : modelResidual, g.val * leftI.val * g.val⁻¹ = (vertex i).val := by
  suffices h : ∀ n : Nat, ∀ i : Fin 30, i.val = n →
      ∃ g : modelResidual, g.val * leftI.val * g.val⁻¹ = (vertex i).val from h i.val i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      refine ⟨1, ?_⟩
      simp only [coe_one, one_mul, inv_one, mul_one, root]
    · obtain ⟨g, hg⟩ := ih (parent i).val
        (by rw [← hi]; exact parent_lt i hi0) (parent i) rfl
      refine ⟨⟨stepElement (step i), step_mem _⟩ * g, ?_⟩
      change (stepElement (step i) * g.val) * leftI.val *
        (stepElement (step i) * g.val)⁻¹ = (vertex i).val
      calc
        _ = stepElement (step i) * (g.val * leftI.val * g.val⁻¹) *
            (stepElement (step i))⁻¹ := by group
        _ = stepElement (step i) * (vertex (parent i)).val *
            (stepElement (step i))⁻¹ := by rw [hg]
        _ = (vertex i).val := edge i hi0

/-- Every noncentral element of order four is reached from the marked quaternion root. -/
theorem root_reaches (x : core) (hxZ : x ∉ center core) (hx4 : orderOf x = 4) :
    ∃ g : modelResidual, g.val * leftI.val * g.val⁻¹ = x.val := by
  obtain ⟨i,rfl⟩ := coordinate_surjective x
  rcases coverage i with hsq | ⟨d,hd⟩ | horbit
  · have hd := orderOf_dvd_of_pow_eq_one (encode_injective hsq)
    rw [hx4] at hd
    norm_num at hd
  · exact (hxZ (by rw [model_core_center]; exact ⟨d,encode_injective hd⟩)).elim
  · rw [← encode_injective horbit]
    exact vertex_reached _

end OrbitCertificate

theorem model_leftI_noncentral : leftI ∉ center core := by
  intro h
  have hc := congrArg ModelOrbitCoordinates.encode (mem_center_iff.mp h leftJ)
  exact (show ModelOrbitCoordinates.encode (leftJ * leftI) ≠
    ModelOrbitCoordinates.encode (leftI * leftJ) by decide +kernel) hc

theorem model_leftI_order_four : orderOf leftI = 4 :=
  (model_core_order_four_iff _).mpr rfl

/-- Actual conjugation in the alternating preimage is transitive on the
noncentral order-four elements. All inclusions are into the full local group. -/
theorem modelResidual_orderFour_transitive (x y : core)
    (hxZ : x ∉ center core) (hyZ : y ∉ center core)
    (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) :
    ∃ g : modelResidual, g.val * x.val * g.val⁻¹ = y.val := by
  obtain ⟨gx,hx⟩ := OrbitCertificate.root_reaches x hxZ hx4
  obtain ⟨gy,hy⟩ := OrbitCertificate.root_reaches y hyZ hy4
  refine ⟨gy * gx⁻¹, ?_⟩
  change (gy.val * gx.val⁻¹) * x.val * (gy.val * gx.val⁻¹)⁻¹ = y.val
  rw [← hx, ← hy]
  group

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
