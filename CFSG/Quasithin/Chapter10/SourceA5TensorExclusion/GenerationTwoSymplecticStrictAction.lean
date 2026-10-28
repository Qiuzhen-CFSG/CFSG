module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticStrictKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallAction

/-!
# The original small-movement action and its exact fixed kernel

For T0=C_Qa(U_d intersect B_a), the small B-index produces a symplectic
marking on the full U_d with kernel exactly T0 intersect Q_d and image
order at most four. Its actual commutator H is fixed by T0.

Either T0 lies in Q_d and H is trivial, or H has order four, the B-index
is exactly four, and U_d intersect B_a equals the full T0-fixed subgroup
of U_d, of order sixty-four. The last theorem applies this to the literal
second vertex of the original critical path.

These are the small-action and exact-kernel steps in MS93 (5.9), printed
p.920, for the source9.3.10 tensor geometry (Aschbacher--Smith, p.734).
The reversed critical witness and span argument, strict movement, both
distance exclusions and SymplecticPlaneRecognition remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Small movement gives an actual matrix action on the full neighboring
seed, retaining its complete neighborhood kernel and conjugation law. -/
theorem original_small_movement_root_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 →
      ∃ F : BinaryField, F.degree = 2 ∧
        ∃ f : kernelCentralizer geometry a d →* Sp F.Carrier,
          f.ker = (Q R d).subgroupOf (kernelCentralizer geometry a d) ∧
        ∃ j : Multiplicative (Vector F.Carrier) →* FreeAmalgam R,
          Function.Injective j ∧ j.range = U R d ∧
          (∀ (x : kernelCentralizer geometry a d) v,
            j (Multiplicative.ofAdd (f x • v)) =
              x.val*j (Multiplicative.ofAdd v)*x.val⁻¹) ∧
          Module.finrank F.Carrier (displacementSpace f.range) ≤ 1 ∧
          (Q R d).relIndex (kernelCentralizer geometry a d) ≤ 4 ∧
          (Nat.card (kernelCommutator geometry a d) = 1 ∨
            Nat.card (kernelCommutator geometry a d) = 4) ∧
          kernelCommutator geometry a d ≤
            centralizer (kernelCentralizer geometry a d : Set _) ∧
          Nat.card (kernelCommutator geometry a d) =
            (centralizer (kernelCentralizer geometry a d : Set _)).relIndex (U R d) := by
  intro R geometry hb a d t ha hat hdt hmove
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := kernelCentralizer geometry a d
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R d) ≤ 4 :=
    (kernelCentralizer_moving_index_le geometry a d).trans hmove
  have hAT : A ≤ Q R t := inf_le_left.trans (Q_le_adjacent_h R ht hat)
  have hAS : A ≤ stabilizer R d :=
    hAT.trans (fun _ hx => hx.2 d (adjacent_symm R hdt))
  obtain ⟨F,hF,f,hf,j,hj,hjr,hact,hdim,himage,hH,hquad⟩ :=
    original_small_actor_marking R hms hodd.isPGroup hne
      hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) hcard hBC hsq hd hfixed A hAS hsmall
  have hindex : (Q R d).relIndex A = Nat.card f.range := by
    change ((Q R d).subgroupOf A).index = _
    rw [←hf,index_ker]
  refine ⟨F,hF,f,hf,j,hj,hjr,hact,hdim,hindex.trans_le himage,?_,?_,?_⟩
  · simpa only [kernelCommutator,commutator_comm] using hH
  · simpa only [kernelCommutator,commutator_comm] using hquad
  · simpa only [kernelCommutator,commutator_comm] using
      original_small_displacement_card_eq_index R hms hodd.isPGroup hne
        hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _) hcard hBC hsq hd hfixed A hAS hsmall

/-- Triviality is measured against the complete original neighborhood kernel. -/
private theorem original_strict_kernel_commutator_eq_bot_iff
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      (kernelCommutator geometry a d = ⊥ ↔ kernelCentralizer geometry a d ≤ Q R d) := by
  intro R geometry a d t ha hat hdt
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hAS : kernelCentralizer geometry a d ≤ stabilizer R d :=
    (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans
      (fun _ hx => hx.2 d (adjacent_symm R hdt))
  have hCQ := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith d hd
  constructor
  · intro h
    rw [←hCQ]
    apply le_inf hAS
    rw [c.original_Z_eq_U d hd]
    apply commutator_eq_bot_iff_le_centralizer.mp
    simpa only [kernelCommutator,commutator_comm] using h
  · intro h
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact ((U_le_Z d).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R d hd))).trans (centralizer_le h)

/-- In the small-movement branch T0 either lies in the full opposite kernel,
or its actual commutator has order four and its whole fixed subgroup has
order sixty-four. The commutator is fixed by T0 itself. -/
theorem original_small_movement_kernel_alternative
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 →
      (kernelCentralizer geometry a d ≤ Q R d ∧ kernelCommutator geometry a d = ⊥) ∨
      (¬ kernelCentralizer geometry a d ≤ Q R d ∧
        Nat.card (kernelCommutator geometry a d) = 4 ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 4 ∧
        U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) =
          U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) ∧
        Nat.card (U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) :
          Subgroup (FreeAmalgam R)) = 64 ∧
        (Q R d).relIndex (kernelCentralizer geometry a d) ≤ 4 ∧
        kernelCommutator geometry a d ≤ centralizer (kernelCentralizer geometry a d : Set _)) := by
  intro R geometry hb a d t ha hat hdt hmove
  have hiff := c.original_strict_kernel_commutator_eq_bot_iff eK geometry ha hat hdt
  by_cases hk : kernelCentralizer geometry a d ≤ Q R d
  · exact Or.inl ⟨hk,hiff.mpr hk⟩
  obtain ⟨F,hF,f,hf,j,hj,hjr,hact,hdim,hindex,hH,hquad,hHindex⟩ :=
    c.original_small_movement_root_action eK geometry hb ha hat hdt hmove
  have hH4 : Nat.card (kernelCommutator geometry a d) = 4 :=
    hH.resolve_left (fun hh => hk (hiff.mp (card_eq_one.mp hh)))
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hU : Nat.card (U R d) = 256 := by
    rw [←c.original_Z_eq_U d hd]
    exact c.original_Z_card eK d hd
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _)) (U R d)
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,←hHindex,hH4,hU] at hmul
  have hfixedcard : Nat.card (U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) :
      Subgroup (FreeAmalgam R)) = 64 := by omega
  have hB4 : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 4 := by
    have hle := kernelCentralizer_moving_index_le geometry a d
    rw [←hHindex,hH4] at hle
    omega
  have hBmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a))
    (U R d) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hB4,hU] at hBmul
  have hBcard : Nat.card (U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) :
      Subgroup (FreeAmalgam R)) = 64 := by omega
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective (inclusion (U_le_Z d)) (inclusion_injective _)
  let : Finite (U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) :
      Subgroup (FreeAmalgam R)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hinc : U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) ≤
      U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) :=
    le_inf inf_le_left (le_centralizer_iff.mp inf_le_right)
  have heq := eq_of_le_of_card_ge hinc (by rw [hfixedcard,hBcard])
  exact Or.inr ⟨hk,hH4,hB4,heq.symm,hfixedcard,hindex,hquad⟩

/-- The literal second vertex of the critical path has the same full-kernel
alternative. This discharges the rank-one action and exact fixed-order steps
of the small branch; escape from Q and the source span argument remain. -/
theorem original_critical_small_movement_alternative
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
        (U R (path.walk.getVert 2)) ≤ 4 →
      (kernelCentralizer geometry a (path.walk.getVert 2) ≤ Q R (path.walk.getVert 2) ∧
        kernelCommutator geometry a (path.walk.getVert 2) = ⊥) ∨
      (¬ kernelCentralizer geometry a (path.walk.getVert 2) ≤ Q R (path.walk.getVert 2) ∧
        Nat.card (kernelCommutator geometry a (path.walk.getVert 2)) = 4 ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
          (U R (path.walk.getVert 2)) = 4 ∧
        U R (path.walk.getVert 2) ⊓ centralizer (kernelCentralizer geometry a (path.walk.getVert 2) : Set _) =
          U R (path.walk.getVert 2) ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) ∧
        Nat.card (U R (path.walk.getVert 2) ⊓ centralizer
          (kernelCentralizer geometry a (path.walk.getVert 2) : Set _) :
            Subgroup (FreeAmalgam R)) = 64 ∧
        (Q R (path.walk.getVert 2)).relIndex (kernelCentralizer geometry a (path.walk.getVert 2)) ≤ 4 ∧
        kernelCommutator geometry a (path.walk.getVert 2) ≤
          centralizer (kernelCentralizer geometry a (path.walk.getVert 2) : Set _)) := by
  intro R geometry hb a z path hmove
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  exact c.original_small_movement_kernel_alternative eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat hdt hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
