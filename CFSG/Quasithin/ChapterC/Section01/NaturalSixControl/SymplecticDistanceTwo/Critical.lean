module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Frattini
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Generation
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Normality

/-!
# The critical commutator in the native symplectic Frattini reduction

A normal kernel of an action that contains an element outside O₂(M) contains
the actual alternating component. This replaces the simple-SL₃ argument by
the native A₆/S₆ quotient. On the Frattini section it forces the whole core
into Phi(Q)X whenever the critical endpoint centralizes that section.
Consequently failure of the Frattini bound gives precisely the commutator
noncontainment in the first paragraph of MS93 (3.6), printed p.870.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- An escaping endpoint detects every nontrivial residual action on a
normal quotient of the original two-core. -/
theorem core_le_of_commutator_le (N E : Subgroup M) [N.Normal]
    (hE : ¬ E ≤ pCore 2 M) (hcomm : ⁅pCore 2 M,E⁆ ≤ N) :
    ⁅pCore 2 M,L⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer ((pCore 2 M).map q : Set (M ⧸ N))).comap q
  have hC (A : Subgroup M) : A ≤ C ↔ ⁅pCore 2 M,A⁆ ≤ N := by
    change A ≤ (centralizer ((pCore 2 M).map q : Set (M ⧸ N))).comap q ↔ _
    rw [← map_le_iff_le_comap, ← le_centralizer_iff,
      ← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  let : ((pCore 2 M).map q).Normal :=
    Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hEC : E ≤ C := (hC E).mpr hcomm
  exact (hC L).mp (s.residual_le_of_not_le_core C (fun h => hE (hEC.trans h)))

omit [Finite M] [L.Normal] [W.Normal] s in
/-- Pullback of a subgroup normalized by the base stabilizer is normal in M. -/
private theorem normal_comap_base (N : Subgroup (FreeAmalgam R))
    (hN : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R))) :
    (N.comap (embedM R)).Normal := by
  constructor
  intro x hx m
  change embedM R (m*x*m⁻¹) ∈ N
  rw [map_mul,map_mul,map_inv]
  apply le_normalizer_iff.mp hN _ _ _ hx
  rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
  exact ⟨m,rfl⟩

/-- A critical endpoint detects the actual Frattini section at distance two. -/
theorem core_le_frattini_of_critical_commutator_le
    (hb : s.geometry.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hcomm : ⁅Q R (alpha R),Z R c⁆ ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R) := by
  let N := (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)
  have hnn : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R)) := by
    apply (le_inf ?_ (X_normalized R (alpha R))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (Q_normalized R (alpha R)).trans (normalizer_le_normalizer_characteristic_image
      (Q R (alpha R)) (frattini (Q R (alpha R))))
  let N0 := N.comap (embedM R)
  let : N0.Normal := normal_comap_base N hnn
  let E := (Z R c).comap (embedM R)
  have hc' := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse
    R s.geometry s.edgeCentralizerCondition (alpha R) rfl
    (by change 0 < s.geometry.b R; omega) c hc' hc
  have hZ : Z R c ≤ (embedM R).range := by
    rw [← show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_two R s.geometry c hc'
    · rw [s.geometry.distance_constant c hc']
      change 0 < s.geometry.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  have hEm : E.map (embedM R) = Z R c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hE : ¬ E ≤ pCore 2 M := by
    intro h
    apply hrev.2
    rw [←hEm,Q_alpha R s.two_group s.core_le]
    exact map_mono h
  have hcomm0 : ⁅pCore 2 M,E⁆ ≤ N0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hEm,←Q_alpha R s.two_group s.core_le]
    exact hcomm
  have hcore := map_mono (f := embedM R) (s.core_le_of_commutator_le N0 E hE hcomm0)
  rw [←core_alpha R s.two_group s.core_le s.residual] at hcore
  exact hcore.trans (map_comap_le _ _)

/-- The first noncontainment used in the genuine symplectic branch of (3.6).
It is stated with the actual kernels and X-layers of the marked source. -/
theorem critical_commutator_not_le
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl)) :
    ¬ ⁅Q R (alpha R),Z R c⁆ ≤
      ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆ := by
  intro h
  apply hlarge
  apply s.core_le_frattini_of_critical_commutator_le hb hc
  apply h.trans
  apply sup_le
  · apply le_trans (commutator_mono le_rfl inf_le_right)
    apply le_trans _ le_sup_left
    let := finite_stabilizer R (alpha R)
    let : Finite (Q R (alpha R)) := Finite.of_injective
      (inclusion (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q R (alpha R))) :=
      ⟨Q_isPGroup R s.two_group s.core_le (alpha R) rfl⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  · apply le_trans _ le_sup_right
    have hc' := critical_endpoint_color R (alpha R) rfl _ hc
    have hrev := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse
      R s.geometry s.edgeCentralizerCondition (alpha R) rfl
      (by change 0 < s.geometry.b R; omega) c hc' hc
    apply le_normalizer_iff_commutator_le_left.mp
    exact (CriticalCriterion.critical_X_le_stabilizer R s.geometry s.edgeCentralizerCondition
      (by omega) c hc' (alpha R) hrev).trans (X_normalized R (alpha R))

/-- The source dichotomy retains the precise remaining branch rather than
replacing it by an unproved whole-core hypothesis. -/
theorem core_eq_moving_or_critical_noncontainment
    (hb : s.geometry.b R = 2)
    (hX : ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R)) :
    core R (alpha R) = U R (alpha R) ∨
      ∀ c, CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl) →
        ¬ ⁅Q R (alpha R),Z R c⁆ ≤
          ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆ := by
  by_cases hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)
  · exact Or.inl (s.core_eq_U_of_le_frattini_sup (alpha R) rfl hX hsmall)
  · exact Or.inr (fun _ hc => s.critical_commutator_not_le hb hsmall hc)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
