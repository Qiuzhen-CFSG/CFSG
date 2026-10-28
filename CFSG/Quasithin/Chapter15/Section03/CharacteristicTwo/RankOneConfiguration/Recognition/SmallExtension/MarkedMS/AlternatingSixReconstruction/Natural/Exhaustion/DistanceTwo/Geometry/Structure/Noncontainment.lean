module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Normality
public import Theory.Frattini.Intersection

/-!
# Failed critical comparison from the original non-Frattini hypothesis

An escaping endpoint detects residual movement on every normal section.
Critical reversal therefore turns a commutator bound on the Frattini section
into a bound on the entire graph core. Its contrapositive supplies the exact
failed comparison needed for the finite-action calculation in MS93 (3.3).

Adapted from SymplecticDistanceTwo/Critical, with normal generation in place
of a marked natural subgroup. Source: MS93 (3.6), printed p.870.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry

variable {M : Type*} [Group M] [Finite M]
omit [Finite M] in
/-- An escaping endpoint detects every nontrivial residual action on a
normal quotient of the original two-core. -/
theorem core_le_of_commutator_le_of_normal_generation
    (hnormal : ∀ (N : Subgroup M) [N.Normal],
      (¬ N ≤ pCore 2 M) → pResidual 2 M ≤ N) (N E : Subgroup M) [N.Normal]
    (hE : ¬ E ≤ pCore 2 M) (hcomm : ⁅pCore 2 M,E⁆ ≤ N) :
    ⁅pCore 2 M,pResidual 2 M⁆ ≤ N := by
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
  exact (hC (pResidual 2 M)).mp (hnormal C (fun h => hE (hEC.trans h)))

variable {R : Subgroup M} (geo : Geometry R)
  (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) (hC : EdgeCentralizerCondition R)
  (hnormal : ∀ (N : Subgroup M) [N.Normal],
    (¬ N ≤ pCore 2 M) → pResidual 2 M ≤ N)
include hp hQR hC hnormal

omit [Finite M] hp hQR hC hnormal in
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
theorem core_le_frattini_of_critical_commutator_le_of_normal_generation
    (hb : geo.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
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
    R geo hC (alpha R) rfl
    (by change 0 < geo.b R; omega) c hc' hc
  have hZ : Z R c ≤ (embedM R).range := by
    rw [← show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_two R geo c hc'
    · rw [geo.distance_constant c hc']
      change 0 < geo.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  have hEm : E.map (embedM R) = Z R c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hE : ¬ E ≤ pCore 2 M := by
    intro h
    apply hrev.2
    rw [←hEm,Q_alpha R hp hQR]
    exact map_mono h
  have hcomm0 : ⁅pCore 2 M,E⁆ ≤ N0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hEm,←Q_alpha R hp hQR]
    exact hcomm
  have hcore := map_mono (f := embedM R) (core_le_of_commutator_le_of_normal_generation hnormal N0 E hE hcomm0)
  rw [←core_alpha R hp hQR rfl] at hcore
  exact hcore.trans (map_comap_le _ _)

/-- The first noncontainment used in the genuine symplectic branch of (3.6).
It is stated with the actual kernels and X-layers of the marked source. -/
theorem critical_commutator_not_le_of_normal_generation
    (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl)) :
    ¬ ⁅Q R (alpha R),Z R c⁆ ≤
      ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆ := by
  intro h
  apply hlarge
  apply core_le_frattini_of_critical_commutator_le_of_normal_generation
    geo hp hQR hC hnormal hb hc
  apply h.trans
  apply sup_le
  · apply le_trans (commutator_mono le_rfl inf_le_right)
    apply le_trans _ le_sup_left
    let := finite_stabilizer R (alpha R)
    let : Finite (Q R (alpha R)) := Finite.of_injective
      (inclusion (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q R (alpha R))) :=
      ⟨Q_isPGroup R hp hQR (alpha R) rfl⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  · apply le_trans _ le_sup_right
    have hc' := critical_endpoint_color R (alpha R) rfl _ hc
    have hrev := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse
      R geo hC (alpha R) rfl
      (by change 0 < geo.b R; omega) c hc' hc
    apply le_normalizer_iff_commutator_le_left.mp
    exact (CriticalCriterion.critical_X_le_stabilizer R geo hC
      (by omega) c hc' (alpha R) hrev).trans (X_normalized R (alpha R))

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L T : Subgroup G}
  (h : SmallMSPair κ L T) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L T)

omit hp hQR hC hnormal in
include e hz in
/-- The precise failed source comparison on the actual replacement, retaining
the whole moved cover and the literal opposite X-layer. -/
theorem replacement_critical_commutator_not_le
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ¬ ⁅Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
      ⁅Q d.radical (alpha d.radical),X d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ⊔
        ⁅X d.radical (alpha d.radical),X d.radical c⁆ :=
  critical_commutator_not_le_of_normal_generation (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (replacement_edge_centralizer h e hz d)
    (replacement_normal_generation h e hz d) hb hlarge hc

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
