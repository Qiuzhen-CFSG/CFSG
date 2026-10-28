module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.QuasisimpleFrattini
public import Theory.Frattini.Intersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.CriticalPairs

/-!
# Literal critical comparisons for quasisimple core reconstruction

Pull the far critical Z-layer back along the original embedding. Critical
reversal makes it escape the two-core and positive distance makes it a
two-group. Thus the quasisimple action-kernel argument applies without
factoring out the component center. At distance two a non-Frattini core
forces exactly the failed comparison in MS93 (3.3).

Source: MS93 (3.6), first paragraph, pp.870--871. The failed-comparison
classification and the bound on critical distance remain source inputs.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

/-- Pull the local comparison back through the actual original embedding. -/
theorem original_frattini_of_embedded_comparison
    (K R : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hgen : K ⊔ R = ⊤) (hQR : pCore 2 H ≤ R)
    (E₀ : Subgroup (FreeAmalgam R)) (hEM : E₀ ≤ Mbar R)
    (hE : IsPGroup 2 E₀) (hne : ¬ E₀ ≤ Q R (alpha R))
    (hcomm : ⁅Q R (alpha R),E₀⁆ ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H) := by
  let E := E₀.comap (embedM R)
  have hEm : E.map (embedM R) = E₀ := by
    exact map_comap_eq_self (show E₀ ≤ (embedM R).range from hEM)
  apply frattini_small_of_local_comparison K R E hK hp hgen
    (hE.comap_of_injective (embedM R) (embedM_injective R)) _ _
  · intro he
    apply hne
    rw [←hEm,Q_alpha R hp hQR]
    exact map_mono he
  · apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator,hEm,Subgroup.map_sup]
    rw [X,Q_alpha R hp hQR,omegaCenter_map _ _ (embedM_injective R),
      frattini_image_map _ _ (embedM_injective R)] at hcomm
    exact hcomm

/-- The far critical layer detects the entire original component commutator. -/
theorem original_frattini_of_critical_comparison
    (K R : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hgen : K ⊔ R = ⊤) (hQR : pCore 2 H ≤ R)
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hC : EdgeCentralizerCondition R)
    (z : Vertex R) (hc : CriticalPair R (alpha R) z (geometry.exists_critical _ rfl))
    (hcomm : ⁅Q R (alpha R),Z R z⁆ ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H) := by
  have hz := critical_endpoint_color R (alpha R) rfl _ hc
  have hba : 0 < criticalDistance R (alpha R) (geometry.exists_critical _ rfl) := by
    rw [geometry.distance_constant _ rfl]; exact hb
  have hbz : 0 < criticalDistance R z (geometry.exists_critical z hz) := by
    rw [geometry.distance_constant z hz]; exact hb
  have hr := critical_reverse R geometry hC (alpha R) rfl hba z hz hc
  have hZM : Z R z ≤ Mbar R := by
    rw [←stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z hz)
    exact hr.1.le
  let := Z_elementary_of_positive R geometry z hz hbz
  exact original_frattini_of_embedded_comparison K R hK hp hgen hQR
    (Z R z) hZM (IsElementaryAbelian.isPGroup _ _) hr.2 hcomm

/-- At distance two, a large core forces the literal failed source comparison. -/
theorem critical_comparison_fails_of_nonfrattini
    (K R : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hgen : K ⊔ R = ⊤) (hQR : pCore 2 H ≤ R)
    (geometry : Geometry R) (hb : geometry.b R = 2) (hC : EdgeCentralizerCondition R)
    (z : Vertex R) (hc : CriticalPair R (alpha R) z (geometry.exists_critical _ rfl))
    (hlarge : ¬ ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    ¬ ⁅Z R z,Q R (alpha R)⁆ ≤ ⁅X R (alpha R),X R z⁆ ⊔
      ⁅X R (alpha R) ⊓ Q R z,Q R (alpha R)⁆ := by
  have hz := critical_endpoint_color R (alpha R) rfl _ hc
  have hd : (cosetGraph R).dist (alpha R) z = 2 :=
    hc.1.trans ((geometry.distance_constant _ rfl).trans hb)
  have hzero : ⁅X R (alpha R) ⊓ Q R z,Q R (alpha R)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_left.trans (le_centralizer_iff.mp (Q_le_centralizer_X R (alpha R))))
  have hXX : ⁅X R (alpha R),X R z⁆ ≤ X R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((omegaCenter_le _).trans
        ((Q_le_stabilizer_of_dist_two R z (alpha R) hz
          (by rwa [SimpleGraph.dist_comm])).trans (X_normalized R (alpha R))))
  intro h
  apply hlarge
  apply original_frattini_of_critical_comparison K R hK hp hgen hQR
    geometry (by omega) hC z hc
  rw [hzero,sup_bot_eq] at h
  rw [commutator_comm]
  exact h.trans (hXX.trans le_sup_right)

end CFSG.Quasithin.ChapterC.MSCentralOrbit
