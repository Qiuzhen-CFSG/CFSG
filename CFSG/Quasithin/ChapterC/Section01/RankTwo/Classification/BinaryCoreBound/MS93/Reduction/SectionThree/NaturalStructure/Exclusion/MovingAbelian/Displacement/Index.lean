module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Intersection

/-!
# Comparing the radius image with the critical image

At a midpoint c of a critical path a--c--a', choose their common edge
vertex t. Transport the original critical pair across t from a to c.
Every M-color generator Z_e of V_a either lies in Q_c or forms a critical
pair with c whose first edge is t. The proved bad-case common-image
rigidity therefore puts every such generator in the same join X_d Q_c.
Conjugation identifies its quotient-image order with |X_a' Q_a / Q_a|.

This is the binary common-image proof of the radius-index comparison in
Meierfrankenfeld--Stellmacher (1993), (3.8), printed p.878, in the paragraph
from “Therefore V_alpha prime” through the displayed fixed-index inequality.
All three binary bad branches have the common-image property used here.
The fixed-core and intersection assumptions remain in the public contract;
the stronger common-image argument proves the comparison independently of
them. In particular, derived-radius containment is not an extra premise.
Finiteness is used only inside the actual local stabilizer.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem radius_le_critical_join (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a c : Vertex R) (ha : color R a = false) (hcColor : color R c = false)
    (hac : (cosetGraph R).dist a c = 2)
    (t : Vertex R) (hat : Adjacent R a t) (hct : Adjacent R c t)
    (d : Vertex R) (hcd : CriticalPair R c d (geometry.exists_critical c hcColor))
    (htd : (cosetGraph R).dist t d + 1 = (cosetGraph R).dist c d) :
    V R a ≤ X R d ⊔ Q R c := by
  have hfour := distance_eq_four source geometry hb hbad
  have himages := badCase_criticalImageControl source geometry (by omega) hbad
  have hta : (cosetGraph R).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
  have hct1 : (cosetGraph R).dist c t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hct)
  apply radius_le_of_m_ball ha
  intro e he hea
  by_cases heQ : Z R e ≤ Q R c
  · exact heQ.trans le_sup_right
  have hmin := criticalDistance_le R e (geometry.exists_critical e he) heQ
  have hecrit : criticalDistance R e (geometry.exists_critical e he) = 4 :=
    (geometry.distance_constant e he).trans hfour
  rw [hecrit] at hmin
  have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := a) (w := c)
  have hec : (cosetGraph R).dist e c = 4 := by omega
  have hpair : CriticalPair R e c (geometry.exists_critical e he) :=
    ⟨hec.trans hecrit.symm, heQ⟩
  have hrev := source.critical_reverse geometry e he c hcColor hpair
  have hte : (cosetGraph R).dist t e + 1 = (cosetGraph R).dist c e := by
    have h₁ := (cosetGraph_connected R).dist_triangle (u := t) (v := a) (w := e)
    have h₂ := (cosetGraph_connected R).dist_triangle (u := c) (v := t) (w := e)
    have hae : (cosetGraph R).dist a e ≤ 2 := by simpa only [SimpleGraph.dist_comm] using hea
    have hce : (cosetGraph R).dist c e = 4 := by rwa [SimpleGraph.dist_comm]
    omega
  have hj := himages.common c hcColor d hcd t hct htd e hrev hte
  have hZX := geometry.omega_bound e he (by rw [hecrit]; decide)
  exact hZX.trans (le_sup_left.trans hj.ge)

private theorem relIndex_join_of_normalizes {G : Type*} [Group G]
    (E N : Subgroup G) (hEN : E ≤ normalizer (N : Set G)) :
    N.relIndex (E ⊔ N) = N.relIndex E := by
  let := normal_subgroupOf_of_le_normalizer hEN
  let := normal_subgroupOf_sup_of_le_normalizer hEN
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).toEquiv.symm

set_option linter.unusedVariables false in
/-- The radius image modulo the midpoint kernel has order at most the actual
critical endpoint image modulo Q_a. The retained fixed-core and intersection
hypotheses match the displacement assembly contract. -/
theorem radius_index_le_critical_image (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hcColor : color R c = false)
    (hac : (cosetGraph R).dist a c = 2) (hca' : (cosetGraph R).dist c a' = 2)
    (hintersection : ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆) :
    (Q R c).relIndex (V R a) ≤ (Q R a).relIndex (X R a') := by
  have hfour := distance_eq_four source geometry hb hbad
  have hd : (cosetGraph R).dist a a' = 4 :=
    (hc.1.trans (geometry.distance_constant a ha)).trans hfour
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hac
  have hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected R).dist_triangle (u := t) (v := c) (w := a')
    omega
  obtain ⟨g, hgt, hga⟩ := stabilizer_transitive_neighbors R t
    (adjacent_symm R hat) (adjacent_symm R hct)
  have hgt' : act R g t = t := hgt
  have hcol : color R (act R g a) = false := by rw [hga]; exact hcColor
  have hcg : CriticalPair R c (act R g a') (geometry.exists_critical c hcColor) := by
    simpa only [hga] using (criticalPair_act_iff R g a a' (geometry.exists_critical a ha)
      (geometry.exists_critical (act R g a) hcol)).mpr hc
  have htg : (cosetGraph R).dist t (act R g a') + 1 =
      (cosetGraph R).dist c (act R g a') := by
    rw [← hgt', ← hga, dist_act, dist_act]
    exact hta'
  have hV := radius_le_critical_join source geometry hb hbad a c ha hcColor hac
    t hat hct (act R g a') hcg htg
  have hX : X R (act R g a') ≤ stabilizer R c :=
    critical_X_le_stabilizer source geometry (by omega) _
      (critical_endpoint_color R c hcColor _ hcg) _
      (source.critical_reverse geometry c hcColor _
        (critical_endpoint_color R c hcColor _ hcg) hcg)
  have hJ : X R (act R g a') ⊔ Q R c ≤ stabilizer R c :=
    sup_le hX (fun _ hx => hx.1)
  let := finite_stabilizer R c
  let : Finite (X R (act R g a') ⊔ Q R c : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hJ) (inclusion_injective hJ)
  calc
    (Q R c).relIndex (V R a) ≤ (Q R c).relIndex (X R (act R g a') ⊔ Q R c) :=
      relIndex_le_of_le_right hV
        ((Q R c).subgroupOf (X R (act R g a') ⊔ Q R c)).index_ne_zero_of_finite
    _ = (Q R c).relIndex (X R (act R g a')) :=
      relIndex_join_of_normalizes _ _ (hX.trans (Q_normalized R c))
    _ = (Q R a).relIndex (X R a') := by
      rw [← hga, Q_act, X_act]
      exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
