module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Normality
/-!
# The critical distance is four

Suppose b > 4. First escape moves the given edge witness without normalizing
it and extends the critical path two steps backwards. Reverse nonnormality,
using the escape already proved from (b)--(c), allows a second extension.
The transported witness lies in the X-layer four steps before the original
endpoint, so it centralizes the witness from (c). Normality at the second
vertex makes the second conjugation fix that subgroup, contradicting the
first escape. Evenness and b > 2 then give b = 4.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3), last paragraph of the
proof on printed pp.858--859. No later escape or representation result is
used.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

private theorem edge_not_normal {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) {a a' t : Vertex R} (ha : color R a = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (hat : Adjacent R a t) (ht : (cosetGraph R).dist t a' + 1 = geometry.b R)
    {W : Subgroup (FreeAmalgam R)} (hW : CommutatorWitness R a a' W) :
    ¬ ((Q R t).subgroupOf (stabilizer R a)).Normal := by
  intro hn
  have ha' := critical_endpoint_color R a ha _ hc
  apply hW.not_le_Q
  have hWT : W ≤ Q R t := hW.le_X.trans
    (X_le_Q_of_dist_lt R geometry (source.edgeCentralizerCondition geometry) a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      change (cosetGraph R).dist t a' < geometry.b R
      omega))
  exact hWT.trans (le_Q_of_normal_edge R a t hat (Q R t)
    (le_inf (edge_le_stabilizer R ha hat) (fun _ hx => hx.1)) hn)

private theorem rightConjugate_cancel {G : Type*} [Group G] (A : Subgroup G) (f : G) :
    rightConjugate (rightConjugate A f) f⁻¹ = A := by
  rw [rightConjugate, rightConjugate, map_map]
  have heq : (MulAut.conj (f⁻¹)⁻¹).toMonoidHom.comp (MulAut.conj f⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [heq, map_id]

/-- A conjugate normal in an overgroup containing the conjugating element
is equal to the original subgroup. No ambient normality is asserted. -/
private theorem rightConjugate_eq_of_normal {G : Type*} [Group G]
    (A K : Subgroup G) (f : G) (hf : f ∈ K)
    (hAK : rightConjugate A f ≤ K)
    (hn : ((rightConjugate A f).subgroupOf K).Normal) : rightConjugate A f = A := by
  have hnorm := (normal_subgroupOf_iff_le_normalizer hAK).mp hn
  have heq : rightConjugate (rightConjugate A f) f⁻¹ = rightConjugate A f :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm (K.inv_mem (K.inv_mem hf)))
  rw [rightConjugate_cancel] at heq
  exact heq.symm

/-- The last paragraph of source (2.3): two applications of step (2), and
normality at the second vertex, exclude critical distance greater than four. -/
theorem distance_eq_four {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a')
    (A : Subgroup (FreeAmalgam R)) (hA : EdgeWitness R geometry a t A) :
    geometry.b R = 4 := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hfour : 4 ≤ geometry.b R := by obtain ⟨k, hk⟩ := heven; omega
  apply Nat.le_antisymm _ hfour
  by_contra hgt
  have hlarge : 4 < geometry.b R := by omega
  have hpos : 0 < geometry.b R := by omega
  have hC := source.edgeCentralizerCondition geometry
  have hdist : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨e, hea', hae⟩ := exists_two_before R a a' (by omega)
  obtain ⟨d₀, hd₀t, hd₀a, hnot⟩ := exists_nonnormal_neighbor R source geometry hb a ha a' hc
    t hat hta'
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  obtain ⟨g, hg, hd, hpair, hescape⟩ := escape_pair R source geometry hb hgen a ha a' hc
    t hat hta' e hea' hae d₀ hd₀t hd₀a hnot A (hA.le_edge R ha hat)
    hA.normal_edge hA.not_normal_vertex W hW
  let d := act R g d₀
  let s := act R g t
  have hfix : act R g a = a := hg
  have hB : EdgeWitness R geometry a s (rightConjugate A g) := by
    have hh := hA.conjugate R ha hat g
    rwa [hfix] at hh
  have hds : Adjacent R d s := (adjacent_act_iff R g d₀ t).mpr hd₀t
  have has : Adjacent R a s := by
    rw [← hfix]
    exact (adjacent_act_iff R g a t).mpr hat
  have hda : (cosetGraph R).dist d a = 2 := by
    change (cosetGraph R).dist (act R g d₀) a = 2
    rw [← hfix, dist_act]
    exact hd₀a
  have hde : (cosetGraph R).dist d e = geometry.b R :=
    hpair.1.trans (geometry.distance_constant d hd)
  have hse : (cosetGraph R).dist s e + 1 = geometry.b R :=
    moved_edge_on_path R geometry hat hd₀t (by omega) g hg hd hpair
  have hrev := critical_nonnormal_reverse R geometry hC (criticalEscape R source geometry hb hgen hcomm)
    d hd (by rw [geometry.distance_constant d hd]; exact hpos) hpair a hda (by omega)
  obtain ⟨j, hje, haj⟩ := exists_two_before R a e (by omega)
  have hdj : (cosetGraph R).dist d j + 2 = (cosetGraph R).dist d e := by
    have hu := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := j)
    have hl := (cosetGraph_connected R).dist_triangle (u := d) (v := j) (w := e)
    omega
  have hja' : (cosetGraph R).dist j a' = 4 := by
    have hu := (cosetGraph_connected R).dist_triangle (u := j) (v := e) (w := a')
    have hl := (cosetGraph_connected R).dist_triangle (u := a) (v := j) (w := a')
    omega
  obtain ⟨W₂, hW₂⟩ := hcomm d hd e hpair
  obtain ⟨f, hf, haf, hpair₂, _⟩ := escape_pair R source geometry hb hgen d hd e hpair
    s hds (by omega) j hje hdj a has (by rwa [SimpleGraph.dist_comm]) hrev.2
    (Q R s) le_rfl (normal_subgroupOf_of_le_normalizer (Q R s).le_normalizer)
    (edge_not_normal R source geometry hd hpair hds hse hW₂) W₂ hW₂
  have hBf := hB.conjugate R ha has f
  have hsj : (cosetGraph R).dist (act R f s) j + 1 = geometry.b R :=
    moved_edge_on_path R geometry hds has (by omega) f hf haf hpair₂
  have hsmall := hBf.le_far_X R hC hpos haf j hpair₂ hsj
  have hjcol := critical_endpoint_color R _ haf _ hpair₂
  have hXj : X R j ≤ Q R a' := X_le_Q_of_dist_lt R geometry hC j hjcol a' (by
    rw [geometry.distance_constant j hjcol]
    change (cosetGraph R).dist j a' < geometry.b R
    omega)
  have hfd : act R f d = d := hf
  have hdsf : Adjacent R d (act R f s) := by
    rw [← hfd]
    exact (adjacent_act_iff R f d s).mpr hds
  have hafs : Adjacent R (act R f a) (act R f s) := (adjacent_act_iff R f a s).mpr has
  have hafd : (cosetGraph R).dist (act R f a) d = 2 := by
    calc
      _ = (cosetGraph R).dist (act R f a) (act R f d) := congrArg _ hfd.symm
      _ = (cosetGraph R).dist a d := dist_act R f a d
      _ = 2 := by rwa [SimpleGraph.dist_comm]
  have hpair₂dist : (cosetGraph R).dist (act R f a) j = geometry.b R :=
    hpair₂.1.trans (geometry.distance_constant _ haf)
  have hnormal := normal_at_second R source geometry hb hgen hcomm
    (act R f a) haf j hpair₂ (act R f s) d hafs hdsf hafd (by omega)
    (rightConjugate (rightConjugate A g) f) hBf
  have hBeq := rightConjugate_eq_of_normal (rightConjugate A g) (stabilizer R d) f hf
    hnormal.1 hnormal.2
  apply hescape
  rw [← hBeq]
  exact le_normalizer_of_le_Q R (hsmall.trans hXj) hW.le_X

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
