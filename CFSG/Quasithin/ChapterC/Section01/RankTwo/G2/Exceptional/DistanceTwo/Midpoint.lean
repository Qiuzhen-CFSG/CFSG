module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.Reduction

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The auxiliary subgroup is fixed by the midpoint residual

Normality at the second vertex makes the local centralizer normal there.
The starting kernel centralizes the auxiliary subgroup and escapes the
midpoint kernel: otherwise equal kernel orders contradict criticality.
Conjugate generation and the two-group edge supplement then put the entire
midpoint two-residual in that centralizer. This proves the fixed-subgroup
containment in the second paragraph of MS93 (3.8), printed p.878, conditional
only on its preceding local module estimates.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.G2Exceptional
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NormalizerTransfer
namespace Reconstruction.DistanceTwo
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h

private theorem kernel_card (a : Vertex T) (ha : color T a = false) :
    Nat.card (Q T a) = Nat.card (pCore 2 (L ⊔ R : Subgroup G)) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color T ha
  have hh := Q_act T g (alpha T)
  simp only [alpha, act_mVertex, one_mul] at hh
  rw [hh, ← Nat.card_congr ((Q T (mVertex T 1)).equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv]
  change Nat.card (Q T (alpha T)) = _
  rw [Q_alpha T (edge_two_group h) (core_le_edge h)]
  exact (Nat.card_congr ((pCore 2 (L ⊔ R : Subgroup G)).equivMapOfInjective
    (embedM T) (embedM_injective T)).toEquiv).symm

include e in
private theorem kernel_not_le_midpoint (hb : 2 < (geometry h).b T)
    (a : Vertex T) (ha : color T a = false) (a' : Vertex T)
    (hc : CriticalPair T a a' ((geometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hca' : (cosetGraph T).dist c a' = 2) : ¬ Q T a ≤ Q T c := by
  intro hle
  let := finite_stabilizer T c
  let : Finite (Q T c) := Finite.of_injective
    (inclusion (show Q T c ≤ stabilizer T c from fun _ hx => hx.1)) (inclusion_injective _)
  have heq : Q T a = Q T c := eq_of_le_of_card_ge hle (by
    rw [kernel_card h a ha, kernel_card h c hcColor])
  have hZX : Z T a ≤ X T a := (geometry h).omega_bound a ha (by
    rw [(geometry h).distance_constant a ha]
    change 0 < (geometry h).b T
    omega)
  have hX : X T a = X T c := congrArg omegaCenter heq
  have hcQ := X_le_Q_of_dist_lt T (geometry h) (edgeCentralizer h e) c hcColor a' (by
    rw [(geometry h).distance_constant c hcColor]
    change _ < (geometry h).b T
    omega)
  exact hc.2 (hZX.trans (hX.le.trans hcQ))

include e in
/-- The auxiliary subgroup from source (2.3)(d) lies in the actual fixed
part D_c of the midpoint kernel, not just in its stabilizer. -/
theorem auxiliary_le_fixed_midpoint (hb : 2 < (geometry h).b T)
    (hloc : LocalControl h)
    (a : Vertex T) (ha : color T a = false) (a' : Vertex T)
    (hc : CriticalPair T a a' ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hca' : (cosetGraph T).dist c a' = 2)
    (A : Subgroup (FreeAmalgam T))
    (hA : CriticalCriterion.EdgeWitness T (geometry h) a t A) : A ≤ fixedCore T c := by
  let S := stabilizer T c
  have hfour := distance_four_of_localControl h e hb hloc
  have hd : (cosetGraph T).dist a a' = 4 :=
    (hc.1.trans ((geometry h).distance_constant a ha)).trans hfour
  obtain ⟨hAS, hAn⟩ := CriticalCriterion.FromCentralizer.normal_at_second T
    (edgeCentralizer h e) (geometry h) hb (generation h e) hloc.commutator
    a ha a' hc t c hat hct hac (by omega) A hA
  have hAQ : A ≤ Q T c := hA.le_X.trans
    (X_le_Q_of_dist_lt T (geometry h) (edgeCentralizer h e) a ha c (by
      rw [(geometry h).distance_constant a ha]
      change _ < (geometry h).b T
      omega))
  let C₀ := S ⊓ centralizer (A : Set (FreeAmalgam T))
  have hCn : (C₀.subgroupOf S).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((((normal_subgroupOf_iff_le_normalizer hAS).mp hAn).trans
          (normalizer_le_normalizer_centralizer A)) hg)]
  have hQC : Q T a ≤ C₀ := le_inf
    (Q_le_stabilizer_of_dist_two T a c ha hac)
    ((Q_le_centralizer_X T a).trans (centralizer_le hA.le_X))
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    cases he : color T t <;> simp_all
  have hQT : Q T a ≤ Q T t := Q_le_adjacent_h T ht hat
  have hTS : Q T t ≤ S := CriticalCriterion.edge_le_stabilizer T hcColor hct
  have hgen := CriticalCriterion.Generation.of_subgroup T (generation h e) hcColor hct
    hQT (kernel_not_le_midpoint h e hb a ha a' hc c hcColor hca')
  have hspan : conjugatesIn (Q T a) S ≤ C₀ := by
    apply iSup_le
    intro g
    exact (map_mono hQC).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (((normal_subgroupOf_iff_le_normalizer inf_le_left).mp hCn)
          (S.inv_mem g.property))).le
  have hgenC : C₀ ⊔ Q T t = S := le_antisymm (sup_le inf_le_left hTS)
    (hgen.ge.trans (sup_le_sup hspan le_rfl))
  let N := C₀.subgroupOf S
  let E := (Q T t).subgroupOf S
  let : N.Normal := hCn
  have htop : N ⊔ E = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show C₀ ≤ S from inf_le_left),
      map_subgroupOf_eq_of_le hTS, ← MonoidHom.range_eq_map, range_subtype]
    exact hgenC
  have hp : IsPGroup 2 (Q T t) := by
    obtain ⟨g, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common T a t).mp hat
    · have hh := Q_act T g (beta T)
      simp only [beta, act_hVertex, one_mul] at hh
      rw [hh, show Q T (hVertex T 1) = (T).map (embedM T) from Q_beta T]
      exact ((edge_two_group h).map _).map _
    · cases ha
  have hr : pResidual 2 S ≤ N :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N E hp.comap_subtype htop⟩
  have hLC : Ltilde T c ≤ C₀ := by
    have hh := map_mono (f := S.subtype) hr
    rwa [map_subgroupOf_eq_of_le (show C₀ ≤ S from inf_le_left)] at hh
  exact le_inf hAQ (le_centralizer_iff.mp (hLC.trans inf_le_right))

end Reconstruction.DistanceTwo
end CFSG.Quasithin.ChapterC.G2Exceptional
