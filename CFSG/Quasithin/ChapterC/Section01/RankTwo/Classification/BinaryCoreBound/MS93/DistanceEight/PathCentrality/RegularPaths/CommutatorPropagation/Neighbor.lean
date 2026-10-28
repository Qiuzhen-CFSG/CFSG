module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure

/-!
# An incident edge moved by the critical endpoint

The literal marked natural action makes every nonzero invariant subgroup of
U_a equal to U_a. An incident edge commutator is nonzero and has order at
most four, whereas U_a has order eight. Its relative normalizer is therefore
proper. The simple quotient G_a/Q_a makes the normal core of that normalizer
exactly Q_a. Covariance of the incident edge commutators then shows that any
subgroup normalizing all of them lies in Q_a. Critical reversal supplies the
required nonnormalizing neighbor, without assuming regularity.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the incident-edge choice in (4.4.4)--(4.4.5), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
private theorem natural_irreducible {a : Vertex R} (model : LocalModel a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R a)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) :
    K = ⊥ ∨ K = U R a := by
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z R a).trans (Z_le_stabilizer R a)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor model.projection ⊤ ((U R a).subgroupOf S) ⊥ := {
    marking := MulEquiv.refl _
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized a g.property
    action := by
      intro g _ x y h
      exact congrArg Multiplicative.toAdd (model.action g
        ((subgroupOfEquivOfLe hUS) x) ((subgroupOfEquivOfLe hUS) y)
        (congrArg Subtype.val h)) }
  have hm : (⊤ : Subgroup S).map model.projection = ⊤ :=
    map_top_of_surjective _ model.surjective
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh

private theorem not_edge_normalized [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a t : Vertex R}
    (ha : color R a = false) (ht : Adjacent R a t) :
    ¬ stabilizer R a ≤ normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) := by
  intro hn
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a ha
  have hE := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) a t ha ht
  rcases natural_irreducible model (edgeCommutator R a t) hE hn with h | h
  · exact Escape.EdgeTransfer.edge_commutator_ne_bot (moduleFacts common) a t ha ht h
  · have he := Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) a t ha ht
    change Nat.card (edgeCommutator R a t) ≤ 4 at he
    rw [h, common.natural.card_at a ha] at he
    omega

private theorem normalCore_eq_kernel {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    (π : A →* B) (hπ : Function.Surjective π) (H : Subgroup A)
    (hker : π.ker ≤ H) (hproper : H ≠ ⊤) : H.normalCore = π.ker := by
  have hk : π.ker ≤ H.normalCore := normal_le_normalCore.mpr hker
  let : (H.normalCore.map π).Normal := H.normalCore_normal.map π hπ
  rcases (inferInstance : (H.normalCore.map π).Normal).eq_bot_or_eq_top with h | h
  · exact le_antisymm ((Subgroup.map_eq_bot_iff _).mp h) hk
  · have hh := congrArg (Subgroup.comap π) h
    rw [comap_map_eq, comap_top, sup_eq_left.mpr hk] at hh
    exact (hproper (top_unique (hh ▸ H.normalCore_le))).elim

/-- The common kernel of the incident edge-commutator action is exactly Q_a. -/
theorem le_kernel_of_normalizes_incident [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a : Vertex R} (ha : color R a = false)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ stabilizer R a)
    (hn : ∀ t, Adjacent R a t → A ≤ normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) :
    A ≤ Q R a := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a ha
  obtain ⟨k, hk⟩ := exists_mVertex_of_color R ha
  have hat : Adjacent R a (hVertex R k) := by
    rw [hk]
    simpa only [act_mVertex, act_hVertex, one_mul] using
      (adjacent_act_iff R k (mVertex R 1) (hVertex R 1)).mpr (base_adjacent R)
  let E := edgeCommutator R a (hVertex R k)
  let H := (normalizer (E : Set (FreeAmalgam R))).subgroupOf (stabilizer R a)
  have hEZ : E ≤ Z R a :=
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a _ ha hat).trans (U_le_Z R a)
  have hQN : Q R a ≤ normalizer (E : Set (FreeAmalgam R)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes a ha))).trans (centralizer_le hEZ)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hker : model.projection.ker ≤ H := by
    rw [model.kernel]
    exact subgroupOf_mono _ hQN
  have hproper : H ≠ ⊤ := by
    intro h
    exact not_edge_normalized common ha hat (subgroupOf_eq_top.mp h)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hcore := normalCore_eq_kernel model.projection model.surjective H hker hproper
  intro x hx
  have hxcore : (⟨x, hA hx⟩ : stabilizer R a) ∈ H.normalCore := by
    intro g
    change (g : FreeAmalgam R) * x * (g : FreeAmalgam R)⁻¹ ∈ normalizer (E : Set (FreeAmalgam R))
    have hga : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := g.property
    have hgt : Adjacent R a (Stellmacher.PushingUp.AmalgamGraph.act R g (hVertex R k)) := by
      simpa only [hga] using (adjacent_act_iff R (g : FreeAmalgam R) a _).mpr hat
    have hxN := hn _ hgt hx
    have hm := mem_map_of_mem (MulAut.conj (g : FreeAmalgam R)).toMonoidHom hxN
    have he : (edgeCommutator R a
        (Stellmacher.PushingUp.AmalgamGraph.act R g (hVertex R k))).map
          (MulAut.conj (g : FreeAmalgam R)).toMonoidHom = E := by
      have he := edgeCommutator_act (g : FreeAmalgam R) a (hVertex R k)
      rw [hga] at he
      rw [he, Subgroup.map_map]
      have heq : (MulAut.conj (g : FreeAmalgam R)).toMonoidHom.comp
          (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro y
        simp [mul_assoc]
      rw [heq, Subgroup.map_id]
    have hh := (le_normalizer_map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) hm
    rwa [he] at hh
  rw [hcore, model.kernel] at hxcore
  exact hxcore

/-- Every critical path admits a neighbor with the nonnormalization required
by (4.4.4). Neither regularity nor an extended path is assumed. -/
theorem exists_nonnormalizing_neighbor [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') :
    ∃ t, Adjacent R a t ∧
      ¬ Z R a' ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) := by
  classical
  by_contra! h
  have hlocal := (source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).2
  have hQ := le_kernel_of_normalizes_incident common p.start_color hlocal
    (fun t ht => (h t ht).trans inf_le_right)
  exact (common.critical_reverse a p.start_color a' p.end_color p.critical).2 hQ

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
