module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionSource

/-!
# Three-core generation at the linear middle vertex

Two distinct Sylows in a finite rank-one group generate the group: a proper
join lies in the unique Sylow normalizer, whose two-subgroups lie in its
normal Sylow. On the actual reduced graph, the original full-Borel marking
identifies a base-neighbor stabilizer in the starred endpoint with its
Sylow normalizer. Consequently a Sylow fixes only one neighbor. The same
literal argument proves generation for Sylows at two distinct neighbors.

Applying this to the Chapter 8 common-Sylow images gives the three-core
identity used at the start of DGS85 p.180. The full-stabilizer version
restricts Sylows through the original subgroup inclusions. Their containment
in the starred endpoint remains explicit: on the source linear middle side
it is the preceding 6.1 identification of L_delta with G_delta*. It must
not be used to identify these two groups in the binary dihedral/Suzuki case.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.1), (12.1)(c,e) and (12.3)(b), pp.118--119, 178--180;
Aschbacher--Smith, F.1.9 for the original starred quotient and full Borel.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G]

private theorem sylow_le_normalizer_eq {A : Type*} [Group A]
    (T R : Sylow 2 A) (hR : (R : Subgroup A) ≤ normalizer (T : Set A)) : R = T := by
  have hr : (R : Subgroup A) ≤ T := by
    rw [← inf_eq_left.mpr hR, R.isPGroup'.inf_normalizer_sylow T]
    exact inf_le_right
  apply Sylow.ext
  exact (R.is_maximal' T.isPGroup' hr).symm

/-- Distinct Sylows generate a finite group with the actual rank-one core quotient. -/
theorem rankOne_sylow_pair_generates (A : Subgroup G) [Finite A]
    (hA : IsRankOneModel (A ⧸ pCore 2 A)) (T R : Sylow 2 A) (hne : T ≠ R) :
    (T : Subgroup A).map A.subtype ⊔ (R : Subgroup A).map A.subtype = A := by
  have he : (T : Subgroup A) ⊔ (R : Subgroup A) = ⊤ := by
    by_contra hn
    have hr := (rankOneSylowFacts_of_rankOneQuotient hA T).unique_maximal _
      le_sup_left (lt_top_iff_ne_top.mpr hn)
    exact hne (sylow_le_normalizer_eq T R (le_sup_right.trans hr)).symm
  rw [← Subgroup.map_sup, he, ← MonoidHom.range_eq_map, range_subtype]

private theorem sylow_unique_fixed {X : Type*} [MulAction G X]
    (A : Subgroup G) [Finite A] (T : Sylow 2 A) (x : X)
    (hstab : (MulAction.stabilizer G x).subgroupOf A = normalizer (T : Set A))
    (g : A)
    (hfix : ∀ t : A, t ∈ (T : Subgroup A) → (t : G) • ((g : G) • x) = (g : G) • x) :
    (g : G) • x = x := by
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let R : Sylow 2 A := T.mapSurjective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).surjective
  have hr : (R : Subgroup A) ≤ normalizer (T : Set A) := by
    rw [← hstab]
    intro r hr
    obtain ⟨t, ht, rfl⟩ := hr
    change (((g : G)⁻¹ * (t : G) * (g : G)⁻¹⁻¹) • x) = x
    rw [inv_inv, mul_smul, mul_smul, hfix t ht, inv_smul_smul]
  have he := sylow_le_normalizer_eq T R hr
  have hmap : (T : Subgroup A).map (MulAut.conj g⁻¹).toMonoidHom = T :=
    congrArg (fun P : Sylow 2 A => (P : Subgroup A)) he
  have hn : g⁻¹ ∈ normalizer (T : Set A) := mem_normalizer_iff_map_conj_eq.mpr hmap
  have hg : g ∈ (MulAction.stabilizer G x).subgroupOf A := by
    rw [hstab]
    simpa only [inv_inv] using (normalizer (T : Set A)).inv_mem hn
  exact hg



private theorem restrict_sylow_image (D A : Subgroup G) (hAD : A ≤ D)
    (T : Sylow 2 D) (hTA : (T : Subgroup D).map D.subtype ≤ A) :
    ∃ R : Sylow 2 A, (R : Subgroup A).map A.subtype = (T : Subgroup D).map D.subtype := by
  let f : A →* D := inclusion hAD
  have hrange : (T : Subgroup D) ≤ f.range := by
    intro t ht
    exact ⟨⟨t, hTA (mem_map_of_mem D.subtype ht)⟩, rfl⟩
  let R := T.comapOfInjective f (inclusion_injective hAD) hrange
  refine ⟨R, ?_⟩
  have he : (R : Subgroup A).map f = (T : Subgroup D) :=
    map_comap_eq_self hrange
  have hm := congrArg (Subgroup.map D.subtype) he
  rw [map_map] at hm
  exact hm

open Subgroup.CosetGeometry.RankTwo
open Reduction
namespace ReducedLayer
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem base_star_sylow_normalizer (h : HypothesisF11 L S) (i : Bool) :
    ∃ T : Sylow 2 (star L S i),
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf
        (star L S i) = normalizer (T : Set (star L S i)) := by
  let j : Fin 2 := if i then 1 else 0
  let := h.finite_parabolic j
  let d := h.starredLocalRankOneData j
  let T₀ : Sylow 2 (starredParabolic L S j) := d.sylow
  let e : star L S i ≃* starredParabolic L S j := subgroupOfEquivOfLe (star_le_completion j)
  let : Finite (starredParabolic L S j) :=
    Finite.of_injective (inclusion (starredParabolic_le j)) (inclusion_injective _)
  let T := T₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨T, ?_⟩
  have he : (T : Subgroup (star L S i)) =
      (T₀ : Subgroup (starredParabolic L S j)).comap e.toMonoidHom := by
    ext t
    change (∃ a ∈ (T₀ : Subgroup (starredParabolic L S j)), e.symm a = t) ↔
      e t ∈ (T₀ : Subgroup (starredParabolic L S j))
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro ht
      exact ⟨e t, ht, e.symm_apply_apply t⟩
  change _ = normalizer ((T : Subgroup (star L S i)) : Set (star L S i))
  rw [he, ← comap_normalizer_eq_of_surjective _ e.surjective]
  change _ = (normalizer (d.sylow : Set d.Pstar)).comap e.toMonoidHom
  rw [← source_star_borel d]
  ext t
  change (t : G₀ L S) ∈ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ↔
    ((t : G₀ L S) : G) ∈ commonBorel L S
  rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
  have hti : ((t : G₀ L S) : G) ∈ P₀ L S j :=
    (show starredParabolic L S j ≤ P₀ L S j from le_sup_left) t.property
  have hB : P₀ L S 0 ⊓ P₀ L S 1 = B₀ L S := by
    rw [P₀_eq_source h 0, P₀_eq_source h 1, B₀_eq_source h]
    exact lemma_F_1_3_6 (SuzukiContainment.reduced_hypothesis h)
  have hb : ((t : G₀ L S) : G) ∈ B₀ L S ↔
      ((t : G₀ L S) : G) ∈ commonBorel L S := by
    constructor
    · exact fun ht => B₀_le h ht
    · intro ht
      have hh : ((t : G₀ L S) : G) ∈ B₀ L S ⊓ starredParabolic L S j := by
        rw [B₀_inf_star h j]
        exact ⟨ht, t.property⟩
      exact hh.1
  rw [← hb, ← hB]
  cases i
  · change _ ∈ (P₀ L S 1).subgroupOf (G₀ L S) ↔ _ ∈ P₀ L S 0 ⊓ P₀ L S 1
    exact ⟨fun ht => ⟨hti, ht⟩, fun ht => ht.2⟩
  · change _ ∈ (P₀ L S 0).subgroupOf (G₀ L S) ↔ _ ∈ P₀ L S 0 ⊓ P₀ L S 1
    exact ⟨fun ht => ⟨ht, hti⟩, fun ht => ht.1⟩

/-- Distinct neighboring point stabilizers contain distinct starred Sylows,
which generate the whole actual starred endpoint. -/
theorem star_sylow_pair_generates (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype ≤
      stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype ≤
      stabilizer (reducedFamily L S) y) :
    (T : Subgroup (star L S i)).map (star L S i).subtype ⊔
      (R : Subgroup (star L S i)).map (star L S i).subtype = star L S i := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (star L S i) := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  apply rankOne_sylow_pair_generates _
    ((h.quotient (if i then 1 else 0)).of_equiv (originalQuotient h i).symm)
  intro he
  obtain ⟨T₀, hT₀⟩ := base_star_sylow_normalizer h i
  have hTT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [← hT₀]
    exact fun t ht => hT (mem_map_of_mem (star L S i).subtype ht))
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g, hg, hgy⟩ := star_locally_transitive h i hadj hy
  have hfixed := sylow_unique_fixed (star L S i) T₀ (base F (!i)) hT₀ ⟨g, hg⟩ (by
    intro t ht
    rw [hgy]
    apply hR
    exact mem_map_of_mem (star L S i).subtype (by rwa [← he, hTT]))
  exact hne (hgy.symm.trans hfixed)

/-- The p.180 three-core generation identity, proved from the actual common
Sylow markings rather than assumed as a generation equation. -/
theorem star_three_core_generation (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
      Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    star L S i = (Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
      Q (reducedFamily L S) y) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have he := star_sylow_pair_generates h i hy hne T R (by
    rw [hT]
    exact sup_le (Q_le_stabilizer F _) ((hQU _).trans
      ((ballKernel_one_le_edge F hadj).trans inf_le_right))) (by
    rw [hR]
    exact sup_le (Q_le_stabilizer F _) ((hQU _).trans
      ((ballKernel_one_le_edge F hy).trans inf_le_right)))
  rw [hT, hR] at he
  simpa only [sup_assoc, sup_left_comm, sup_comm, sup_idem, sup_left_idem] using he.symm


/-- Restriction retains the literal full-stabilizer Sylows and their core images.
Their placement in the starred endpoint is the earlier linear-side 6.1 input. -/
theorem star_three_core_generation_of_full_sylows (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hT : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTS : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hRS : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i) :
    star L S i = (Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
      Q (reducedFamily L S) y) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  obtain ⟨T', hT'⟩ := restrict_sylow_image _ _ (star_le_stabilizer i) T hTS
  obtain ⟨R', hR'⟩ := restrict_sylow_image _ _ (star_le_stabilizer i) R hRS
  exact star_three_core_generation h i hy hne T' R' (hT'.trans hT) (hR'.trans hR)

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
