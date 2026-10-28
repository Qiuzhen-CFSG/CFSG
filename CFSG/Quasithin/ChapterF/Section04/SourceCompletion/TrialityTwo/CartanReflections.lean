module
public import Theory.GroupAction.HexagonReflections.Normalized
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.MiddleConjugation
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Reflections

/-!
# A common order-seven subgroup for the marked reflection pair

The pointwise apartment fixer equals the seven-path fixer and has order
seven. Lift the two cycle reflections while retaining normalization of this
same subgroup. Pull it back through the original middle map; injectivity
and the two commuting squares transport normalization to the native model.
Thus the actual order-six pair has native preimages normalizing one common
subgroup of the full Borel. A single Borel conjugation aligns it with the
fixed native torus, with no change to the endpoint markings.

This supplies the common subgroup for the remaining binary comparison.
It does not assert the native sixth-power relation: torus normalization
alone does not establish it at q = 2.
Source: Aschbacher--Smith F.4.15--17, printed pp.281--283.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open GroupAction.HexagonReflections
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] (c : Completion G)

/-- The whole apartment fixer has order seven, on the original base edge. -/
theorem cycleFixer_card
    (f : cycleGraph 12 →g c.graph) (hf : Function.Injective f)
    (h0 : f 0 = RankTwo.base c.family false) :
    Nat.card (cycleFixer (G := G) f) = 7 := by
  let p := BasedWalk.rebase h0 (arc f 0 7)
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_rebase _ _).mpr
    (arc_nonbacktracking f hf _ _)
  have he : cycleFixer (G := G) f = pathStabilizer c.family p := by
    ext g
    rw [mem_cycleFixer_iff_seven c.graphAction c.cycle_length_ge_twelve f hf]
    change (∀ i : Fin 8, _) ↔ ∀ v ∈ p.vertices, g • v = v
    simp only [p, BasedWalk.vertices_rebase, arc_vertices, zero_add,
      List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  rw [he]
  exact c.seven_fixer_card p hp

private theorem normalizes_map_iff {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (Q : Subgroup A) (x : A) :
    f x ∈ normalizer (Q.map f : Set B) ↔ x ∈ normalizer (Q : Set A) := by
  change x ∈ (normalizer (Q.map f : Set B)).comap f ↔ _
  rw [comap_normalizer_eq_of_le_range (Subgroup.map_le_range f Q),
    comap_map_eq_self_of_injective hf]

/-- Normalization of a subgroup of the whole marked Borel is independent
of the completion, through its literal left inclusion. -/
theorem left_normalizes_middle_iff {H : Type*} [Group H] (d : Completion H)
    (Q : Subgroup (borel parameters)) (s : parabolic parameters .arms) :
    c.left s ∈ normalizer (Q.map c.middle : Set G) ↔
      d.left s ∈ normalizer (Q.map d.middle : Set H) := by
  have hc : Q.map c.middle = (Q.map amalgam.left).map c.left := (Subgroup.map_map _ _ _).symm
  have hd : Q.map d.middle = (Q.map amalgam.left).map d.left := (Subgroup.map_map _ _ _).symm
  rw [hc,hd,normalizes_map_iff _ c.left_injective,normalizes_map_iff _ d.left_injective]

/-- The same normalization transfer uses the right commuting square. -/
theorem right_normalizes_middle_iff {H : Type*} [Group H] (d : Completion H)
    (Q : Subgroup (borel parameters)) (t : parabolic parameters .central) :
    c.right t ∈ normalizer (Q.map c.middle : Set G) ↔
      d.right t ∈ normalizer (Q.map d.middle : Set H) := by
  have hc : Q.map c.middle = (Q.map amalgam.right).map c.right := by
    rw [Subgroup.map_map, ← c.compatible]
  have hd : Q.map d.middle = (Q.map amalgam.right).map d.right := by
    rw [Subgroup.map_map, ← d.compatible]
  rw [hc,hd,normalizes_map_iff _ c.right_injective,normalizes_map_iff _ d.right_injective]

variable [Finite G]

/-- The actual order-six pair normalizes one common subgroup of order seven,
both here and in the native model, with exactly the same marked preimages. -/
theorem exists_normalizing_endpoint_involutions_of_order_bound
    (horder : Nat.card G ≤ Nat.card Model) :
    ∃ Q : Subgroup (borel parameters), Nat.card Q = 7 ∧
      ∃ s : parabolic parameters .arms, ∃ t : parabolic parameters .central,
        s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
          (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
          c.left s ∈ normalizer (Q.map c.middle : Set G) ∧
          c.right t ∈ normalizer (Q.map c.middle : Set G) ∧
          modelCompletion.left s ∈ normalizer (Q.map modelCompletion.middle : Set Model) ∧
          modelCompletion.right t ∈ normalizer (Q.map modelCompletion.middle : Set Model) := by
  obtain ⟨f,hf,h0,h1⟩ := c.exists_cycle_on_base_edge
    (c.exists_twelve_cycle_of_order_bound horder)
  let Q := cycleFixer (G := G) f
  have hQ : Nat.card Q = 7 := c.cycleFixer_card f hf h0
  obtain ⟨s,t,hs,ht,hst,hs0,hs1,ht1,ht0,hsQ,htQ⟩ :=
    exists_normalizing_reflections c.graphAction c.cycle_length_ge_twelve
      c.seven_transitive f hf (by rw [hQ]; decide)
  have hQB : Q ≤ c.middle.range := by
    intro x hx
    rw [← c.overlap]
    have hh := (mem_cycleFixer f x).mp hx
    have hx0 := hh 0
    have hx1 := hh 1
    rw [h0] at hx0
    rw [h1] at hx1
    constructor
    · change x ∈ c.left.range
      change x ∈ MulAction.stabilizer G (RankTwo.base c.family false) at hx0
      simpa only [RankTwo.base, stabilizer_base, family_false] using hx0
    · change x ∈ c.right.range
      change x ∈ MulAction.stabilizer G (RankTwo.base c.family true) at hx1
      simpa only [RankTwo.base, stabilizer_base, family_true] using hx1
  let R := Q.comap c.middle
  have hR : R.map c.middle = Q := map_comap_eq_self hQB
  have hRcard : Nat.card R = 7 := by
    rw [← card_map_of_injective c.middle_injective, hR, hQ]
  rw [h0] at hs0 ht0
  rw [h1] at hs1 ht1
  have hprod : orderOf (s*t)=6 := GroupAction.DihedralPolygon.edge_exponent_eq
    c.bipartiteAction c.uniqueGeodesicsBelow_six (orderOf_pos (s*t))
    (Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hst))
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs ht hs0 hs1 ht1 ht0
    (by rw [pow_orderOf_eq_one,one_smul]) (by rw [pow_orderOf_eq_one,one_smul])
  have hsf : s∈c.left.range := by
    have h : s∈MulAction.stabilizer G (RankTwo.base c.family false) := hs0
    simpa only [RankTwo.base,stabilizer_base,family_false] using h
  have htf : t∈c.right.range := by
    have h : t∈MulAction.stabilizer G (RankTwo.base c.family true) := ht1
    simpa only [RankTwo.base,stabilizer_base,family_true] using h
  obtain ⟨a,rfl⟩ := hsf
  obtain ⟨b,rfl⟩ := htf
  have haR : c.left a ∈ normalizer (R.map c.middle : Set G) := hR.symm ▸ hsQ
  have hbR : c.right b ∈ normalizer (R.map c.middle : Set G) := hR.symm ▸ htQ
  refine ⟨R,hRcard,a,b,c.left_injective ?_,c.right_injective ?_,?_,?_,hst,hprod,
    haR,hbR,(c.left_normalizes_middle_iff modelCompletion R a).mp haR,
    (c.right_normalizes_middle_iff modelCompletion R b).mp hbR⟩
  · rw [map_pow,hs,map_one]
  · rw [map_pow,ht,map_one]
  · intro h
    apply hs1
    have hmem := c.middle_le_right h
    change c.left a∈MulAction.stabilizer G (RankTwo.base c.family true)
    simpa only [RankTwo.base,stabilizer_base,family_true] using hmem
  · intro h
    apply ht0
    have hmem := c.middle_le_left h
    change c.right b∈MulAction.stabilizer G (RankTwo.base c.family false)
    simpa only [RankTwo.base,stabilizer_base,family_false] using hmem

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion

open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat

/-- The literal native torus inside the full marked Borel. -/
abbrev borelTorus : Subgroup (borel parameters) :=
  (torus parameters).subgroupOf (borel parameters)

theorem borelTorus_card : Nat.card borelTorus = 7 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel parameters)).toEquiv]
  exact TorusCoordinates.card_torus parameters parameters_prime

/-- Borel conjugacy aligns the actual cycle fixer with the native torus. -/
theorem exists_borel_conjugate_eq_torus (Q : Subgroup (borel parameters))
    (hQ : Nat.card Q = 7) :
    ∃ b : borel parameters, Q.map (MulAut.conj b).toMonoidHom = borelTorus := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have sylow (R : Subgroup (borel parameters)) (hR : Nat.card R = 7) :
      ∃ S : Sylow 7 (borel parameters), (S : Subgroup (borel parameters)) = R := by
    have hp : IsPGroup 7 R := IsPGroup.of_card (show Nat.card R = 7^1 by simpa only [pow_one] using hR)
    have hi : ¬ 7 ∣ R.index := by
      have h := R.card_mul_index
      rw [hR, borel_card] at h
      have hidx : R.index = 4096 := by omega
      rw [hidx]
      decide
    exact ⟨hp.toSylow hi, rfl⟩
  obtain ⟨S,hS⟩ := sylow Q hQ
  obtain ⟨R,hR⟩ := sylow borelTorus borelTorus_card
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq (borel parameters) S R
  refine ⟨b,?_⟩
  have hh := congrArg Sylow.toSubgroup hb
  change (S : Subgroup (borel parameters)).map (MulAut.conj b).toMonoidHom =
    (R : Subgroup (borel parameters)) at hh
  simpa only [hS,hR] using hh

variable {G : Type*} [Group G] (c : Completion G)

variable [Finite G]

/-- The pair may be chosen to normalize the fixed native torus. The single
Borel conjugation is made in both endpoints, so the actual relation and
all original markings are preserved. -/
private theorem exists_actual_torus_pair
    (horder : Nat.card G ≤ Nat.card Model) :
    ∃ s : parabolic parameters .arms, ∃ t : parabolic parameters .central,
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
        c.left s ∈ normalizer (borelTorus.map c.middle : Set G) ∧
        c.right t ∈ normalizer (borelTorus.map c.middle : Set G) := by
  obtain ⟨Q,hQ,s,t,hs,ht,hsout,htout,hpow,horderst,hsQ,htQ,_,_⟩ :=
    c.exists_normalizing_endpoint_involutions_of_order_bound horder
  obtain ⟨b,hb⟩ := exists_borel_conjugate_eq_torus Q hQ
  obtain ⟨s',t',hs',ht',hsout',htout',hpow',ho',hsQ',htQ'⟩ :=
    c.conjugate_endpoint_pair Q b s t 6 hs ht hsout htout hpow hsQ htQ
  rw [hb] at hsQ' htQ'
  exact ⟨s',t',hs',ht',hsout',htout',hpow',ho'.trans horderst,hsQ',htQ'⟩

private theorem borelTorus_model_map :
    borelTorus.map modelCompletion.middle = torus parameters := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x,torus_le_borel parameters hx⟩,hx,rfl⟩

/-- Both members of an actual order-six pair normalize the fixed native
Cartan under the same endpoint markings. -/
theorem exists_torus_normalizing_endpoint_involutions_of_order_bound
    (horder : Nat.card G ≤ Nat.card Model) :
    ∃ s : parabolic parameters .arms, ∃ t : parabolic parameters .central,
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
        c.left s ∈ normalizer (borelTorus.map c.middle : Set G) ∧
        c.right t ∈ normalizer (borelTorus.map c.middle : Set G) ∧
        modelCompletion.left s ∈ normalizer (torus parameters : Set Model) ∧
        modelCompletion.right t ∈ normalizer (torus parameters : Set Model) := by
  obtain ⟨s,t,hs,ht,hsout,htout,hpow,ho,hsN,htN⟩ := c.exists_actual_torus_pair horder
  refine ⟨s,t,hs,ht,hsout,htout,hpow,ho,hsN,htN,?_,?_⟩
  · rw [←borelTorus_model_map]
    exact (c.left_normalizes_middle_iff modelCompletion borelTorus s).mp hsN
  · rw [←borelTorus_model_map]
    exact (c.right_normalizes_middle_iff modelCompletion borelTorus t).mp htN

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
