module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Edge
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal

/-!
# The actual triangle in Baumeister's coset graph

A subgroup of order 24 in A₅ × C₂ is a five-point stabilizer times C₂.
Project to A₅, use the Sylow-four normalizer to locate its order-twelve
image, and compare orders to recover the whole inverse image. A checked
five-point calculation supplies the cubic word for every involution.
Transporting that word through the actual H₃ isomorphism gives a triangle
in the source coset graph, hence completeness, degree seventeen, faithful
triple transitivity and order 8160 without any additional premise.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.7, printed p.497.
-/

@[expose] public noncomputable section
open Subgroup MulAction
namespace Sporadic.Janko3.SourceRecognition.Seventeen
abbrev A5 := alternatingGroup (Fin 5)
abbrev C2 := Multiplicative (ZMod 2)

private theorem a5_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.card_fin, Nat.factorial]

private theorem a5_twelve_stabilizer (P : Subgroup A5) (hc : Nat.card P = 12) :
    ∃ i : Fin 5, P = stabilizer A5 i := by
  let Q : Sylow 2 P := default
  have hQ : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity, hc]
    decide +kernel
  let R : Sylow 2 A5 := Sylow.ofCard ((Q : Subgroup P).map P.subtype) (by
    rw [card_map_of_injective P.subtype_injective, hQ]
    rw [a5_card]
    decide +kernel)
  have hRP : (R : Subgroup A5) ≤ P := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hp : P ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top, a5_card] at hc
    omega
  have hPN := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
    R P hRP hp
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  refine ⟨i, eq_of_le_of_card_ge (hi ▸ hPN) ?_⟩
  have hs : ∀ j : Fin 5, Nat.card (stabilizer A5 j) = 12 := by
    intro j
    rw [Nat.card_eq_fintype_card]
    revert j
    decide +kernel
  rw [hs, hc]

private theorem triangle_point_subgroup (P : Subgroup TriangleGroup) (hc : Nat.card P = 24) :
    ∃ i : Fin 5, P = (stabilizer A5 i).prod (⊤ : Subgroup C2) := by
  let Q := P.map (MonoidHom.fst A5 C2)
  have h24 : Nat.card Q ∣ 24 := hc ▸ card_map_dvd P (MonoidHom.fst A5 C2)
  have h60 : Nat.card Q ∣ 60 := by
    simpa only [a5_card] using Q.card_subgroup_dvd_card
  have h12 : Nat.card Q ∣ 12 := Nat.dvd_gcd h24 h60
  have hle : P ≤ Q.prod (⊤ : Subgroup C2) := by
    intro x hx
    exact ⟨mem_map.mpr ⟨x, hx, rfl⟩, mem_top _⟩
  have hb := card_le_of_le hle
  have h2 : Nat.card C2 = 2 := by
    norm_num [C2, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hprod : Nat.card (Q.prod (⊤ : Subgroup C2)) = Nat.card Q * Nat.card C2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv Q (⊤ : Subgroup C2)).toEquiv, Nat.card_prod]
    rw [card_top]
  rw [hprod, h2] at hb
  have hp : Nat.card Q = 12 := by
    have hu := Nat.le_of_dvd (by decide : 0 < 12) h12
    have hb' : 24 ≤ Nat.card Q * 2 := by simpa [hc] using hb
    omega
  obtain ⟨i, hi⟩ := a5_twelve_stabilizer Q hp
  refine ⟨i, eq_of_le_of_card_ge (hi ▸ hle) ?_⟩
  rw [Nat.card_congr (Subgroup.prodEquiv (stabilizer A5 i) (⊤ : Subgroup C2)).toEquiv,
    Nat.card_prod, card_top, h2, ← hi, hp, hc]


private theorem point_cube : ∀ (i : Fin 5) (b : A5), b * b = 1 →
    ∃ h : stabilizer A5 i, (b * h.val)^3 = 1 := by
  decide +kernel

theorem triangle_cube (P : Subgroup TriangleGroup) (hc : Nat.card P = 24)
    (b : TriangleGroup) (hb : b * b = 1) :
    ∃ h ∈ P, (b * h)^3 ∈ P := by
  obtain ⟨i, rfl⟩ := triangle_point_subgroup P hc
  obtain ⟨h, hcube⟩ := point_cube i b.1 (congrArg Prod.fst hb)
  refine ⟨(h.val, 1), ⟨h.property, mem_top _⟩, ?_⟩
  exact ⟨by
    change (b.1 * h.val)^3 ∈ stabilizer A5 i
    rw [hcube]
    exact mem_stabilizer_iff.mpr (by simp), mem_top _⟩

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem point_third_overlap_card : Nat.card (S.H1 ⊓ S.H3 : Subgroup G) = 24 := by
  have ha4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.card_fin, Nat.factorial]
  have hc2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  rw [Nat.card_congr S.overlap13.toEquiv, Nat.card_prod, ha4, hc2]

theorem exists_cube (b : G) (hb : b * b = 1) (hb3 : b ∈ S.H3) :
    ∃ h ∈ S.H1 ⊓ S.H3, (b * h)^3 ∈ S.H1 ⊓ S.H3 := by
  let P : Subgroup S.H3 := (S.H1 ⊓ S.H3).subgroupOf S.H3
  let Q := P.map S.triangleEquiv.toMonoidHom
  have hcP : Nat.card P = 24 := by
    change Nat.card ((S.H1 ⊓ S.H3).subgroupOf S.H3) = 24
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show S.H1 ⊓ S.H3 ≤ S.H3 from inf_le_right)).toEquiv]
    exact point_third_overlap_card S
  have hcQ : Nat.card Q = 24 := by
    rw [card_map_of_injective S.triangleEquiv.injective, hcP]
  let b3 : S.H3 := ⟨b, hb3⟩
  have hb3sq : b3 * b3 = 1 := Subtype.ext hb
  have hbmodel : S.triangleEquiv b3 * S.triangleEquiv b3 = 1 := by
    rw [← map_mul, hb3sq, map_one]
  obtain ⟨hModel, hhQ, hcube⟩ := triangle_cube Q hcQ (S.triangleEquiv b3) hbmodel
  obtain ⟨h, hhP, hhmap⟩ := Subgroup.mem_map.mp hhQ
  have heh : S.triangleEquiv h = hModel := hhmap
  have hcubeQ : S.triangleEquiv ((b3 * h)^3) ∈ Q := by
    rw [map_pow, map_mul, heh]
    exact hcube
  obtain ⟨x, hx, hmap⟩ := Subgroup.mem_map.mp hcubeQ
  have hxeq : x = (b3 * h)^3 := S.triangleEquiv.injective hmap
  have hm : (b3 * h)^3 ∈ P := hxeq ▸ hx
  exact ⟨h.val, hhP, hm⟩

/-- The complete graph conclusions, with the cubic word constructed in H₃. -/
theorem consequences
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3) :
    let D := cosetData S b hb hbout
    FaithfulSMul G (CosetGraph.Vertex D) ∧
      (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      Nat.card (CosetGraph.Vertex D) = 17 ∧
      IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧ Nat.card G = 8160 := by
  obtain ⟨h, hh, hc⟩ := S.exists_cube b hb hb3
  exact S.consequences_of_cube b hb hbout hb2 h hh.1 hc.1

/-- Lemma 2.7, including the actual graph and its faithful action. -/
theorem exists_complete_graph :
    ∃ (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1), b ∈ S.H2 ∧ b ∈ S.H3 ∧
      let D := cosetData S b hb hbout
      FaithfulSMul G (CosetGraph.Vertex D) ∧
        (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
        (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
        Nat.card (CosetGraph.Vertex D) = 17 ∧
        IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧ Nat.card G = 8160 := by
  obtain ⟨b, hb, hb2, hb3, hbout⟩ := S.exists_outside_involution
  exact ⟨b, hb, hbout, hb2, hb3, S.consequences b hb hbout hb2 hb3⟩

include S in
/-- The source hypotheses force the ambient group to have order 8160. -/
theorem group_card : Nat.card G = 8160 := by
  obtain ⟨b, hb, hbout, hb2, hb3, hf, hconn, hcomp, hval, hcard, ht, hG⟩ :=
    S.exists_complete_graph
  exact hG

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
