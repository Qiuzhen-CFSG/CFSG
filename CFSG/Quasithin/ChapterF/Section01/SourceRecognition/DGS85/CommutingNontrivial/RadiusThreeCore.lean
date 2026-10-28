module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions

/-!
# The complete predecessor-core containment in DGS 8.4(1)

The escaping case of the radius-three configuration puts an adjacent-core
intersection in a third core. In the linear, Suzuki and unitary models,
the marked edge action propagates this containment to every neighbor.
The intersection is then normal in the full vertex stabilizer, contradicting
the original 6.5 obstruction.

For D₁₀, the escaping neighboring core already fills the quotient Sylow.
Proper-overgroup uniqueness traps X in the edge unless its quotient image
is full. A full image gives the same core conjugate span inside X, contrary
to the original core-span obstruction, since that core is a Sylow of X.
Thus the whole W = V_beta^(3) lies in Q_(alpha'-1), for every source model.
No elementary-W hypothesis or transitivity callback is used.

Source: DGS, *Groups and Graphs* (1985), 6.5 and 8.4(1), printed pp.121,137.
`RadiusThreeOmega` applies the result to the original marked Sylow and
reduced F1.11 configuration. The remaining parts of 8.4--8.7 are separate.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- In a locally doubly transitive source action, containment of one adjacent
core intersection in a third core contradicts the original 6.5 obstruction.
The conclusion uses normality in the full vertex stabilizer. -/
theorem source_core_intersection_not_le_third
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (_hvz : (graph (family P)).Adj v z) (_hzw : z ≠ w)
    (hob : ¬ stabilizer (family P) v ≤ normalizer
      ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (ht : ∀ y : Vertex (family P), (graph (family P)).Adj v y → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • z = y) :
    ¬ Q (family P) w ⊓ Q (family P) v ≤ Q (family P) z := by
  let F := family P
  let K := Q F w ⊓ Q F v
  intro hK
  have hall (y : Vertex F) (hy : (graph F).Adj v y) : K ≤ Q F y := by
    by_cases he : y = w
    · exact he ▸ inf_le_left
    obtain ⟨g,hg,hgy⟩ := ht y hy he
    have hv : g • v = v := d.local_le v hg.1
    have hw : g • w = w := hg.2
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hK
    rwa [map_inf _ _ _ (MulAut.conj g).injective, ← Q_translate, ← Q_translate,
      ← Q_translate, hv, hw, hgy] at hm
  apply hob
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hg' : g⁻¹ • v = v := (stabilizer F v).inv_mem hg
  have hback : (graph F).Adj v (g⁻¹ • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hvw
    change (graph F).Adj (g⁻¹ • v) (g⁻¹ • w) at hh
    rwa [hg'] at hh
  have hxw : g * x * g⁻¹ ∈ Q F w := by
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom (hall _ hback hx)
    rwa [← Q_translate, smul_inv_smul] at hm
  exact ⟨hxw,(le_normalizer_iff.mp (stabilizer_normalizes_Q F v) g hg x hx.2)⟩

private theorem source_core_sylow_not_full_image (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (X : Subgroup G) (_hXL : X ≤ d.localGroup v)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = Q (family P) w) :
    (X.subgroupOf (d.localGroup v)).map
      (QuotientGroup.mk' (pCore 2 (d.localGroup v))) ≠ ⊤ := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let q := QuotientGroup.mk' (pCore 2 L)
  let C := conjugateSpanBy (Q F w) L
  have hQX : Q F w ≤ X := hS ▸ map_subtype_le _
  have hQn : Q F v ≤ normalizer (Q F w : Set G) :=
    ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F hvw).trans inf_le_right)).trans
      (stabilizer_normalizes_Q F w)
  intro hfull
  have hCX : C ≤ X := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,x,hx,rfl⟩
    have hm : q ⟨g,hg⟩ ∈ (X.subgroupOf L).map q := hfull.symm ▸ mem_top _
    obtain ⟨y,hy,he⟩ := hm
    have hk : (y : G)⁻¹ * g ∈ Q F v := by
      have hk' : y⁻¹ * ⟨g,hg⟩ ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (y⁻¹ * ⟨g,hg⟩) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      rw [← localGroup_core_eq F d v]
      exact mem_map_of_mem L.subtype hk'
    have hz : ((y : G)⁻¹ * g) * x * ((y : G)⁻¹ * g)⁻¹ ∈ Q F w :=
      le_normalizer_iff.mp hQn _ hk x hx
    have hh : (y : G) * (((y : G)⁻¹ * g) * x * ((y : G)⁻¹ * g)⁻¹) * (y : G)⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem hy (hQX hz)) (X.inv_mem hy)
    have heq : (y : G) * (((y : G)⁻¹ * g) * x * ((y : G)⁻¹ * g)⁻¹) * (y : G)⁻¹ =
        g * x * g⁻¹ := by group
    rwa [heq] at hh
  have hQC : Q F w ≤ C := le_conjugateSpanBy _ _
  have hSR : (S : Subgroup X) ≤ (inclusion hCX).range := by
    intro x hx
    exact ⟨⟨x,hQC (hS ▸ mem_map_of_mem X.subtype hx)⟩,rfl⟩
  apply d.core_span_obstruction v w hvw
  refine ⟨S.comapOfInjective (inclusion hCX) (inclusion_injective _) hSR,?_⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hm := mem_map_of_mem X.subtype
      (show inclusion hCX x ∈ (S : Subgroup X) from hx)
    rw [hS] at hm
    exact hm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hS.symm ▸ hx
    exact ⟨⟨y,hQC (hS ▸ mem_map_of_mem X.subtype hy)⟩,hy,rfl⟩

/-- The dihedral quotient cannot support an escaping two-subgroup in X
when the neighboring core is a Sylow of X. Its nonzero quotient image is
already a full quotient Sylow; maximality then gives a forbidden full image. -/
theorem source_dihedral_core_sylow_escape_false (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z) (hwz : w ≠ z)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5)
    (X A : Subgroup G) (hXL : X ≤ d.localGroup v)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = Q (family P) w)
    (hp : IsPGroup 2 A) (hAX : A ≤ X) (hAQ : A ≤ Q (family P) z)
    (he : ¬ A ≤ Q (family P) v) (hQe : ¬ Q (family P) w ≤ Q (family P) v) : False := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let M : IsRankOneModel (L ⧸ pCore 2 L) := .dihedral ⟨e⟩
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  let T := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let I := ((Q F w).subgroupOf L).map q
  let D := (X.subgroupOf L).map q
  have hQX : Q F w ≤ X := hS ▸ map_subtype_le _
  have hQL : Q F w ≤ L := hQX.trans hXL
  have hQT : I ≤ T := by
    apply map_mono
    intro x hx
    have hh : (x : G) ∈ (R : Subgroup L).map L.subtype := by
      rw [hR,inf_comm]
      exact Noncommuting.graph_Q_le_edgeCore h hvw.symm hx
    obtain ⟨r,hr,heq⟩ := hh
    exact (Subtype.ext heq : r = x) ▸ hr
  have hI : I ≠ ⊥ := by
    intro hh
    have hk : (Q F w).subgroupOf L ≤ pCore 2 L := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh
    apply hQe
    rw [← localGroup_core_eq F d v]
    intro x hx
    exact ⟨⟨x,hQL hx⟩,hk hx,rfl⟩
  have hc : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num
  have hIT : I = (T : Subgroup (L ⧸ pCore 2 L)) :=
    eq_of_le_of_card_ge hQT (by have hh := (Subgroup.one_lt_card_iff_ne_bot I).mpr hI; omega)
  have hTD : (T : Subgroup (L ⧸ pCore 2 L)) ≤ D :=
    hIT ▸ map_mono (comap_mono hQX)
  have hDN : D ≤ normalizer (T : Set (L ⧸ pCore 2 L)) :=
    (M.rankOneSylowFacts T).unique_maximal D hTD
      (lt_top_iff_ne_top.mpr (source_core_sylow_not_full_image h d hvw X hXL S hS))
  have hpre : (T : Subgroup (L ⧸ pCore 2 L)).comap q = R :=
    comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal R)
  have hXw : X ≤ stabilizer F w := by
    intro x hx
    have hn : (⟨x,hXL hx⟩ : L) ∈ (normalizer (T : Set (L ⧸ pCore 2 L))).comap q :=
      hDN (mem_map_of_mem q hx)
    change (⟨x,hXL hx⟩ : L) ∈
      (normalizer ((T : Subgroup (L ⧸ pCore 2 L)) : Set _)).comap q at hn
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      hpre,Sylow.coe_coe,← (source_edge_local_normalizer h d hvw M R hR).2] at hn
    exact hn
  exact he (source_two_neighbor_pGroup_le_core h hB d hvw hvz hwz M A hp
    (hAX.trans (hXL.trans (d.local_le v))) (hAX.trans hXw) (hAQ.trans (Q_le_stabilizer F z)))

/-- DGS 8.4(1), for the entire original characteristic-two model catalogue.
The full radius-three span lies in the actual predecessor's two-core.
Marked two-transitivity handles the linear, Suzuki and unitary models;
the exceptional dihedral image is excluded by the original core-span 6.5. -/
theorem source_radius_three_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 3 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    ∃ prev : Vertex (family P), (graph (family P)).Adj a' prev ∧
      (graph (family P)).dist beta prev + 1 = (graph (family P)).dist beta a' ∧
      V (family P) beta 3 ≤ Q (family P) prev := by
  obtain ⟨_,_,hp,_,x₁,x₂,x₃,h₁,h₂,h₃,hd₁,hd₂,hd₃,_,hWQ₃,_,hinside,hXL,_,⟨S,hS⟩,hinter⟩ :=
    source_radius_three_configuration h hB d hob models hc hab hd hb hcomm hne
  refine ⟨x₁,h₁,hd₁,hinside ?_⟩
  by_contra hescape
  have hne₃ : x₃ ≠ x₁ := by intro he; rw [he] at hd₃; omega
  rcases source_edge_transitive_or_dihedral h hB d h₂.symm (models x₂) with ht | hi
  · exact source_core_intersection_not_le_third d h₂.symm h₃ hne₃ (hob x₂ x₁ h₂.symm)
      (fun y hy hyw => ht x₃ y h₃ hy hne₃ hyw) (hinter hescape)
  · obtain ⟨e⟩ := hi
    apply source_dihedral_core_sylow_escape_false h hB d h₂.symm h₃ hne₃.symm e
      _ _ hXL S hS hp le_sup_left hWQ₃ hescape
    intro he
    apply hob x₁ x₂ h₂
    rw [inf_eq_right.mpr he]
    exact stabilizer_normalizes_Q (family P) x₁


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
