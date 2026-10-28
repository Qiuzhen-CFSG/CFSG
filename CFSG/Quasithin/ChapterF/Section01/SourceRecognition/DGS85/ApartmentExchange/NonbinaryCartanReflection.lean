module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NonbinaryCartanCentralizer
public import Theory.SpecificGroups.SL2.TorusNormalizerReflection

/-!
# A full-Cartan transporter is a reflection

Hall conjugacy supplies an intrinsic local actor normalizing the entire
edge Cartan and moving the opposite vertex to a second Cartan-fixed neighbor.
Its rank-one image normalizes a nontrivial odd torus outside the Borel, so
its square lies in the vertex core. Since that square normalizes the odd
Cartan, it centralizes it. A trivial core centralizer therefore makes the
original transporter an involution, with its original ambient marking.

Source: DGS, *Groups and Graphs* (1985), (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ApartmentExchange
open CommutingTrivial Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem normalizing_disjoint_mem_centralizer
    (N C : Subgroup G) (hCN : C ≤ normalizer (N : Set G))
    (hd : Disjoint C N) {x : G} (hxN : x ∈ N)
    (hxC : x ∈ normalizer (C : Set G)) : x ∈ centralizer (C : Set G) := by
  apply mem_centralizer_iff.mpr
  intro c hc
  have hcommC : x*c*x⁻¹*c⁻¹ ∈ C :=
    C.mul_mem ((mem_normalizer_iff.mp hxC c).mp hc) (C.inv_mem hc)
  have hcommN : x*c*x⁻¹*c⁻¹ ∈ N := by
    have hconj := (mem_normalizer_iff.mp (hCN hc) x⁻¹).mp (N.inv_mem hxN)
    simpa only [mul_assoc] using N.mul_mem hxN hconj
  have he := disjoint_def.mp hd hcommC hcommN
  have he' : x*c*x⁻¹=c := mul_inv_eq_one.mp he
  have hh := congrArg (·*x) he'
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

/-- In a nonbinary local quotient the selected full-Cartan transporter
is an involution as soon as its actual vertex-core centralizer is trivial. -/
theorem full_cartan_neighbor_transporter_square
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,k))
    (hk : 2 < Nat.card k) (C : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hgen : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hcentral : Q (family P) v ⊓ centralizer (C : Set G) = ⊥)
    (g : G) (hg : g ∈ graphLocalGroup (family P) v)
    (hgC : g ∈ normalizer (C : Set G)) (hgmove : g • w ≠ w) : g*g=1 := by
  let _ := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let U := E.pCoreIn 2
  let D := (C ⊓ H).subgroupOf H
  let _ : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hCQ : Disjoint C (Q Γ v) := hd.mono_right (graph_Q_le_edgeCore h hvw)
  obtain ⟨R,hR⟩ := local_edge_sylow h hB hS hvw
  change (R : Subgroup H).map H.subtype = U at hR
  have hUH : U ≤ H := hR ▸ map_subtype_le _
  have hR' : (R : Subgroup H) = U.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hUH,hR]
  have hN (l : H) : l ∈ normalizer (R : Set H) ↔ (l : G) ∈ E := by
    change l ∈ normalizer ((R : Subgroup H) : Set H) ↔ _
    rw [hR',←subgroupOf_normalizer_eq hUH]
    constructor
    · intro hl
      exact (local_edge_core_normalizer h hB hS hvw).le ⟨sylowGenerated_le _ l.property,hl⟩
    · intro hl
      exact (E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))) hl
  have hDN : D ≤ normalizer (R : Set H) := fun l hl => (hN l).mpr (hCE hl.1)
  have hoD : Odd (Nat.card D) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ⊓ H ≤ H from inf_le_right)).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le (show C ⊓ H ≤ C from inf_le_left))
  have hneD : D.map q ≠ ⊥ := by
    obtain ⟨⟨f⟩,_⟩ := edge_complement_local_torus h hB hS hvw e C hCE hd hgen
    have hcard : 1 < Nat.card (C ⊓ H : Subgroup G) := by
      rw [Nat.card_congr f.toEquiv,Nat.card_units]
      omega
    have hne : C ⊓ H ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; omega
    obtain ⟨d,hdD,hdne⟩ := (C ⊓ H).bot_or_exists_ne_one.resolve_left hne
    intro he
    have hqd : q (⟨d,hdD.2⟩ : H) = 1 := he.le (mem_map_of_mem q hdD)
    have hdp : (⟨d,hdD.2⟩ : H) ∈ pCore 2 H := hker ▸ hqd
    have hdQ : d ∈ Q Γ v :=
      (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hdp)
    exact hdne (disjoint_def.mp hCQ hdD.1 hdQ)
  let gH : H := ⟨g,hg⟩
  have hgD : gH ∈ normalizer (D : Set H) := by
    apply mem_normalizer_iff.mpr
    intro d
    change ((d : G) ∈ C ∧ (d : G) ∈ H) ↔
      (g*(d : G)*g⁻¹ ∈ C ∧ g*(d : G)*g⁻¹ ∈ H)
    constructor
    · intro hdD
      exact ⟨(mem_normalizer_iff.mp hgC _).mp hdD.1,
        H.mul_mem (H.mul_mem hg hdD.2) (H.inv_mem hg)⟩
    · intro hdD
      exact ⟨(mem_normalizer_iff.mp hgC _).mpr hdD.1,d.property⟩
  let Rq := R.mapSurjective hq
  have hqN : q gH ∉ normalizer (Rq : Set SL(2,k)) := by
    intro hh
    have hh' : gH ∈ (normalizer (((R : Subgroup H).map q) : Set SL(2,k))).comap q := hh
    rw [comap_normalizer_eq_of_surjective _ hq,
      comap_map_eq_self (hker ▸ pCore_isPGroup.le_sylow_of_normal R)] at hh'
    exact hgmove ((hN gH).mp hh').2
  have hqg : q gH * q gH = 1 := Matrix.SpecialLinearGroup.sylow_odd_subgroup_normalizer_square
    Rq (D.map q) ((map_mono hDN).trans ((R : Subgroup H).le_normalizer_map q))
    (hoD.of_dvd_nat (D.card_map_dvd q)) hneD (q gH)
    (D.le_normalizer_map q (mem_map_of_mem q hgD)) hqN
  have hgsq : gH*gH ∈ pCore 2 H := hker ▸ (show gH*gH ∈ q.ker by
    rw [MonoidHom.mem_ker,map_mul,hqg])
  have hgsqQ : g*g ∈ Q Γ v :=
    (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hgsq)
  have hgsqC := normalizing_disjoint_mem_centralizer (Q Γ v) C
    ((hCE.trans inf_le_left).trans (stabilizer_normalizes_Q Γ v)) hCQ hgsqQ
    ((normalizer (C : Set G)).mul_mem hgC hgC)
  exact hcentral.le ⟨hgsqQ,hgsqC⟩

/-- Construct an actual involution normalizing the full Cartan, fixing its
marked endpoint and moving the opposite endpoint. -/
theorem exists_full_cartan_reflection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G w 2)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,k))
    (hk : 2 < Nat.card k) (C : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hgen : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hcentral : Q (family P) v ⊓ centralizer (C : Set G) = ⊥) :
    ∃ g ∈ graphLocalGroup (family P) v,
      g ∈ normalizer (C : Set G) ∧ g*g=1 ∧ g • v=v ∧ g • w≠w := by
  obtain ⟨r,hr,hrne,hCr⟩ := edge_cartan_second_fixed_neighbor h hB hS hvw.symm ht C
    (hCE.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hd)
    (by simpa only [inf_comm] using hgen)
  obtain ⟨g,hg,hgC,hgr⟩ := Assembly.BTwoSource.full_cartan_neighbor_transport
    h hB hS hvw hr C hCE hCr ho hd hgen
  have hgmove : g • w ≠ w := hgr ▸ hrne
  exact ⟨g,hg,hgC,full_cartan_neighbor_transporter_square h hB hS hvw e hk C
    hCE ho hd hgen hcentral g hg hgC hgmove,sylowGenerated_le _ hg,hgmove⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.ApartmentExchange
