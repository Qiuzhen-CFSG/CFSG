module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementaryFiniteQuotient
public import Theory.GroupAction.ElementaryCentralizingTransporter
public import Theory.GroupAction.ThreePointTransitivity

/-!
# The full-Cartan reflection at the binary commuting endpoint

At a cubic critical endpoint, a full edge Cartan fixes a second neighbor
by short-path transitivity and hence fixes all three neighbors. The
critical center at that second neighbor is elementary and acts nontrivially
on the other two. Coprime adjustment in its point-stabilizer coset supplies
an involution moving the original neighbor and centralizing the whole Cartan.

The original elementary Chapter 11 source gives the required path
transitivity. Its literal binary beta quotient gives valence three. Lift
the constructed element through the original locally injective universal
cover, preserving its square, endpoint action, whole-Cartan centralization
and the image in the same neighboring center. No quotient reflection or
trivial Cartan-core centralizer is assumed, and the ambient group need not
be finite.

This supplies the basic beta reflection used in the binary (14.2) branch.
The prescribed four-path-root conjugacy clause, alpha reflection, exchange,
unitary branches and complete marked (11.7)--(11.8) assembly remain separate
obligations; this is not a complete recognition theorem.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7), pp.174--175, and (14.2), pp.210--211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- At the cubic critical endpoint, an involution in a neighboring elementary
center moves the marked neighbor and centralizes the full prescribed Cartan. -/
theorem source_cubic_critical_cartan_reflection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P)=1)
    (hthree : Nat.card ((graph (family P)).neighborSet b)=3)
    (ht : RootPathTransitive (graph (family P)) G a 2)
    (C : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) b) :
    ∃ c : Vertex (family P), (graph (family P)).Adj b c ∧ c≠a ∧
      ∃ t ∈ Z (family P) c, t∈centralizer (C : Set G) ∧
        t*t=1 ∧ t • b=b ∧ t • a≠a := by
  let _ := finite_endpoints h
  let F := family P
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨c,hbc,hca,hCc⟩ := CommutingTrivial.edge_cartan_second_fixed_neighbor
    h hB hS hab ht C hCE hd hg
  have hpres (g : G) (hgb : g • b=b) (z : Vertex F) :
      z ∈ (graph F).neighborSet b ↔ g • z ∈ (graph F).neighborSet b := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff
      (v := b) (w := z)
    change (graph F).Adj (g • b) (g • z) ↔ (graph F).Adj b z at hh
    change (graph F).Adj b z ↔ (graph F).Adj b (g • z)
    simpa only [hgb] using hh.symm
  have hCall : ∀ g ∈ C, ∀ z ∈ (graph F).neighborSet b, g • z=z := by
    intro g hgC
    exact MulAction.fixes_three_point_set _ hthree g (hpres g (hCE hgC).2)
      hab.symm hbc (Ne.symm hca) (hCE hgC).1 (hCc hgC)
  let _ : Finite ((graph F).neighborSet b) := Nat.finite_of_card_ne_zero
    (by change Nat.card ((graph (family P)).neighborSet b)≠0; rw [hthree]; decide)
  have hcard : 2 < ((graph F).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hthree]; decide
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcard
  have hex : ∃ r ∈ (graph F).neighborSet b, r≠a ∧ r≠c := by
    by_cases hux : u≠a ∧ u≠c
    · exact ⟨u,hu,hux⟩
    by_cases hvx : v≠a ∧ v≠c
    · exact ⟨v,hv,hvx⟩
    exact ⟨w,hw,by aesop⟩
  obtain ⟨r,hbr,hra,hrc⟩ := hex
  obtain ⟨g,hgb,hgac⟩ := locally_transitive F hab.symm hbc
  have hc' := CommutingNontrivial.criticalPair_translate F hc g
  rw [hgac,show g • b=b from hgb] at hc'
  have hZb : Z F c ≤ stabilizer F b :=
    ((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h c).2.trans ((ballKernel_one_le_edge F hbc.symm).trans inf_le_right))
  have hmove : ¬ Z F c ≤ fixingSubgroup G ((graph F).neighborSet b) := by
    intro he
    apply hc'.2
    intro z hz x hx
    rcases (mem_ball_one F b x).mp hx with hx | rfl
    · exact (mem_fixingSubgroup_iff G).mp (he hz) x hx
    · exact hZb hz
  obtain ⟨x,hx,hxa⟩ := MulAction.transitive_other_two_of_nontrivial
    ((graph F).neighborSet b) hthree (Z F c) hbc
    (fun _ hz => Z_le_stabilizer F c hz)
    (fun g hg => hpres g (hZb hg)) hmove hab.symm hbr hca (Ne.symm hrc)
  let _ : Finite (Z F c) := Finite.of_injective (inclusion (Z_le_stabilizer F c))
    (inclusion_injective _)
  let _ : Finite C := Finite.of_injective (inclusion (hCE.trans inf_le_left))
    (inclusion_injective _)
  let _ := source_center_elementary h c
  have hn : C ≤ normalizer (Z F c : Set G) := hCc.trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F c)).mp (Z_normal F c))
  obtain ⟨t,ht,htC,htsq,hta⟩ := Theory.GroupAction.exists_elementary_centralizing_transporter
    (Z F c) C hn ho a r (fun g hg => (hCE hg).1)
    (fun g hg => hCall g hg r hbr) ⟨x,hx⟩ hxa
  exact ⟨c,hbc,hca,t,ht,htC,htsq,hZb ht,by rw [hta]; exact hra⟩

section Original
open Reduction NoncommutingProfile CommutingNontrivial
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
local notation "α" => base F false
local notation "β" => base F true
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S)
      (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S)=1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆=⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype)) 2 2)
include h hc hb hcomm helem hbinary

/-- The actual elementary binary source discharges the valence and short-path
premises for the beta reflection, using the original full edge Cartan. -/
theorem original_elementary_binary_beta_cartan_reflection
    (C : Subgroup G₀) [IsMulCommutative C]
    (hCE : C ≤ stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hg : C ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 =
      stabilizer F α ⊓ stabilizer F β) :
    ∃ c : Vertex F, (graph F).Adj β c ∧ c≠α ∧
      ∃ t ∈ Z F c, t∈centralizer (C : Set G₀) ∧ t*t=1 ∧
        t • β=β ∧ t • α≠α := by
  let H := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let j := (graphLocalGroup F β).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let e := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have mb : ClassicalGroup.IsPSL (d.localGroup β ⧸ pCore 2 (d.localGroup β)) 2 2 :=
    hbinary.of_mulEquiv e
  obtain ⟨k,fk,fink,hk,⟨eb⟩⟩ := mb
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (show Fintype.card k=2^1 by simpa only [Nat.card_eq_fintype_card,pow_one] using hk)
  let eSL : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,k) :=
    eb.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have M : IsRankOneModel (d.localGroup β ⧸ pCore 2 (d.localGroup β)) :=
    .linear 1 (by decide) ⟨k,fk,fink,hk,⟨eb⟩⟩
  have hcard : Nat.card ((graph F).neighborSet β)=3 := by
    have hh := source_linear_neighbor_card H (reduced_borel_core_sylow h) d
      (source_critical_one_adjacent hc hb) M eSL
    change Nat.card ((graph F).neighborSet β)=Nat.card k+1 at hh
    rw [hk] at hh
    exact hh
  obtain ⟨_,_,_,_,_,_,_,_,_,hpar,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf G₀)=5 :=
    (sourceS_spec H (reduced_vertex_sylow h)).2.unique hpar.2
  exact source_cubic_critical_cartan_reflection H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc hb hcard
    (sourceS_transitive H (reduced_vertex_sylow h) α (by omega)) C hCE ho hd hg

/-- Lift the source beta reflection through the literal universal cover. Its
image still lies in the same neighboring center; the entire Cartan is centralized. -/
theorem original_elementary_binary_beta_tree_reflection
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ t : (A).Universal, t • base T true=base T true ∧
      t • base T false≠base T false ∧ t*t=1 ∧
      t∈centralizer (cartan c : Set (A).Universal) ∧
      ∃ v : Vertex F, (graph F).Adj β v ∧ v≠α ∧ bOne_tree_map h t∈Z F v := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U₀ := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let _ : Finite (F false) := (finite_endpoints (reduced_triple h)) false
  let _ : Finite (F true) := (finite_endpoints (reduced_triple h)) true
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmiddle : originalMiddle A=T false ⊓ T true :=
    (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).symm
  have hmapE : (originalMiddle A).map φ=E := by
    rw [hmiddle]
    exact cov.map_inf
  have hCE : C≤E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U₀≤E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E≤normalizer (U₀ : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U₀≤E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E=U₀ ⊔ C := he.symm
      _≤C ⊔ E.pCoreIn 2 := sup_le (hUcore.trans le_sup_right) le_sup_left
  have hE : E=stabilizer F α ⊓ stabilizer F β := by
    have ha : stabilizer F α=F false := Subgroup.CosetGeometry.stabilizer_base F false
    have hb : stabilizer F β=F true := Subgroup.CosetGeometry.stabilizer_base F true
    rw [ha,hb]
  obtain ⟨v,hv,hva,g,hgZ,hgC,hgsq,hgfix,hgmove⟩ :=
    original_elementary_binary_beta_cartan_reflection h hc hb hcomm helem hbinary
      C (hE ▸ hCE) ho (hE ▸ hd) (hE ▸ hg)
  have hgF : g∈F true := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F true]
    exact hgfix
  obtain ⟨t,ht,htg⟩ := (cov.map_eq true).symm ▸ hgF
  have hfix : t • base T true=base T true := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base T true] at hh
    exact hh
  have hmove : t • base T false≠base T false := by
    intro he
    have hh := congrArg cov.vertex he
    apply hgmove
    have hh' : bOne_tree_map h t • base (reducedFamily L S) false =
        base (reducedFamily L S) false := by
      simpa only [cov.vertex_smul,cov.vertex_base] using hh
    change φ t • α=α at hh'
    rwa [htg] at hh'
  have hsq : t*t=1 := by
    have he : φ (t*t)=φ 1 := by rw [map_mul,htg,hgsq,map_one]
    exact congrArg Subtype.val (cov.injective true
      (a₁ := ⟨t*t,(T true).mul_mem ht ht⟩) (a₂ := 1) he)
  have hCbeta : cartan c≤T true := (cartan_le c).trans (hmiddle ▸ inf_le_right)
  have htC : t∈centralizer (cartan c : Set (A).Universal) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    have he : φ (k*t)=φ (t*k) := by
      rw [map_mul,map_mul,htg]
      exact mem_centralizer_iff.mp hgC _ (mem_map_of_mem φ hk)
    exact congrArg Subtype.val (cov.injective true
      (a₁ := ⟨k*t,(T true).mul_mem (hCbeta hk) ht⟩)
      (a₂ := ⟨t*k,(T true).mul_mem ht (hCbeta hk)⟩) he)
  exact ⟨t,hfix,hmove,hsq,htC,v,hv,hva,htg ▸ hgZ⟩

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
