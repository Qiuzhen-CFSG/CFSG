module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryAlphaFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaNatural

/-!
# Natural alpha coordinates without an initial path profile

The actual alpha local quotient acts on the proved elementary section
Q_alpha/Z_alpha. The special beta core makes a full alpha Sylow action
quadratic; nonelementarity of the beta edge quotient makes that action
nontrivial. The exact section order is the minimum binary degree, so there
are no fixed vectors and the action is irreducible. Quadratic recognition
then constructs the equivariant natural coordinates over the marked field.

OriginalUnitaryNatural transports the surjection, its exact kernel and
ambient conjugation formula through the original inclusion. No four-walk
transitivity, independent nonelementarity or natural-action premise is used.
Source: DGS85, Groups and Graphs, corrected (5.12), (11.8)(e), pp.113--115,176.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryConjugationSection Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
private theorem natural_of_minimal_quadratic
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) SL(2,k) W) (S : Sylow 2 SL(2,k))
    (hq : IsQuadratic σ S) (hnt : ∃ t, σ t ≠ 1)
    {j : ℕ} (hj : 1 < j) (hk : Nat.card k = 2^j)
    (hcard : Nat.card W = Nat.card k ^ 2) :
    ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → k), ∀ t w, E (σ t w) = Matrix.mulVec t.val (E w) := by
  have hd : Module.finrank (ZMod 2) W = 2*j := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hcard,hk,Nat.card_zmod,←pow_mul] at hh
    have he := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh
    omega
  have hdimpos : 0 < Module.finrank (ZMod 2) W := by omega
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hdimpos
  have hlo := Representation.SL2.fixedCodim_top_lower σ hnt hj hk
  have hsum := fixedCodim_add_finrank σ ⊤
  have hfix : fixedSpace σ ⊤ = ⊥ := (Submodule.finrank_eq_zero).mp (by omega)
  have hfix' : σ.invariants = ⊥ := by
    apply bot_unique
    intro w hw
    exact hfix.le (fun t => hw t.val)
  let := Representation.SL2.irreducible_of_fixed_free_minimal_binary_degree σ hfix'
    (by omega) hk hd.le
  have hfixed : fixedSpace σ S ≠ ⊥ := by
    intro hz
    have hevery (w : W) : w ∈ fixedSpace σ S := by
      intro t
      have hw : σ t.val w - w ∈ fixedSpace σ S := fun u => hq u u.property t t.property w
      have he : σ t.val w - w = 0 := by simpa only [hz,Submodule.mem_bot] using hw
      exact sub_eq_zero.mp he
    have ht : fixedSpace σ S = ⊤ := top_unique (fun w _ => hevery w)
    exact top_ne_bot (ht.symm.trans hz)
  have hgen : GeneratedByFixedSpace σ S := by
    have ht : fixedConjugateSpan σ S = ⊤ := (eq_bot_or_eq_top _).resolve_left (by
      intro hb
      apply hfixed
      apply bot_unique
      have hh := fixedSpace_le_fixedConjugateSpan σ (S : Subgroup SL(2,k))
      rw [hb] at hh
      exact hh)
    exact congrArg Subrepresentation.toSubmodule ht
  exact natural_of_quadratic_pair_size σ S hq hgen hfix hcard

theorem source_unitary_alpha_natural_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n)) :
    ∃ f : Q (family P) a →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
      f.ker = (Z (family P) a).subgroupOf (Q (family P) a) ∧
      ∀ (l : d.localGroup a) (x y : Q (family P) a),
        (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
        (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 (d.localGroup a)) l)).val
          (f x).toAdd := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hn mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    mark.elim (IsRankOneModel.projective_unitary n hn) (IsRankOneModel.special_unitary n hn)

  have hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)) := by
    have hh := source_unitary_edge_quotient_not_elementary h hB d hab.symm hn mark
    rw [inf_comm (stabilizer (family P) b) (stabilizer (family P) a)] at hh
    exact hh

  let := finite_endpoints h
  let := source_center_elementary h a
  let L := d.localGroup a
  let R := Q (family P) a
  let A := Z (family P) a
  let C := Q (family P) b
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  have hcore : (pCore 2 L).map L.subtype = R := localGroup_core_eq (family P) d a
  have hRL : R ≤ L := hcore ▸ map_subtype_le _
  have hAR : A ≤ R := (source_Z_Q_U h a).1.trans (map_subtype_le _)
  have hnR : L ≤ normalizer (R : Set G) := (d.local_le a).trans (stabilizer_normalizes_Q _ a)
  have hnA : L ≤ normalizer (A : Set G) := (d.local_le a).trans (stabilizer_normalizes_Z (family P) a)
  let π := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := ea.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = R.subgroupOf L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hRL]
    exact localGroup_core_eq (family P) d a
  obtain ⟨_,hN,hE⟩ := source_unitary_alpha_frattini_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  let := hN
  let := hE
  obtain ⟨σ,s,hs⟩ := exists_canonical L R A hRL hAR hnR hnA π hπ hker
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  let S := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hprod : S = R ⊔ C := (source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp).1
  have hT' : (T : Subgroup L).map L.subtype = S := hT
  have hCL : C ≤ L := (show C ≤ S from hprod ▸ le_sup_right).trans (hT' ▸ map_subtype_le _)
  have hQi : (R.subgroupOf L).map π = ⊥ := by rw [←hker,Subgroup.map_ker_self]
  have himage : (C.subgroupOf L).map π = (T.mapSurjective hπ : Subgroup SL(2,k)) := by
    have hh := congrArg (fun X : Subgroup G => (X.subgroupOf L).map π) hprod
    rw [subgroupOf_sup hRL hCL,Subgroup.map_sup,hQi,bot_sup_eq] at hh
    have hTT : (((T : Subgroup L).map L.subtype).subgroupOf L) = T := by
      apply map_injective L.subtype_injective
      rw [map_subgroupOf_eq_of_le (map_subtype_le _)]
    rw [show S = (T : Subgroup L).map L.subtype from hT.symm,hTT] at hh
    exact hh.symm
  have hZbA : Z (family P) b ≤ A := by
    rw [critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b)]
    exact local_omega_le_neighbor_Z h d hab.symm
  have hder : ⁅C,C⁆ ≤ A := (source_unitary_beta_core_layers h hB hS d hc hb hcomm hbc hac Ma hn mark).2.1.trans hZbA
  have hCR : ⁅C,R⁆ ≤ C := by
    rw [commutator_comm]
    exact (source_adjacent_core_commutator h hab).trans inf_le_right
  have hquad := isQuadratic_of_triple_commutator_le L R A C σ π s
    ((commutator_mono le_rfl hCR).trans hder)
  rw [himage] at hquad
  have hnt : ∃ t, σ t ≠ 1 := by
    by_contra! htriv
    have hRC : ⁅R,C⁆ ≤ A := by
      apply commutator_le.mpr
      intro x hx c hc
      exact (s.fixed_coordinate_iff_commutator_mem ⟨c,hCL hc⟩ ⟨x,hx⟩).mp (by
        change σ (π ⟨c,hCL hc⟩) _ = _
        rw [htriv]
        rfl)
    obtain ⟨hNC,hnot⟩ := hne
    let := hNC
    apply hnot
    apply beta_quotient_elementary_of_core_commutator R C A S (isPGroup_pCoreIn 2 _)
      hprod (source_adjacent_core_normalizes_core h hab) hRC (source_core_centralizes_center h a)
    exact (inf_le_inf_right _ ((pCoreIn_le 2 _).trans inf_le_right)).trans
      (source_core_selfCentralizing_in_vertex h b)
  have hcard : Nat.card (Additive (R ⧸ A.subgroupOf R)) = Nat.card k ^ 2 := by
    change Nat.card (R ⧸ A.subgroupOf R) = _
    rw [←index_eq_card]
    change A.relIndex R = _
    rw [(source_unitary_core_orders_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark).2.2.2.2,hk,←pow_mul]
    congr 1
    omega
  obtain ⟨E,hEact⟩ := natural_of_minimal_quadratic σ (T.mapSurjective hπ) hquad hnt
    (by omega : 1 < 2*n) hk hcard
  let f := E.toAddEquiv.toMultiplicative.toMonoidHom.comp s.coordinates
  refine ⟨f,E.toAddEquiv.toMultiplicative.surjective.comp s.onto,?_,?_⟩
  · ext x
    change E (s.coordinates x).toAdd = 0 ↔ (x : G) ∈ A
    rw [E.map_eq_zero_iff]
    exact s.coordinates_eq_one_iff x
  · intro l x y hy
    have heq : y = ⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hnR l.property) x).mp x.property⟩ := Subtype.ext hy
    subst y
    change E (s.coordinates _).toAdd = Matrix.mulVec _ (E (s.coordinates x).toAdd)
    rw [s.equivariant]
    exact hEact (π l) (s.coordinates x).toAdd

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
