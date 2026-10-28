module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaNatural
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import Theory.Representation.SpecialLinearNatural
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions

/-!
# Three-core intersections and odd unitary five-walk fixers

Two beta cores at distinct alpha neighbors intersect inside Q_alpha. Their
special commutator layers make their intersection fixed modulo Z_alpha by
two distinct full alpha Sylows. The already constructed natural alpha
coordinates and generation of SL₂ by those Sylows put this intersection
inside Z_alpha. The original edge action transports the known remote-center
separation to every other beta neighbor. The center-intersection identities
then kill both three-core intersections used in DGS (11.8)(g).

Any two-subgroup fixing five nonbacktracking edges lies in the cores of its
three internal turns, so it is trivial. Cauchy's theorem gives odd order of
the full pointwise fixer. Conjugation and reversal give the same conclusion
on every five-walk, including closed source paths, without a tree assumption.
The local kernel is never identified with the two-core. Both unitary covers
and every positive field degree remain allowed; earlier local structure,
escaping source-path and path-transitivity premises remain explicit.

ReducedUnitaryPathFixers transports this result under the original inclusion
and the full Borel. The exact source parameters r=4 and s=5 still require
five-walk transitivity. Source: Delgado--Goldschmidt--Stellmacher, Groups and
Graphs (1985), (11.6) and (11.8)(e--g), printed pp.172--177.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

omit [Finite k] [CharP k 2] in
private theorem natural_fixed_all_zero (w : Fin 2 → k)
    (hw : ∀ t : SL(2,k), Matrix.mulVec t.val w = w) : w = 0 := by
  have h₀ := congrFun (hw (Matrix.SpecialLinearGroup.transvection
    (i := 0) (j := 1) zero_ne_one (1 : k))) 0
  have h₁ := congrFun (hw (Matrix.SpecialLinearGroup.transvection
    (i := 1) (j := 0) one_ne_zero (1 : k))) 1
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h₀ h₁
  ext i
  fin_cases i
  · simpa using h₁
  · simpa using h₀

omit [Finite k] [CharP k 2] in
private theorem neighbor_core_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hprod : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b) :
    let L := d.localGroup a
    let π := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 L,
      (T : Subgroup L).map L.subtype =
        (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ∧
      Q (family P) b ≤ L ∧
      ((Q (family P) b).subgroupOf L).map π = (T : Subgroup L).map π := by
  let := finite_endpoints h
  let L := d.localGroup a
  let π := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hcore : (pCore 2 L).map L.subtype = Q (family P) a := localGroup_core_eq _ d a
  have hRL : Q (family P) a ≤ L := hcore ▸ map_subtype_le _
  have hCL : Q (family P) b ≤ L :=
    (hprod ▸ le_sup_right).trans (hT ▸ map_subtype_le _)
  have hk : π.ker = (Q (family P) a).subgroupOf L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hRL,hcore]
  have hQi : ((Q (family P) a).subgroupOf L).map π = ⊥ := by
    rw [←hk,Subgroup.map_ker_self]
  have hh := congrArg (fun X : Subgroup G => (X.subgroupOf L).map π) hprod
  rw [subgroupOf_sup hRL hCL,Subgroup.map_sup,hQi,bot_sup_eq] at hh
  have hTT : (((T : Subgroup L).map L.subtype).subgroupOf L) = T := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (map_subtype_le _)]
  rw [←hT,hTT] at hh
  exact ⟨T,hT,hCL,hh.symm⟩

/-- Two distinct neighboring beta cores intersect in the alpha center. -/
theorem source_unitary_opposite_beta_cores_le_alpha_center_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n)) :
    Q (family P) b ⊓ Q (family P) (g • b) ≤ Z (family P) a := by
  let := finite_endpoints h
  let L := d.localGroup a
  let R := Q (family P) a
  let A := Z (family P) a
  let C := Q (family P) b
  let D := Q (family P) (g • b)
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hat : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp).1
  have hprod' : (stabilizer (family P) a ⊓ stabilizer (family P) (g • b)).pCoreIn 2 = R ⊔ D := by
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) hprod
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ←stabilizer_translate,←stabilizer_translate,Subgroup.map_sup,
      ←Q_translate,←Q_translate,hga'] at hh
    exact hh
  let π := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := ea.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkπ : π.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
  obtain ⟨T,hT,hCL,hCT⟩ := neighbor_core_image h hB d hab ea hprod
  obtain ⟨U,hU,hDL,hDU⟩ := neighbor_core_image h hB d hat ea hprod'
  let T' := T.mapSurjective hπ
  let U' := U.mapSurjective hπ
  have hTU : T' ≠ U' := by
    intro he
    have hh := congrArg (fun X : Sylow 2 SL(2,k) => (X : Subgroup SL(2,k)).comap π) he
    change ((T : Subgroup L).map π).comap π = ((U : Subgroup L).map π).comap π at hh
    rw [Subgroup.comap_map_eq,Subgroup.comap_map_eq,hkπ,
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal U)] at hh
    apply hgb
    exact source_edge_sylow_unique_neighbor h d hab hat Ma T hT (by
      rw [hh,hU]
      exact (pCoreIn_le 2 _).trans inf_le_right)
  have hgen := Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 T' U' hTU
  have hCDR : C ⊓ D ≤ R :=
    source_rankOne_pair_core_le_beta h hB d hab.symm hat hgb.symm Ma
  have hZbA : Z (family P) b ≤ A :=
    source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hder : ⁅C,C⁆ ≤ A :=
    (source_beta_core_special_on_escaping_path h hB hS d hc hb hcomm
      hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.1.le.trans hZbA
  have hder' : ⁅D,D⁆ ≤ A := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hder
    rw [map_commutator,←Q_translate,←Z_translate,hga'] at hh
    exact hh
  obtain ⟨f,_,hker,hact⟩ := source_unitary_alpha_natural_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne hn mark ea hk
  let σ : Representation k SL(2,k) (Fin 2 → k) := specialLinearNatural 2
  intro x hx
  let xR : R := ⟨x,hCDR hx⟩
  have hfixed (E : Subgroup G) (hEL : E ≤ L) (hxE : x ∈ E) (hd : ⁅E,E⁆ ≤ A)
      (t : SL(2,k)) (ht : t ∈ (E.subgroupOf L).map π) :
      Matrix.mulVec t.val (f xR).toAdd = (f xR).toAdd := by
    obtain ⟨u,hu,rfl⟩ := ht
    let y : R := ⟨(u : G) * x * (u : G)⁻¹,
      (mem_normalizer_iff.mp (((d.local_le a).trans (stabilizer_normalizes_Q _ a)) u.property) x).mp xR.property⟩
    have hcA : (y * xR⁻¹ : R) ∈ A.subgroupOf R :=
      hd (commutator_mem_commutator hu hxE)
    have he : f y = f xR := by
      have hh : y * xR⁻¹ ∈ f.ker := hker.symm ▸ hcA
      change f (y * xR⁻¹) = 1 at hh
      rw [map_mul,map_inv,mul_inv_eq_one] at hh
      exact hh
    exact (hact u xR y rfl).symm.trans (congrArg Multiplicative.toAdd he)
  have hfixT : (f xR).toAdd ∈ Representation.invariants (σ.comp (T' : Subgroup SL(2,k)).subtype) := by
    intro t
    exact hfixed C hCL hx.1 hder t (hCT ▸ t.property)
  have hfixU : (f xR).toAdd ∈ Representation.invariants (σ.comp (U' : Subgroup SL(2,k)).subtype) := by
    intro t
    exact hfixed D hDL hx.2 hder' t (hDU ▸ t.property)
  have hall : (f xR).toAdd ∈ Representation.invariants (σ.comp ((T' : Subgroup SL(2,k)) ⊔ U').subtype) := by
    rw [σ.invariants_comp_sup]
    exact ⟨hfixT,hfixU⟩
  rw [hgen] at hall
  have hz : (f xR).toAdd = 0 := natural_fixed_all_zero _ (fun t => hall ⟨t,mem_top _⟩)
  have he : xR ∈ f.ker := hz
  rw [hker] at he
  exact he

/-- Every other beta neighbor has the same center separation and core bound. -/
theorem source_unitary_turn_intersections_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n)) :
    ∀ {t : Vertex (family P)}, (graph (family P)).Adj a t → t ≠ b →
      Q (family P) b ⊓ Q (family P) t ≤ Z (family P) a ∧
      Z (family P) b ⊓ Q (family P) t = ⊥ := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  have hat : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hpair := source_unitary_opposite_beta_cores_le_alpha_center_on_escaping_path
    h hB hS d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
    hne hn mark ea hk
  have hz := source_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hd : Z (family P) b ⊓ Q (family P) (g • b) = ⊥ := bot_unique
    ((inf_le_inf_right _ (source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm)).trans hz.le)
  have htrans := (source_edge_transitive_or_dihedral h hB d hab Ma).resolve_right (by
    rintro ⟨e⟩
    exact source_alpha_dihedral_exclusion h hB d hc hb hcomm hbc hac Mb e)
  intro t hat' htb
  obtain ⟨u,hu,hut⟩ := htrans (g • b) t hat hat' hgb htb
  have hua : u • a = a := d.local_le a hu.1
  have hub : u • b = b := hu.2
  have hpair' := map_mono (f := (MulAut.conj u).toMonoidHom) hpair
  rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective,←Q_translate,←Q_translate,
    ←Z_translate,hua,hub,hut] at hpair'
  have hd' := congrArg (fun X : Subgroup G => X.map (MulAut.conj u).toMonoidHom) hd
  rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective,←Z_translate,←Q_translate,
    hub,hut,Subgroup.map_bot] at hd'
  exact ⟨hpair',hd'⟩

/-- The two literal three-core intersections in DGS (11.8)(g) vanish. -/
theorem source_unitary_three_core_intersections_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n))
    {t w : Vertex (family P)} (hat : (graph (family P)).Adj a t) (htb : t ≠ b)
    (hbw : (graph (family P)).Adj b w) (haw : a ≠ w) :
    Q (family P) b ⊓ Q (family P) t ⊓ Q (family P) w = ⊥ ∧
      Q (family P) a ⊓ Q (family P) w ⊓ Q (family P) t = ⊥ := by
  obtain ⟨hpair,hd⟩ := source_unitary_turn_intersections_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne hn mark ea hk hat htb
  have hcent := (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbw haw Ma Mb ea).1
  have hzero : Q (family P) b ⊓ Q (family P) t ⊓ Q (family P) w = ⊥ := by
    apply bot_unique
    apply le_trans ?_ hd.le
    exact le_inf ((le_inf (inf_le_left.trans hpair) inf_le_right).trans hcent.le)
      (inf_le_left.trans inf_le_right)
  refine ⟨hzero,bot_unique ?_⟩
  apply le_trans ?_ hzero.le
  have hQ := source_rankOne_pair_core_le_beta h hB d (source_critical_one_adjacent hc hb) hbw haw Mb
  exact le_inf (le_inf (inf_le_left.trans hQ) inf_le_right) (inf_le_left.trans inf_le_right)

private def turn_quotient_conjugate (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (g : G) :
    (d.localGroup (g • a) ⧸ pCore 2 (d.localGroup (g • a))) ≃*
      (d.localGroup a ⧸ pCore 2 (d.localGroup a)) := by
  let e := (MulEquiv.subgroupCongr (d.conjugate g a)).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- Odd fixers for all nonbacktracking five-edge chains with the given middle edge.
The extra source-path premises are used only for the earlier core structure. -/
theorem source_unitary_five_edge_fixer_odd_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n))
    {v₀ t w v₅ : Vertex (family P)}
    (h0t : (graph (family P)).Adj v₀ t) (hta : (graph (family P)).Adj t a)
    (hbw : (graph (family P)).Adj b w) (hw5 : (graph (family P)).Adj w v₅)
    (h0a : v₀ ≠ a) (htb : t ≠ b) (haw : a ≠ w) (hb5 : b ≠ v₅) :
    Odd (Nat.card (stabilizer (family P) v₀ ⊓ stabilizer (family P) t ⊓
      stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
      stabilizer (family P) w ⊓ stabilizer (family P) v₅ : Subgroup G)) := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨u,hua,hub⟩ := locally_transitive (family P) hab hta.symm
  have hub' : u • b = t := hub
  have Mt : IsRankOneModel (d.localGroup t ⧸ pCore 2 (d.localGroup t)) := by
    rw [←hub']
    exact Mb.of_equiv (turn_quotient_conjugate d b u)
  obtain ⟨z,hzb,hza⟩ := locally_transitive (family P) hab.symm hbw
  have hza' : z • a = w := hza
  have Mw : IsRankOneModel (d.localGroup w ⧸ pCore 2 (d.localGroup w)) := by
    rw [←hza']
    exact Ma.of_equiv (turn_quotient_conjugate d a z)
  have hzero := (source_unitary_three_core_intersections_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne hn mark ea hk
    hta.symm htb hbw haw).1
  let D := stabilizer (family P) v₀ ⊓ stabilizer (family P) t ⊓
    stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
    stabilizer (family P) w ⊓ stabilizer (family P) v₅
  have hD0 : D ≤ stabilizer (family P) v₀ := fun _ hx => hx.1.1.1.1.1
  let : Finite D := Finite.of_injective (inclusion hD0) (inclusion_injective _)
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hd
  let A := zpowers (x : G)
  have hpA : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    change Nat.card (zpowers (x : G)) ∣ 2^1
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]; decide)
  have hAD : A ≤ D := zpowers_le.mpr x.property
  have hA0 : A ≤ stabilizer (family P) v₀ := hAD.trans hD0
  have hAt : A ≤ stabilizer (family P) t := hAD.trans (fun _ hx => hx.1.1.1.1.2)
  have hAa : A ≤ stabilizer (family P) a := hAD.trans (fun _ hx => hx.1.1.1.2)
  have hAb : A ≤ stabilizer (family P) b := hAD.trans (fun _ hx => hx.1.1.2)
  have hAw : A ≤ stabilizer (family P) w := hAD.trans (fun _ hx => hx.1.2)
  have hA5 : A ≤ stabilizer (family P) v₅ := hAD.trans inf_le_right
  have hAtQ := source_two_neighbor_two_group_le_core h hB d h0t hta h0a Mt A hpA hA0 hAt hAa
  have hAbQ := source_two_neighbor_two_group_le_core h hB d hab hbw haw Mb A hpA hAa hAb hAw
  have hAwQ := source_two_neighbor_two_group_le_core h hB d hbw hw5 hb5 Mw A hpA hAb hAw hA5
  have hA : A = ⊥ := bot_unique ((le_inf (le_inf hAbQ hAtQ) hAwQ).trans hzero.le)
  have hx1 : x = 1 := Subtype.ext (mem_bot.mp (hA ▸ mem_zpowers (x : G)))
  simp only [hx1,orderOf_one] at hx
  omega

open SimpleGraph.Walk Theory.GroupTheory.WeakBNPair.RegularTree

private theorem bool_opposite_unique {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

omit [Finite k] [CharP k 2] [Field k] in
private theorem five_walk_fixer_odd_oriented
    {F : Bool → Subgroup G} [∀ i, Finite (F i)]
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (hfix : ∀ {v₀ t w v₅ : Vertex F},
      (graph F).Adj v₀ t → (graph F).Adj t a → (graph F).Adj b w → (graph F).Adj w v₅ →
      v₀ ≠ a → t ≠ b → a ≠ w → b ≠ v₅ →
      Odd (Nat.card (stabilizer F v₀ ⊓ stabilizer F t ⊓ stabilizer F a ⊓
        stabilizer F b ⊓ stabilizer F w ⊓ stabilizer F v₅ : Subgroup G)))
    {x y : Vertex F} (q : (graph F).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2))
    (ha : (q.getVert 2).type = a.type) : Odd (Nat.card (pathFixer (X := G) q)) := by
  have h23 := q.adj_getVert_succ (by omega : 2 < q.length)
  have hb : (q.getVert 3).type = b.type :=
    bool_opposite_unique h23.1 (ha ▸ hab.1)
  obtain ⟨s,hsa,hsb⟩ := incident_common_translate F hab.2
  obtain ⟨t,hta,htb⟩ := incident_common_translate F h23.2
  rw [ha] at hta
  rw [hb] at htb
  let u := t*s⁻¹
  have hua : u • a = q.getVert 2 := by
    rw [←hsa]
    change (t*s⁻¹) • (s • base F a.type) = _
    rw [mul_smul,inv_smul_smul,hta]
  have hub : u • b = q.getVert 3 := by
    rw [←hsb]
    change (t*s⁻¹) • (s • base F b.type) = _
    rw [mul_smul,inv_smul_smul,htb]
  let e := Subgroup.CosetGeometry.translationGraphIso F u⁻¹
  let p := q.map e.toHom
  have hpl : p.length = 5 := by rw [length_map,hlen]
  have hpa : p.getVert 2 = a := by
    change (q.map e.toHom).getVert 2 = _
    rw [getVert_map]
    change u⁻¹ • q.getVert 2 = a
    rw [←hua,inv_smul_smul]
  have hpb : p.getVert 3 = b := by
    change (q.map e.toHom).getVert 3 = _
    rw [getVert_map]
    change u⁻¹ • q.getVert 3 = b
    rw [←hub,inv_smul_smul]
  have hpn (i : ℕ) (hi : i+2 ≤ p.length) : p.getVert i ≠ p.getVert (i+2) := by
    change (q.map e.toHom).getVert i ≠ (q.map e.toHom).getVert (i+2)
    simp only [getVert_map]
    exact fun he => hnb i (by omega) (e.injective he)
  have hadj (i : ℕ) (hi : i < 5) := p.adj_getVert_succ (by omega : i < p.length)
  have ho := hfix (hadj 0 (by decide))
    (by simpa only [hpa] using hadj 1 (by decide))
    (by simpa only [hpb] using hadj 3 (by decide)) (hadj 4 (by decide))
    (by simpa only [hpa] using hpn 0 (by omega))
    (by simpa only [hpb] using hpn 1 (by omega))
    (by simpa only [hpa] using hpn 2 (by omega))
    (by simpa only [hpb] using hpn 3 (by omega))
  have hpo : Odd (Nat.card (pathFixer (X := G) p)) := by
    apply Odd.of_dvd_nat ho
    apply card_dvd_of_le
    intro x hx
    exact ⟨⟨⟨⟨⟨hx 0 (by omega),hx 1 (by omega)⟩,hpa ▸ hx 2 (by omega)⟩,
      hpb ▸ hx 3 (by omega)⟩,hx 4 (by omega)⟩,hx 5 (by omega)⟩
  have he := pathFixer_map_conj q p u⁻¹ (by rw [length_map]) (by
    intro i hi
    change u⁻¹ • q.getVert i = (q.map e.toHom).getVert i
    rw [getVert_map]
    rfl)
  rw [←he,card_map_of_injective (MulAut.conj u⁻¹).injective] at hpo
  exact hpo

omit [Finite k] [CharP k 2] [Field k] in
private theorem five_walk_fixer_odd_of_middle_edge
    {F : Bool → Subgroup G} [∀ i, Finite (F i)]
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (hfix : ∀ {v₀ t w v₅ : Vertex F},
      (graph F).Adj v₀ t → (graph F).Adj t a → (graph F).Adj b w → (graph F).Adj w v₅ →
      v₀ ≠ a → t ≠ b → a ≠ w → b ≠ v₅ →
      Odd (Nat.card (stabilizer F v₀ ⊓ stabilizer F t ⊓ stabilizer F a ⊓
        stabilizer F b ⊓ stabilizer F w ⊓ stabilizer F v₅ : Subgroup G)))
    {x y : Vertex F} (q : (graph F).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := G) q)) := by
  by_cases ha : (q.getVert 2).type = a.type
  · exact five_walk_fixer_odd_oriented hab hfix q hlen hnb ha
  have ha3 : (q.getVert 3).type = a.type :=
    bool_opposite_unique (q.adj_getVert_succ (by omega : 2 < q.length)).1 ha
  have hnb' : ∀ i, i+2 ≤ q.reverse.length →
      q.reverse.getVert i ≠ q.reverse.getVert (i+2) := by
    intro i hi
    rw [length_reverse,hlen] at hi
    simp only [getVert_reverse,hlen]
    convert (hnb (3-i) (by omega)).symm using 1 <;> congr 1 <;> omega
  have ho := five_walk_fixer_odd_oriented hab hfix q.reverse (by rwa [length_reverse]) hnb'
    (by simpa only [getVert_reverse,hlen] using ha3)
  rwa [pathFixer_reverse] at ho

/-- Every nonbacktracking five-walk has odd fixer, in both orientations and
without requiring the source graph to be a tree. -/
theorem source_unitary_five_walk_fixer_odd_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (hk : Nat.card k = 2^(2*n))
    {x y : Vertex (family P)} (q : (graph (family P)).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := G) q)) := by
  let := finite_endpoints h
  apply five_walk_fixer_odd_of_middle_edge (source_critical_one_adjacent hc hb) ?_ q hlen hnb
  intro v₀ t w v₅ h0t hta hbw hw5 h0a htb haw hb5
  exact source_unitary_five_edge_fixer_odd_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne hn mark ea hk
    h0t hta hbw hw5 h0a htb haw hb5

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
