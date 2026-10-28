module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedPairCoreSpan

/-!
# Elementary Chapter 11 profiles without a prescribed alpha row

The branch hypothesis is the literal elementary quotient S/Q_beta. Its
critical-center image proves the edge-core product. The independently
proved pair-span identity on the source path then selects a linear alpha
row, excluding its degree-one and dihedral alternatives. The existing
linear-alpha theorem selects linear beta, excludes D10, and supplies the
field relation q_alpha = q_beta^2, both core identities and all local orders. The direct D10 exclusion constructs its own elementary
branch from the actual Sylow marking before deriving alpha.

The original-image application keeps both actual quotient markings and
the reduced-group inclusion. The base-edge consumer accepts elementary
abelianness on O2 of the full original Borel modulo the original beta-core
image, and proves its exact order q_alpha^2 q_beta^2. It assumes neither
core identity nor either linear marking. The actual earlier local data,
rank-one catalogue and transitive source path remain explicit inputs.

These are the algebraic clauses (11.7)(a)--(e), not the remaining path
parameters in (f) or a marked amalgam recognition. The general nonelementary
(11.4) comparison and all (11.8) duties remain separate.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.7), printed pp.169--175, and reduction pp.95--96.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The elementary-beta hypothesis and the earlier source path derive both
linear rows and (11.7)(c)--(e), with no core-product or core-span premise. -/
theorem reduced_elementary_profile_of_elementary_beta_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ∃ n m, 1 < n ∧ 0 < m ∧
      ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) ∧
      ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) ∧
      n = 2*m ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2^m ∧ Nat.card (Z F₀ a) = (2^n)^2 ∧
      Nat.card (Q F₀ b) = (2^n)^2 * 2^m ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = (2^n)^2 * (2^m)^2 := by
  have hproduct := source_elementary_beta_core_product (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb Mb helem
  exact reduced_elementary_profile_on_path h d hc hb hcomm hbc hac Ma Mb hproduct helem
    ht p hp ha hb' hc'

/-- Both selected endpoint quotient markings and all core orders transport
through the literal reduced-to-original inclusion. -/
theorem original_reduced_elementary_profile_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸ pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ∃ n m, 1 < n ∧ 0 < m ∧
      ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n) ∧
      ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 2 (2^m) ∧
      n = 2*m ∧ (Q F₀ a).map (G₀).subtype = (Z F₀ a).map (G₀).subtype ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^m ∧
      Nat.card ((Q F₀ a).map (G₀).subtype) = (2^n)^2 ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = (2^n)^2 * 2^m ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (2^n)^2 * (2^m)^2 := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨n,m,hn,hm,ha',hb',_⟩ := reduced_elementary_profile_of_elementary_beta_on_path
    h d hc hb hcomm hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) helem ht p hp ha hb' hc'
  have han := ha'.of_mulEquiv eqa.symm
  have hbm := hb'.of_mulEquiv eqb.symm
  exact ⟨n,m,hn,hm,han,hbm,original_reduced_linear_linear_profile
    h d hc hb hcomm n m (by omega) hm han hbm⟩

private theorem elementary_of_mapped_quotient {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    (he : ∃ hn : ((N.map f).subgroupOf (R.map f)).Normal, letI := hn
      IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f))) :
    IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  obtain ⟨hn,he⟩ := he
  let := hn
  let := he
  let e := R.equivMapOfInjective f hf
  have hmap : (N.subgroupOf R).map e.toMonoidHom = (N.map f).subgroupOf (R.map f) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem f hy
    · intro hx
      obtain ⟨y,hy,heq⟩ := hx
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩
  let eq := QuotientGroup.congr _ _ e hmap
  exact IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective

/-- The full original Borel carries the elementary-beta branch hypothesis
and the exact source (11.7)(c) order; neither linear row is an input. -/
theorem original_borel_elementary_profile_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    {c : Vertex F₀} (hbc : (graph F₀).Adj (base F₀ true) c)
    (hac : base F₀ false ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (helem : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀))))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : base F₀ false ∈ p.vertices) (hb' : base F₀ true ∈ p.vertices)
    (hc' : c ∈ p.vertices) :
    ∃ n m, 1 < n ∧ 0 < m ∧
      ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^n) ∧
      ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m) ∧
      n = 2*m ∧ Nat.card (twoCore (commonBorel L₀ S₀)) = (2^n)^2 * (2^m)^2 := by
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L₀ S₀ ≤ G₀ :=
    (show Reduction.B₀ L₀ S₀ ≤ Reduction.P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ Reduction.B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  let hN : ((Q F₀ (base F₀ true)).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have hQR : Q F₀ (base F₀ true) ≤ R := by
    have hq := Noncommuting.graph_Q_le_edgeCore htr
      (source_critical_one_adjacent hc hb).symm
    change Q F₀ (base F₀ true) ≤
      (stabilizer F₀ (base F₀ true) ⊓ stabilizer F₀ (base F₀ false)).pCoreIn 2 at hq
    rw [inf_comm (stabilizer F₀ (base F₀ true)) (stabilizer F₀ (base F₀ false))] at hq
    exact hq
  have he : IsElementaryAbelian 2 (R ⧸ (Q F₀ (base F₀ true)).subgroupOf R) :=
    elementary_of_mapped_quotient R _ hQR (G₀).subtype (G₀).subtype_injective
      (by
        rw [hmap]
        exact helem)
  obtain ⟨n,m,hn,hm,han,hbm,_⟩ := original_reduced_elementary_profile_on_path
    h d hc hb hcomm hbc hac Ma Mb ⟨hN,he⟩ ht p hp ha hb' hc'
  exact ⟨n,m,hn,hm,han,hbm,original_linear_linear_borel_core_order
    h d hc hb hcomm n m (by omega) hm han hbm⟩

/-- D10 is excluded directly from its actual beta marking and the earlier
source path. Neither an elementary-quotient nor a linear-alpha premise is added. -/
theorem reduced_dihedral_beta_exclusion_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) : False := by
  have htr := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hab := source_critical_one_adjacent hc hb
  let R := (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2
  let hN : ((Q F₀ b).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ b))
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow htr hB d hab.symm (hN := hN)
  change (R ⧸ (Q F₀ b).subgroupOf R) ≃* T at e
  let := dihedral_model_sylow_elementary eb T
  have he : IsElementaryAbelian 2 (R ⧸ (Q F₀ b).subgroupOf R) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)) := by
    rw [inf_comm (stabilizer F₀ a) (stabilizer F₀ b)]
    exact ⟨hN,he⟩
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  have hproduct := source_elementary_beta_core_product htr hB d hc hb Mb helem
  have hcore := source_rankOne_pair_core_span_on_path htr hB d hc hb hbc hac Ma Mb
    ht p hp ha hb' hc'
  obtain ⟨n,hn,han⟩ := source_alpha_linear_of_core_identities htr hB d hc hb hcomm hbc hac
    Ma Mb hproduct hcore
  exact reduced_linear_dihedral_exclusion h d hc hb hcomm n (by omega) han eb

/-- The same D10 exclusion retains the original beta quotient isomorphism
and the original alpha catalogue, transported through the actual inclusion. -/
theorem original_reduced_dihedral_beta_exclusion_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸ pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* DihedralGroup 5)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) : False := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eβ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqβ := QuotientGroup.congr _ _ eβ (pCore_map_iso 2 eβ)
  exact reduced_dihedral_beta_exclusion_on_path h d hc hb hcomm hbc hac
    (Ma.of_equiv eqa) (eqβ.trans eb) ht p hp ha hb' hc'

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
