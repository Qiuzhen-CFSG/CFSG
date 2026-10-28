module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearBetaProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaCenterBound

/-!
# The elementary-beta source branch on the full original Borel

The literal quotient S_0/Q_beta is a Sylow subgroup of the marked local
quotient. Elementary abelianness selects a linear or D10 beta row; the
proved arbitrary-linear-alpha exclusion eliminates D10. The linear/linear
module argument then supplies q_alpha=q_beta², the core identities and
the source (11.7)(c) order q_alpha² q_beta² without a beta linear marking.

Both local quotient markings and the branch hypothesis transport through
the actual reduced-group inclusion. At the base edge its radical image
is O2 of the full original Borel, giving the original numerical conclusion.
The independent (11.3)(h) and (11.4) identities also give a conditional
application without preselecting alpha. Their general proofs remain
explicit obligations; no linear-alpha identity is used circularly.
The complementary branch retains Suzuki, PSU3 and SU3, including all
small field parameters. Its further exclusion and structural arguments,
and the remaining paths and marked assembly, are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.8), printed pp.169--176; reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

/-- In the elementary S/Q_beta branch, beta is linear. The existing arbitrary-field
D10 exclusion discharges the dihedral alternative without a field-four premise. -/
theorem reduced_linear_elementary_beta_selection (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) := by
  rcases source_linear_or_dihedral_of_elementary_edge (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d (source_critical_one_adjacent hc hb).symm Mb
    (by
      change ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2)).Normal,
        letI := hN
        IsElementaryAbelian 2 (((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2) ⧸
          (Q F₀ b).subgroupOf ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2))
      rw [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)]
      exact helem) with hm | eb
  · exact hm
  · exact (reduced_linear_dihedral_exclusion h d hc hb hcomm n hn ha eb.some).elim

/-- The core and numerical clauses of (11.7) from its literal elementary-beta
hypothesis, with the beta row and both field restrictions derived. -/
theorem reduced_linear_elementary_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) ∧
      n = 2*m ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2^m ∧ Nat.card (Z F₀ a) = (2^n)^2 ∧
      Nat.card (Q F₀ b) = (2^n)^2 * 2^m ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = (2^n)^2 * (2^m)^2 := by
  obtain ⟨m,hm,hmodel⟩ := reduced_linear_elementary_beta_selection h d hc hb hcomm n hn ha Mb helem
  exact ⟨m,hm,hmodel,reduced_linear_linear_profile h d hc hb hcomm n m hn hm ha hmodel⟩

/-- With the independent (11.3)(h) and (11.4) identities, neither endpoint
needs a preselected linear marking. The elementary branch remains S/Q_beta. -/
theorem reduced_elementary_profile_of_core_identities (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hproduct : (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b)
    (hcore : Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ⊔ (Q F₀ a ⊓ Q F₀ b))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    ∃ n m, 1 < n ∧ 0 < m ∧
      ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) ∧
      ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) ∧
      n = 2*m ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2^m ∧ Nat.card (Z F₀ a) = (2^n)^2 ∧
      Nat.card (Q F₀ b) = (2^n)^2 * 2^m ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = (2^n)^2 * (2^m)^2 := by
  obtain ⟨n,hn,ha⟩ := source_alpha_linear_of_core_identities (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac Ma Mb hproduct hcore
  obtain ⟨m,hm,hmodel,hs⟩ := reduced_linear_elementary_profile h d hc hb hcomm n (by omega) ha Mb helem
  exact ⟨n,m,hn,hm,ha,hmodel,hs⟩

/-- The elementary branch preserves the original quotient markings and all
literal subgroup images, with no prescribed beta field or beta linear marking. -/
theorem original_reduced_linear_elementary_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
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
  obtain ⟨m,hm,hmodel⟩ := reduced_linear_elementary_beta_selection h d hc hb hcomm n hn
    (ha.of_mulEquiv eqa) (Mb.of_equiv eqb) helem
  have hmorig := hmodel.of_mulEquiv eqb.symm
  exact ⟨m,hm,hmorig,original_reduced_linear_linear_profile h d hc hb hcomm n m hn hm ha hmorig⟩

/-- Source (11.7)(c) on the full original Borel under its literal elementary
beta branch; the beta quotient and its parameter are selected from the catalogue. -/
theorem original_linear_elementary_borel_core_order (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2 ^ n))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (helem : ∃ hN : ((Q F₀ (base F₀ true)).subgroupOf
        ((stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2) ⧸
        (Q F₀ (base F₀ true)).subgroupOf
          ((stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m) ∧
      n = 2*m ∧ Nat.card (twoCore (commonBorel L S)) = (2^n)^2 * (2^m)^2 := by
  obtain ⟨m,hm,hmodel,_⟩ := original_reduced_linear_elementary_profile h d hc hb hcomm n hn ha Mb helem
  exact ⟨m,hm,hmodel,original_linear_linear_borel_core_order h d hc hb hcomm n m hn hm ha hmodel⟩

/-- The nonelementary S/Q_beta branch excludes the linear and dihedral rows
without selecting SU3 from PSU3 or excluding the small field parameters. -/
theorem reduced_nonElementary_beta_selection (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀) {a b : Vertex F₀} (hab : (graph F₀).Adj a b)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hne : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    (∃ m, Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      ∃ n, 0 < n ∧ (ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
        IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) := by
  apply source_nonlinear_of_nonElementary_edge (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hab.symm Mb
  change ∃ hN : ((Q F₀ b).subgroupOf
    ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2)).Normal,
    letI := hN
    ¬ IsElementaryAbelian 2 (((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2) ⧸
      (Q F₀ b).subgroupOf ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2))
  rw [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)]
  exact hne

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

/-- The branch premise itself can be given on O2 of the full original
Borel, modulo the original image of Q_beta. It is pulled back through the
same inclusion used for both local quotient markings and the resulting order. -/
theorem original_borel_elementary_beta_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2 ^ n))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (helem : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L S)))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m) ∧
      n = 2*m ∧ Nat.card (twoCore (commonBorel L S)) = (2^n)^2 * (2^m)^2 := by
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have ht := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L S ≤ G₀ :=
    (show Reduction.B₀ L S ≤ Reduction.P₀ L S 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L S) ≤ G₀ :=
    (show twoCore (commonBorel L S) ≤ Reduction.B₀ L S from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L S) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L S).subgroupOf G₀ from ht.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  let hN : ((Q F₀ (base F₀ true)).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have hQR : Q F₀ (base F₀ true) ≤ R := by
    have hq := Noncommuting.graph_Q_le_edgeCore ht
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
  exact original_linear_elementary_borel_core_order h d hc hb hcomm n hn ha Mb ⟨hN,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
