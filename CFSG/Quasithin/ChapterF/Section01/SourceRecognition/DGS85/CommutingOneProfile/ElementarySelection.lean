module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Elementary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallAlphaExclusions

/-!
# Source quotient selection through the actual edge Sylow

The edge two-core maps onto a Sylow subgroup of the local quotient, with
kernel exactly the vertex two-core restricted to that edge group. The
quotient equivalence therefore transfers elementary abelianness in either
direction. The model catalogue selects linear or D10 in the elementary
case, and Suzuki or either unitary cover in the nonelementary case.

For alpha, the independent (11.3)(h) pair-core identity and (11.4) product
make this quotient elementary. The nonquadratic seed obstruction then
excludes D10 and the binary linear field, giving the genuine (11.5)
linear marking. The two general core identities remain explicit inputs;
no identity proved only under linear alpha is used to select alpha.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.5), printed pp.169--172; the split in (11.7)--(11.8),
printed pp.174--176. That split concerns S/Q_beta, distinct from (11.5).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal edge-core quotient is a Sylow of the actual local quotient. -/
theorem source_edge_core_quotient_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    [hN : ((Q (family P) a).subgroupOf
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal] :
    ∃ T : Sylow 2 (d.localGroup a ⧸ pCore 2 (d.localGroup a)),
      Nonempty ((((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) a).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)) ≃* T) := by
  let := finite_endpoints h
  let L := d.localGroup a
  let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  obtain ⟨U,hU⟩ := source_edge_core_local_sylow h hB d hab
  change (U : Subgroup L).map L.subtype = R at hU
  let q := QuotientGroup.mk' (pCore 2 L)
  let T := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hRL : R ≤ L := by rw [←hU]; exact map_subtype_le _
  let j : R →* L := inclusion hRL
  have hjU (x : R) : j x ∈ (U : Subgroup L) := by
    obtain ⟨y,hy,he⟩ := (show x.val ∈ (U : Subgroup L).map L.subtype by rw [hU]; exact x.property)
    exact (Subtype.ext he : y = j x) ▸ hy
  let f : R →* T := (q.comp j).codRestrict (T : Subgroup (L ⧸ pCore 2 L))
    (fun x => mem_map_of_mem q (hjU x))
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨u,hu,rfl⟩ := hx
    have huR : u.val ∈ R := by rw [←hU]; exact mem_map_of_mem L.subtype hu
    exact ⟨⟨u.val,huR⟩,rfl⟩
  have hk : (Q (family P) a).subgroupOf R = f.ker := by
    ext x
    change x.val ∈ Q (family P) a ↔ f x = 1
    rw [←localGroup_core_eq (family P) d a]
    constructor
    · rintro ⟨y,hy,he⟩
      apply Subtype.ext
      change q (j x) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      exact (Subtype.ext he : y = j x) ▸ hy
    · intro hx
      have hxq : q (j x) = 1 := congrArg Subtype.val hx
      exact mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff _).mp hxq)
  exact ⟨T,⟨QuotientGroup.liftEquiv _ hf hk⟩⟩

/-- Model selection from the elementary quotient of the original edge radical. -/
theorem source_linear_or_dihedral_of_elementary_edge (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (M : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (helem : ∃ hN : ((Q (family P) a).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      let := hN
      IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) a).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))) :
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n)) ∨
      Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) := by
  obtain ⟨hN,helem⟩ := helem
  let := hN
  let := helem
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d hab
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  exact M.linear_or_dihedral_of_elementary_sylow T

/-- Source (11.5): the two earlier core identities select a genuine linear
alpha row; neither identity is inferred from a linear marking. -/
theorem source_alpha_linear_of_core_identities (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hproduct : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b)
    (hcore : Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b)) :
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  let := source_center_elementary h c
  have hab := source_critical_one_adjacent hc hb
  let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  let hN : ((Q (family P) a).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ a))
  have helem : IsElementaryAbelian 2 (R ⧸ (Q (family P) a).subgroupOf R) :=
    alpha_quotient_elementary_of_pair_generation _ _ _ _ _ hproduct hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  rcases source_linear_or_dihedral_of_elementary_edge h hB d hab Ma ⟨hN,helem⟩ with
    ⟨n,hn,ha⟩ | ea
  · obtain ⟨k,_,_,hcard,⟨ea⟩⟩ := ha
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let ep : Matrix.SpecialLinearGroup (Fin 2) k ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    have hne := source_alpha_linear_field_card_ne_two h hB d hc hb hcomm hbc hac Mb (ea.trans ep.symm)
    have hn1 : n ≠ 1 := by
      intro he
      apply hne
      simpa only [he,pow_one] using hcard
    exact ⟨n,by omega,k,inferInstance,inferInstance,hcard,⟨ea⟩⟩
  · exact (source_alpha_dihedral_exclusion h hB d hc hb hcomm hbc hac Mb ea.some).elim

/-- The complementary source branch retains Suzuki and both unitary quotient
forms, with their actual model isomorphisms and all small parameters. -/
theorem source_nonlinear_of_nonElementary_edge (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (M : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (hne : ∃ hN : ((Q (family P) a).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) a).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))) :
    (∃ m, Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      ∃ n, 0 < n ∧ (ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n) ∨
        IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n)) := by
  obtain ⟨hN,hne⟩ := hne
  let := hN
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d hab
  apply M.suzuki_or_unitary_of_nonElementary_sylow T
  intro he
  let := he
  exact hne (IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
