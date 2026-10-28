module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedFieldParameters

/-!
# Original natural alpha coordinates and the full Borel

The source field equation supplies the actual alpha field and local quotient
marking. The alpha Frattini and natural-action theorems then construct a
surjective coordinate map on the original alpha core, with kernel exactly
the original alpha center. Equivariance is for ambient conjugation by the
original local group and its literal quotient by its two-core.

Both beta unitary covers and every positive fixed-field degree are retained.
The full-Borel application identifies the reduced edge core with O₂ of the
original common Borel; its nonelementary quotient hypothesis is transported
through that equality. Earlier local theorems, the escaping source path and
path transitivity remain explicit for their source assembly owners.
Source: DGS85, Groups and Graphs (1985), (11.8)(c)--(f), printed pp.175--176.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
private theorem alpha_nonElementary_of_mapped_quotient {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    (hne : ∃ hn : ((N.map f).subgroupOf (R.map f)).Normal, letI := hn
      ¬ IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f))) :
    ¬ IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  intro he
  obtain ⟨hn,hne⟩ := hne
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
  exact hne (IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective)


/-- Natural coordinates and the Frattini kernel under the original inclusion. -/
theorem original_reduced_unitary_alpha_natural_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)))
    (m : ℕ) (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m)) :
    let R := (Q F₀ a).map (G₀).subtype
    let A := (Z F₀ a).map (G₀).subtype
    let L := (d.localGroup a).map (G₀).subtype
    (frattini R).map R.subtype = A ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        Nat.card k = 2^(2*m) ∧
        ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
          ∃ f : R →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
            f.ker = A.subgroupOf R ∧
            ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
              (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val (f x).toAdd := by
  let eL := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let S := (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2
  let hN : ((Q F₀ b).subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have hQS : Q F₀ b ≤ S := by
    have hh := Noncommuting.graph_Q_le_edgeCore
      (Reduction.reduced_triple h) (source_critical_one_adjacent hc hb).symm
    change Q F₀ b ≤ (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2 at hh
    rwa [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)] at hh
  have hnot := alpha_nonElementary_of_mapped_quotient S (Q F₀ b) hQS
    (G₀).subtype (G₀).subtype_injective hne
  have mark' : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  have hphi := (source_unitary_alpha_frattini_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp ⟨hN,hnot⟩ hm mark').1
  change (frattini (Q F₀ a)).map (Q F₀ a).subtype = Z F₀ a at hphi
  dsimp only
  refine ⟨?_,?_⟩
  · rw [frattini_image_map _ _ (G₀).subtype_injective,hphi]
  · obtain ⟨k,_,_,hk,⟨ea₀⟩⟩ := (original_reduced_unitary_field_orders_on_escaping_path h d hc hb hcomm
      hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m hm mark).1
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hk)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    let ea := ea₀.trans ep.symm
    obtain ⟨f,hf,hker,hact⟩ := source_unitary_alpha_natural_on_escaping_path
      (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      g hga hgb (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
      ⟨hN,hnot⟩ hm mark' (eqa.trans ea) hk
    let eR := (Q F₀ a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    let f₀ := f.comp eR.symm.toMonoidHom
    refine ⟨k,inferInstance,inferInstance,inferInstance,hk,ea,f₀,hf.comp eR.symm.surjective,?_,?_⟩
    · ext x
      obtain ⟨x,rfl⟩ := eR.surjective x
      change f (eR.symm (eR x)) = 1 ↔ (eR x : G) ∈ (Z F₀ a).map (G₀).subtype
      rw [eR.symm_apply_apply]
      change x ∈ f.ker ↔ _
      rw [hker]
      constructor
      · intro hx
        exact mem_map_of_mem (G₀).subtype hx
      · rintro ⟨z,hz,he⟩
        have he' : z = (x : G₀) := (G₀).subtype_injective he
        change (x : G₀) ∈ Z F₀ a
        exact he' ▸ hz
    · intro l x y hy
      obtain ⟨l,rfl⟩ := eL.surjective l
      obtain ⟨x,rfl⟩ := eR.surjective x
      obtain ⟨y,rfl⟩ := eR.surjective y
      have he : (y : G₀) = (l : G₀) * (x : G₀) * (l : G₀)⁻¹ := by
        apply (G₀).subtype_injective
        exact hy
      have hh := hact l x y he
      change (f (eR.symm (eR y))).toAdd =
        Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 ((d.localGroup a).map (G₀).subtype)) (eL l))).val
          (f (eR.symm (eR x))).toAdd
      rw [eR.symm_apply_apply,eR.symm_apply_apply]
      exact hh

/-- The same natural action with the nonelementary quotient of the full Borel. -/
theorem original_borel_unitary_alpha_natural_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false)) (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤ (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • (base F₀ true) ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀))))
    (m : ℕ) (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) :
    let R := (Q F₀ (base F₀ false)).map (G₀).subtype
    let A := (Z F₀ (base F₀ false)).map (G₀).subtype
    let L := (d.localGroup (base F₀ false)).map (G₀).subtype
    (frattini R).map R.subtype = A ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        Nat.card k = 2^(2*m) ∧
        ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
          ∃ f : R →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
            f.ker = A.subgroupOf R ∧
            ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
              (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val (f x).toAdd := by
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
  have hne' := hne
  rw [←hmap] at hne'
  exact original_reduced_unitary_alpha_natural_on_escaping_path h d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne' m hm mark

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
