module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryInitial
public import Theory.SpecificGroups.SU3.SylowOmegaIndex

/-!
# The nonelementary quotient of the original unitary Borel

The beta quotient of the edge two-core is a Sylow subgroup of the marked
unitary local quotient. Its omega-center has index q squared, including
q=2, so this quotient cannot be elementary abelian. Transport along the
literal inclusion identifies the edge two-core with the two-core of the
whole original Borel. This supplies the branch premise of (11.8), without
any path-transitivity hypothesis and for both unitary covers.
Source: DGS85 (5.4), (11.8), pp.106--107,175--176.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem unitary_sylow_not_elementary {H : Type*} [Group H]
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU H 3 (2^m) ∨ IsSU H 3 (2^m))
    (T : Sylow 2 H) : ¬ IsElementaryAbelian 2 T := by
  intro he
  let := he
  let : Finite H := (show IsRankOneModel H from mark.elim
    (.projective_unitary m hm) (.special_unitary m hm)).finite
  have exclude {D : Type} [Group D] (e : H ≃* D)
      (hidx : ∀ R : Sylow 2 D, (omegaCenterIn (R : Subgroup D)).relIndex R = (2^m)^2) : False := by
    let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
    let : IsElementaryAbelian 2 R := IsElementaryAbelian.map e.toMonoidHom
    have ho : omegaCenterIn (R : Subgroup D) = R := by
      apply le_antisymm (map_subtype_le _)
      intro x hx
      exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
        fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : R) (⟨x,hx⟩ : R)),
        elemPow_eq_one_of_isElementaryAbelian x hx⟩
    have hi := hidx R
    rw [ho,relIndex_self] at hi
    have hpow : 1 < (2^m)^2 := one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
    omega
  rcases mark with ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
  · exact exclude e (fun R => (HermitianForm.SylowOmegaIndex.projective J hm hcard hconj R).2)
  · exact exclude e (fun R => (HermitianForm.SylowOmegaIndex.special J hm hcard hconj R).2)

/-- A unitary local marking proves nonelementarity of the literal edge-core
quotient; no critical-pair or path premise is needed. -/
theorem source_unitary_edge_quotient_not_elementary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^m) ∨
      IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^m)) :
    ∃ hN : ((Q (family P) a).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) a).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)) := by
  let hN : ((Q (family P) a).subgroupOf
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ a))
  refine ⟨hN,?_⟩
  intro he
  let := he
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d hab
  exact unitary_sylow_not_elementary hm mark T
    (IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective)

section Original
open Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The full original Borel lies in the nonelementary branch under either
unitary beta marking, with the actual reduced-to-original inclusion. -/
theorem original_borel_unitary_quotient_not_elementary
    (h : HypothesisF11 L₀ S₀) {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) :
    ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀))) := by
  let d := reducedFullEarlierLocalTheorems h
  let eb := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have mark' : ClassicalGroup.IsPSU (d.localGroup (base F₀ true) ⧸
      pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) ∨
      IsSU (d.localGroup (base F₀ true) ⧸
        pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  have htr := reduced_triple h
  have hBG : B₀ L₀ S₀ ≤ G₀ :=
    (show B₀ L₀ S₀ ≤ P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ B₀ L₀ S₀ from le_sup_right).trans hBG
  let R := (stabilizer F₀ (base F₀ true) ⊓ stabilizer F₀ (base F₀ false)).pCoreIn 2
  let N := Q F₀ (base F₀ true)
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [inf_comm (stabilizer F₀ (base F₀ true)),
      show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  have hab : (graph F₀).Adj (base F₀ true) (base F₀ false) :=
    ⟨show true ≠ false from by decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hNR : N ≤ R := Noncommuting.graph_Q_le_edgeCore htr hab
  obtain ⟨hN,hne⟩ := source_unitary_edge_quotient_not_elementary htr
    (reduced_borel_core_sylow h) d hab hm mark'
  let : (N.subgroupOf R).Normal := hN
  have hn : R ≤ normalizer (N : Set G₀) :=
    ((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ _)
  let hN' : ((N.map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((map_mono hn).trans (N.le_normalizer_map (G₀).subtype))
  rw [←hmap]
  refine ⟨hN',?_⟩
  intro he
  let := he
  let eR := R.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  have heN : (N.subgroupOf R).map eR.toMonoidHom =
      (N.map (G₀).subtype).subgroupOf (R.map (G₀).subtype) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem (G₀).subtype hy
    · rintro ⟨y,hy,hyx⟩
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext hyx⟩
  let eqR := QuotientGroup.congr _ _ eR heN
  exact hne (IsElementaryAbelian.of_surjective eqR.symm.toMonoidHom eqR.symm.surjective)

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
