module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Edge
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.FieldExtension
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# The original M23-shaped coset uniqueness system

Construct the actual source coset graph, its stabilizers and all three
generation identities. Its vertex set remains G/(L ∨ H); the exceptional
local marking records the compatible native heptad and four-set stabilizers.
Source: Aschbacher--Smith 5.2.19--5.2.22, printed pp.656--657.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G]

theorem Preparation.linear_exceptional_coset_system
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧ U.H ≤ J ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) := by
  obtain ⟨ζ,I,t,hcore,hK,hHm,hMm,hI,htI,hswap,hne,horbit,htx,hxI,hxyI,hedgeI,hfix,hvertex,hlocal,hglobal⟩ :=
    d.linear_exceptional_coset_edge_geometry h hH hp F hm hF he hJ hKJ
  let X := L ⊔ H
  let x0 := ((1 : G) : G ⧸ X)
  let y0 := t • x0
  have ht : (t:G) ∉ X := by
    intro hh
    have hx : (t:G) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.stabilizer_quotient]; exact hh
    exact hne (show t • x0 = x0 from hx).symm
  have hy : y0 = Cosets.vertex X (t:G) := by
    change Cosets.vertex X ((t:G)*1) = _
    rw [mul_one]
  have hX : X ≠ ⊤ := fun hh => ht (hh.symm ▸ mem_top _)
  have hcoreX : X.normalCore = ⊥ := by
    let : IsSimpleGroup G := h.qtke.simple
    rcases (inferInstance : X.normalCore.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · exact (hX (top_unique (hh ▸ X.normalCore_le))).elim
  let U : System G (G ⧸ X) := {
    graph := Cosets.graph X (t:G) ht
    H := I.map J.subtype
    x := x0
    y := y0
    adjacent := by rw [hy]; exact Cosets.graph_adj_base X (t:G) ht
    preserves := Cosets.preserves X (t:G) ht
    faithful := Cosets.faithful X hcoreX
    vertex_transitive := Cosets.transitive X
    edge_transitive := by rw [hy]; exact Cosets.edge_transitive X (t:G) ht
    local_orbit := ⟨⟨t,⟨t,htI,rfl⟩⟩,rfl⟩
    generate := by change I.map J.subtype ⊔ MulAction.stabilizer G x0 = ⊤
                   rw [MulAction.stabilizer_quotient]; exact hglobal
    vertex_generate := by change edgeFixer G x0 y0 ⊔ (I.map J.subtype ⊓ MulAction.stabilizer G x0) = _
                          rw [hfix,MulAction.stabilizer_quotient]; exact hvertex
    local_generate := hlocal }
  have hIU : U.H.subgroupOf J = I := by
    ext j
    change (j:G) ∈ I.map J.subtype ↔ j ∈ I
    constructor
    · rintro ⟨i,hi,he⟩
      exact (show i = j from Subtype.ext he) ▸ hi
    · intro hj
      exact ⟨j,hj,rfl⟩
  have hmap (R : Subgroup G) : (U.H ⊓ R).subgroupOf J = I ⊓ R.subgroupOf J := by
    change U.H.subgroupOf J ⊓ R.subgroupOf J = _
    rw [hIU]
  refine ⟨U,ζ,rfl,MulAction.stabilizer_quotient X,hfix,map_subtype_le _, hcore,hK,hHm,hMm,?_,?_,?_,?_,horbit,?_⟩
  · rw [hIU]; exact hI
  · rw [hmap]; exact hxI
  · rw [hmap]; exact hxyI
  · rw [hmap]; exact hedgeI
  · exact ⟨t,⟨t,htI,rfl⟩,rfl,htx⟩

theorem Preparation.linear_nonmaximal_coset_system
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧ U.H ≤ J ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) := by
  obtain ⟨_,hcases⟩ := d.linear_maximal_or_exceptional h hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hcases.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_coset_system h hH hp F hm hF he hJ hKJ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
