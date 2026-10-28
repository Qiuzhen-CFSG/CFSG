module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCubic
public import Theory.GroupTheory.ResidualComplementAutomizer

/-!
# The cubic automizer in the original tensor point centralizer

For every Sylow three-subgroup P of X, Frattini factorization identifies
Aut_T(P) with the Sylow image of T in XT/O₂(XT). The previously proved
wreath quotient therefore identifies this actual automizer with D₈.
The comparison preserves P, the normalizer N_T(P), and the quotient map;
it uses equality of action kernels rather than an order comparison.

This excludes the cyclic symplectic alternative of the Chapter1 embedding
theorem in the original C_G(z). The linear-three, Mathieu, Held, normal,
and swapped alternatives remain explicit. The tensor-base marking is
still a hypothesis; the remaining ambient centralizer analysis and quiet
fixed-support exclusions stay with the selected-module owner.
Source: Aschbacher--Smith 8.3.7, printed p.724.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem cubic_automizer_dihedral {X P H : Subgroup G}
    (h : Chapter1.XiEmbedding.LocalInput 3 (T : Subgroup G) X P H)
    (e : ((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) ≃* WreathTwoResidual.Actor) :
    Nonempty (Chapter1.XiEmbedding.automizer (T : Subgroup G) P ≃* DihedralGroup 4) := by
  let J := X ⊔ (T : Subgroup G)
  have hXJ : X ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hPJ : P ≤ J := (le_sup_right.trans h.complement.le).trans hXJ
  let q : J →* WreathTwoResidual.Actor :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcore : X.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hXJ (sup_le X.le_normalizer h.invariant)
  have hCK : (X.pCoreIn 2).subgroupOf J ≤ q.ker := by
    rw [hk]
    intro x hx
    obtain ⟨y,hy,he⟩ := hcore hx
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  have hr : pResidual 2 J = X.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hXJ]
    exact embedded_pResidual_join_pGroup X (T : Subgroup G) h.perfect T.isPGroup' h.invariant
  have hc : (X.pCoreIn 2).subgroupOf J ⊔ P.subgroupOf J = X.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXJ),
      map_subgroupOf_eq_of_le hPJ,map_subgroupOf_eq_of_le hXJ,h.complement]
  have hp : (P.subgroupOf J).map q = pResidual 2 WreathTwoResidual.Actor := by
    have hh := congrArg (fun A : Subgroup J => A.map q) hc
    rw [Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hCK,bot_sup_eq,←hr,
      map_pResidual_of_surjective 2 q hq] at hh
    exact hh
  have hd : Disjoint (P.subgroupOf J) q.ker := by
    rw [hk]
    exact IsPGroup.disjoint_of_ne 3 2 (by decide) _ _
      (Chapter1.isSylowIn_iff.mp h.sylow).1.comap_subtype pCore_isPGroup
  have hfactor : (T : Subgroup G).subgroupOf J ≤ q.ker ⊔
      ((T : Subgroup G).subgroupOf J ⊓ normalizer (P.subgroupOf J : Set J)) := by
    have hh : (T : Subgroup G).subgroupOf J = (X.pCoreIn 2).subgroupOf J ⊔
        ((T : Subgroup G) ⊓ normalizer (P : Set G)).subgroupOf J := by
      apply map_injective J.subtype_injective
      rw [map_subgroupOf_eq_of_le hTJ,Subgroup.map_sup,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXJ),
        map_subgroupOf_eq_of_le (inf_le_left.trans hTJ)]
      exact h.normalizer_factor
    conv_lhs => rw [hh]
    apply sup_le_sup hCK
    change ((T : Subgroup G).subgroupOf J ⊓ (normalizer (P : Set G)).subgroupOf J) ≤ _
    rw [subgroupOf_normalizer_eq hPJ]
  obtain ⟨a⟩ := normalizer_action_range_equiv_subgroupOf (T : Subgroup G) P J hTJ hPJ
  obtain ⟨b⟩ := complement_automizer_equiv_image q ((T : Subgroup G).subgroupOf J)
    (P.subgroupOf J) T.isPGroup'.comap_subtype WreathTwoResidual.twoCore_eq_bot hp hd hfactor
  obtain ⟨c⟩ := wreath_two_sylow_mulEquiv_dihedral_four ((T.subtype hTJ).mapSurjective hq)
  exact ⟨a.trans (b.trans c)⟩

variable {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- The actual cubic automizer in 8.3.7 is dihedral of order eight, for
 every Sylow three-subgroup of the original point residual. -/
theorem quiet_tensor_point_automizer_dihedral
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    Nonempty (Chapter1.XiEmbedding.automizer (T : Subgroup G)
      ((P : Subgroup d.X).map d.X.subtype) ≃* DihedralGroup 4) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXi := quiet_tensor_point_residual_mem_Xi D hn e hbase hzV hz1 hzT
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hXT : d.XT ≤ d.Gz := sup_le (d.X_le.trans inf_le_right) hzT
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient d.X) := by
    refine Or.inl ⟨IsElementaryAbelian.of_injective c.toMonoidHom c.injective,?_⟩
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨b⟩ := quiet_tensor_point_quotient D hn e hbase hzV hz1 hzT
  exact cubic_automizer_dihedral
    (Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hT hXT (by decide) hq P) b
/-- The original cubic automizer cannot be cyclic. This excludes the
symplectic alternative in the actual Chapter1 embedding theorem. -/
theorem quiet_tensor_point_automizer_not_cyclic
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    ¬ IsCyclic (Chapter1.XiEmbedding.automizer (T : Subgroup G)
      ((P : Subgroup d.X).map d.X.subtype)) := by
  dsimp only
  obtain ⟨c⟩ := quiet_tensor_point_automizer_dihedral D hn e hbase hzV hz1 hzT P
  intro hc
  let := hc
  exact DihedralGroup.not_isCyclic (by decide : 4 ≠ 1)
    (isCyclic_of_surjective c.toMonoidHom c.surjective)

open Chapter1.XiEmbedding in
/-- The literal 8.3.7 embedding alternatives after excluding the cyclic
symplectic branch. The linear-three, Mathieu, Held and swapped alternatives
remain genuine ambient obligations. -/
theorem quiet_tensor_point_embedding_reduced
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let P₀ := (P : Subgroup d.X).map d.X.subtype
    (d.X.subgroupOf d.Gz).Normal ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn d.Gz ∧ IsQuasisimple (Chapter1.XiQuotient K) ∧
      d.X ≤ componentOrbit K (T : Subgroup G) ∧ Nonempty (P₀ ≃* Plane 3) ∧
      ((SwappedFactors (T : Subgroup G) P₀ K ∧ SwappedModel 3 (Chapter1.XiQuotient K)) ∨
        ((T : Subgroup G) ≤ normalizer (K : Set G) ∧
          (LinearThreeModel 3 (Chapter1.XiQuotient K) ∨
            ExceptionalModel (Chapter1.XiQuotient K) ∨
            Nonempty (Chapter1.XiQuotient K ≃* Held.He)))) := by
  dsimp only
  have hnc := quiet_tensor_point_automizer_not_cyclic D hn e hbase hzV hz1 hzT P
  rcases quiet_tensor_point_embedding_alternatives D hn e hbase hzV hz1 hzT P with
    hnX | ⟨K,hK,hq,hX,hrows⟩
  · exact Or.inl hnX
  · refine Or.inr ⟨K,hK,hq,hX,?_⟩
    rcases hrows with ⟨hP,hswap | ⟨hTK,hlin | hsym | hexc⟩⟩ | ⟨_,hP,hTK,hHeld⟩
    · exact ⟨hP,Or.inl hswap⟩
    · exact ⟨hP,Or.inr ⟨hTK,Or.inl hlin⟩⟩
    · exact (hnc hsym.2).elim
    · exact ⟨hP,Or.inr ⟨hTK,Or.inr (Or.inl hexc.2)⟩⟩
    · exact ⟨hP,Or.inr ⟨hTK,Or.inr (Or.inr hHeld)⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
