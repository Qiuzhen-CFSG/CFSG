module
public import Stellmacher.SectionTen.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.PSetResidualKernel

/-!
# A first-module actor survives every noncentral residual action

In the actual Section Ten geometry, a first-module actor outside the
terminal two-core acts nontrivially in any homomorphic image where the
terminal two-residual acts nontrivially. The supplied actor and homomorphism
are retained; irreducibility of the target action is unnecessary.

The first module is elementary abelian, so the actor generates a two-group.
If its image were trivial, that two-group would lie in a normal kernel
which does not contain the terminal residual. The local PSet normal-kernel
theorem then puts it inside the terminal two-core, a contradiction.

This supplies the nontrivial actor in the chief quotient used just before
(15) in Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.63.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_first_actor_image_ne_one
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {X : Type u} [Group X]
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (action : GAt ctx.Γ ctx.criticalPath.a' →* X)
    (hres : ¬ (EAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a') ≤ action.ker) :
    action actor ≠ 1 := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let K := action.ker.map P.subtype
  let C := Subgroup.zpowers (actor : G)
  have hKP : K ≤ P := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf P = action.ker := subgroupOf_map_subtype_eq _
  have hKN : (K.subgroupOf P).Normal := by rw [hKsub]; infer_instance
  have hE : EAt ctx.Γ ctx.criticalPath.a' = twoResidualAmbient P :=
    ctx.Γ.twoResidualAt_def ctx.criticalPath.a'
  have hRnot : ¬ twoResidualAmbient P ≤ K := by
    intro hle
    apply hres
    intro x hx
    have hxK : x ∈ K.subgroupOf P := hle (hE ▸ hx)
    rwa [hKsub] at hxK
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
  have hCtwo : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2
    (VAt ctx.Γ ctx.criticalPath.firstStep)).to_le (Subgroup.zpowers_le.mpr hactor)
  have hterminal : ctx.Γ.adjacent middle ctx.criticalPath.a' := by
    obtain ⟨index, hindex, rfl⟩ := hpath
    have hlen := ctx.critical_length
    have hadj := ctx.criticalPath.path_adj ⟨2, by omega⟩
    have hleft : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).castSucc = index :=
      Fin.ext hindex.symm
    have hright : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rwa [hleft, hright, ctx.criticalPath.path_end] at hadj
  let edge := P ⊓ GAt ctx.Γ middle
  let sylow : Sylow 2 edge := default
  let Sedge := sylowTwoAmbient edge sylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) sylow
  intro htrivial
  have hCK : C ≤ K := Subgroup.zpowers_le.mpr ⟨actor, htrivial, rfl⟩
  have hcore := SectionThree.pSet_two_subgroup_normal_kernel_le_core
    Sedge hlocal.1 P K C hlocal.2.1 hlocal.2.2.2.1 hKP hKN hRnot hCK hCtwo
  apply hout
  change (actor : G) ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a'
  rw [ctx.Γ.twoCoreAt_def]
  exact hcore (Subgroup.mem_zpowers (actor : G))

end Stellmacher.SectionTen
