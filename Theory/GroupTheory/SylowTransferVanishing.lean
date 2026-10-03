module
public import Theory.GroupTheory.TransferIndexTwoVanishing
public import Theory.GroupTheory.TransferTower
public import Theory.GroupTheory.TransferSelfNormalizer
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# A maximal-subgroup transfer obstruction in a Sylow subgroup

For a self-normalizing Sylow two-subgroup `S`, an element outside its derived
subgroup also lies outside the ambient derived subgroup if its square and
all its Sylow commutators lie in a subgroup contained in every maximal
subgroup's derived subgroup.

Every maximal subgroup of the finite two-group has index two. The square
and commutator hypotheses kill transfer to any commutative image of such a
subgroup; transfer composition extends this vanishing to every proper
subgroup. The self-normalizer Mackey formula then identifies ambient
transfer to `Abelianization S` on the supplied element with its nontrivial
abelianization image. Since a map to an abelian group kills the ambient
derived subgroup, the element cannot belong to that subgroup.

This is the ordinary group and self-normalizing-Sylow specialization of
Andersen–Oliver–Ventura, `Fusion systems and amalgams`, Proposition 2.3(b),
author manuscript p.6. It uses the actual Mathlib transfer and no fusion
system, simplicity, or named Sylow-model assumption.
-/

open scoped commutatorElement

namespace Sylow

public theorem not_mem_commutator_of_maximal_transfer_vanishing
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hN : Subgroup.normalizer (S : Set G) = (S : Subgroup G))
    (u : S) (U : Subgroup S)
    (hu : u ∉ commutator S)
    (hsquare : u ^ 2 ∈ U)
    (hcomm : ∀ v : S, ⁅u, v⁆ ∈ U)
    (hmax : ∀ M : Subgroup S, M.index = 2 → U ≤ ⁅M, M⁆) :
    (u : G) ∉ commutator G := by
  classical
  have hproper (K : Subgroup S) (hK : K ≠ ⊤)
      (ψ : K →* Abelianization S) : MonoidHom.transfer ψ u = 1 := by
    obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
    have hindex : M.index = 2 := S.isPGroup'.index_of_isCoatom M hM
    let ψM : M →* Abelianization S :=
      MonoidHom.transfer (H := K.subgroupOf M)
        (ψ.comp (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom)
    have hzero : MonoidHom.transfer ψM u = 1 :=
      MonoidHom.transfer_eq_one_of_index_two M hindex u
        (hmax M hindex hsquare) (fun v => hmax M hindex (hcomm v)) ψM
    have htower := congrArg (fun f : S →* Abelianization S => f u)
      (MonoidHom.transfer_transfer K M hKM ψ)
    exact htower.symm.trans hzero
  let φ : S →* Abelianization S := Abelianization.of
  have htransfer : MonoidHom.transfer φ (u : G) = φ u :=
    MonoidHom.transfer_eq_self_of_self_normalizing (S : Subgroup G) hN φ u hproper
  intro huG
  have hzero : MonoidHom.transfer φ (u : G) = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer φ) huG
  have huZero : Abelianization.of u = 1 := htransfer.symm.trans hzero
  apply hu
  change u ∈ Abelianization.of.ker at huZero
  rwa [Abelianization.ker_of] at huZero

end Sylow
