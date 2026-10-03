module
public import Theory.GroupTheory.TransferIndexTwoVanishing
public import Theory.GroupTheory.TransferTower
public import Theory.GroupTheory.TransferAutomorphismInvariant
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Sylow transfer from an automorphism-invariant involution

A Sylow-two involution outside the Sylow derived subgroup remains outside
the ambient derived subgroup when its commutators and square lie in every
maximal subgroup's derived group, and its abelianization image is invariant
under automorphisms. Proper stabilizers have even index and contribute
trivial transfer terms. The remaining terms give the involution image raised
to the odd Sylow index.

Source: Andersen--Oliver--Ventura, *Fusion systems and amalgams*, Proposition
2.3(b), using the ordinary Mackey transfer formula.
-/

open scoped commutatorElement

namespace Sylow

public theorem not_mem_commutator_of_invariant_maximal_transfer_vanishing
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (u : S) (U : Subgroup S)
    (hu : u ∉ commutator S)
    (hu2 : u ^ 2 = 1)
    (hinvariant : ∀ f : MulAut S, Abelianization.of (f u) = Abelianization.of u)
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
  have heven (K : Subgroup S) (hK : K ≠ ⊤) : 2 ∣ K.index := by
    obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
    have hindex : M.index = 2 := S.isPGroup'.index_of_isCoatom M hM
    simpa only [hindex] using Subgroup.index_dvd_of_le hKM
  have hφ2 : (φ u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have htransfer : MonoidHom.transfer φ (u : G) = φ u := by
    rw [MonoidHom.transfer_eq_pow_of_automorphism_invariant
      (S : Subgroup G) φ u hφ2 hinvariant heven hproper]
    have hodd : (S : Subgroup G).index % 2 = 1 := by
      have hn := S.not_dvd_index
      omega
    have hind : (S : Subgroup G).index =
        2 * ((S : Subgroup G).index / 2) + 1 := by omega
    rw [hind, pow_add, pow_mul, hφ2, one_pow, pow_one, one_mul]
  intro huG
  have hzero : MonoidHom.transfer φ (u : G) = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer φ) huG
  have huZero : Abelianization.of u = 1 := htransfer.symm.trans hzero
  apply hu
  change u ∈ Abelianization.of.ker at huZero
  rwa [Abelianization.ker_of] at huZero

end Sylow
