import Stellmacher.SectionOne.LemmaOneOne
open scoped BigOperators Pointwise
namespace Stellmacher.SectionOne
universe u v

example {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    oddCore G =
      ⁅oddCore G, (S : Subgroup G)⁆ ⊔
        (oddCore G ⊓ Subgroup.centralizer (S : Set G)) := by
  let W : Subgroup G := oddCore G
  let A : Subgroup G := (S : Subgroup G)
  letI : Group.IsSolvable G := h.G_solvable
  letI : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  have hAnormW : A ≤ Subgroup.normalizer (W : Set G) := by
    exact Subgroup.le_normalizer_of_normal
  letI : MulDistribMulAction ↥A ↥W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAnormW
  have hWsolv : Group.IsSolvable (↥W) := by infer_instance
  have hWcop : Nat.Coprime 2 (Nat.card W) := by
    dsimp [W]
    exact pPrimeCore_coprime_card (p := 2) (G := G)
  have hAcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact hWcop.pow_left n
  have hsup :
      fixedPointSubgroup (↥A) (↥W) ⊔
          commutatorAction (A := ↥A) (G := ↥W) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := ↥W) (A := ↥A) hWsolv hAcop
  have hmap := congrArg (fun K : Subgroup W => K.map W.subtype) hsup
  have hfix : fixedPointSubgroup (↥A) (↥W) =
      (subgroupCentralizerIn W A).subgroupOf W :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn W A hAnormW
  have hfixmap :
      (fixedPointSubgroup (↥A) (↥W)).map W.subtype = subgroupCentralizerIn W A := by
    rw [hfix, Subgroup.map_subgroupOf_eq_of_le]
    exact inf_le_left
  have hcommmap :
      (commutatorAction (A := ↥A) (G := ↥W)).map W.subtype = ⁅W, A⁆ := by
    exact commutatorAction_subgroup_conj_map_eq_commutator W A hAnormW
  have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  rw [Subgroup.map_sup, hfixmap, hcommmap, htopmap] at hmap
  simpa [W, A, subgroupCentralizerIn, Subgroup.commutator_comm, sup_comm] using hmap.symm

end Stellmacher.SectionOne
