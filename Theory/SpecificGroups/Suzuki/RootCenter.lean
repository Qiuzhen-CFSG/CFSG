module

public import Theory.SpecificGroups.Suzuki.AbelianSubgroups

/-!
# Centers and complements in Suzuki Sylow normalizers

The center consists of the root matrices with first coordinate zero.
The second coordinate gives a bijection with the field, so its order is q.
This is the coordinate clause of Huppert--Blackburn, Finite Groups III,
XI.3.1, transported from the matrix closure to the Suzuki subgroup.
Sylow conjugacy then transports this order, the root-element centralizer
bound, and the cyclic split-torus complement to any specified Sylow subgroup
of a group actually isomorphic to this Suzuki group. The centralizer and
normalizer inputs are the proved ovoid geometry of XI.3.3 and XI.3.10.
-/

open BenderSuzuki PFAppendixIII Subgroup
open scoped Pointwise LinearAlgebra.Projectivization
namespace BenderSuzuki.MatrixGroups

/-- The center of the standard Suzuki root group has order q. -/
public theorem suzukiRootSubgroup_center_card (m : ℕ) (hm : 0 < m) :
    Nat.card (center (SuzukiRootSubgroup m)) = 2 ^ (2 * m + 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def K 2 (m + 1)
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, hz, _⟩ :=
    External.huppert_blackburn_XI_3_1 m hm pi
      (External.binaryGaloisField_tits_formula_sq m pi hpi)
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  change ∀ x : SuzukiRootClosure m, x ∈ commutator (SuzukiRootClosure m) ↔
    ∃ b : K, (x : GL (Fin 4) K) = SuzukiRootGL m 0 b at hz
  rw [hc] at hz
  let f : K → center (SuzukiRootClosure m) := fun b =>
    ⟨⟨SuzukiRootGL m 0 b, subset_closure ⟨0, b, rfl⟩⟩,
      (hz _).mpr ⟨b, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b c he
      have h02 := congrArg (fun z : center (SuzukiRootClosure m) =>
        ((z.val.val : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) he
      simpa [f, SuzukiRootGL, SuzukiRootMatrix] using h02
    · intro z
      obtain ⟨b, hb⟩ := (hz z.val).mp z.property
      exact ⟨b, Subtype.ext (Subtype.ext hb.symm)⟩
  calc
    Nat.card (center (SuzukiRootSubgroup m)) = Nat.card (center (SuzukiRootClosure m)) :=
      Nat.card_congr (centerCongr (subgroupOfEquivOfLe (suzukiRootClosure_le m))).toEquiv
    _ = Nat.card K := (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = _ := GaloisField.card 2 (2 * m + 1) (by omega)

private theorem suzuki_aligned_equiv {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (S : Sylow 2 H) :
    ∃ f : SuzukiMatrixGroup m ≃* H,
      (SuzukiRootSubgroup m).map f.toMonoidHom = (S : Subgroup H) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  let P' : Sylow 2 H := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' S
  refine ⟨e.symm.trans (MulAut.conj g), ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup (SuzukiMatrixGroup m)).map e.symm.toMonoidHom).map
    (MulAut.conj g).toMonoidHom = (S : Subgroup H) at hh
  change (SuzukiRootSubgroup m).map
    ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
  simpa only [hP, map_map] using hh

/-- A prescribed Suzuki Sylow subgroup has center of order q, contains the
centralizer of each of its nonidentity elements, and has a cyclic split-torus
complement of order q - 1 in its normalizer. The equivalence is with the
actual matrix group. -/
public theorem suzukiSylow_borel_structure {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (S : Sylow 2 H) :
    Nat.card (center S) = 2 ^ (2 * m + 1) ∧
    (∀ x ∈ (S : Subgroup H), x ≠ 1 → centralizer ({x} : Set H) ≤ S) ∧
    ∃ D : Subgroup H,
      Nonempty (D ≃* Multiplicative (ZMod (2 ^ (2 * m + 1) - 1))) ∧
      (S : Subgroup H) ⊔ D = normalizer (S : Set H) ∧
      (S : Subgroup H) ⊓ D = ⊥ := by
  obtain ⟨f, hf⟩ := suzuki_aligned_equiv hm e S
  let eR : SuzukiRootSubgroup m ≃* S :=
    ((SuzukiRootSubgroup m).equivMapOfInjective f.toMonoidHom f.injective).trans
      (MulEquiv.subgroupCongr hf)
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.card_congr (centerCongr eR).toEquiv).symm.trans
      (suzukiRootSubgroup_center_card m hm)
  · intro x hx hne y hy
    obtain ⟨x₀, hx₀, rfl⟩ := show x ∈ (SuzukiRootSubgroup m).map f.toMonoidHom from hf.symm ▸ hx
    have hne₀ : x₀ ≠ 1 := fun hh => hne (hh ▸ f.map_one)
    have hc : Commute (f.symm y) x₀ := by
      simpa only [MulEquiv.symm_apply_apply] using
        (show Commute y (f x₀) from mem_centralizer_singleton_iff.mp hy).map f.symm
    have hy₀ := suzukiRootSubgroup_centralizer_le m hm hx₀ hne₀
      (mem_centralizer_singleton_iff.mpr hc.eq)
    rw [← hf]
    exact ⟨f.symm y, hy₀, f.apply_symm_apply y⟩
  · let D := (SuzukiSplitTorus m).map f.toMonoidHom
    let eD := (SuzukiSplitTorus m).equivMapOfInjective f.toMonoidHom f.injective
    let _ : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
    let _ : IsCyclic D := eD.isCyclic.mp inferInstance
    have hcard : Nat.card D = 2 ^ (2 * m + 1) - 1 :=
      (Nat.card_congr eD.toEquiv).symm.trans (suzukiSplitTorus_card m hm)
    refine ⟨D, ⟨mulEquivOfCyclicCardEq ?_⟩, ?_, ?_⟩
    · change Nat.card D = Nat.card (ZMod (2 ^ (2 * m + 1) - 1))
      rwa [Nat.card_zmod]
    · rw [← hf, ← Subgroup.map_sup, ← suzukiBorelSubgroup_eq_sup,
        ← suzukiRootSubgroup_normalizer m hm, map_equiv_normalizer_eq, hf]
      rfl
    · exact (disjoint_iff.mp (hf ▸ disjoint_map f.injective
        (suzukiRootSubgroup_disjoint_splitTorus m hm)))

end BenderSuzuki.MatrixGroups
