module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The two-core of a Sylow supplement to an action kernel

Suppose `G` acts through a homomorphism `f`, and `[ker(f), Y] ≤ O₂(G)`.
For a Sylow two-subgroup `T`, this makes `T ∩ ker(f)` normal in `YT`:
conjugation by `Y` changes an element only by a member of `O₂(G) ≤ T`.
If the image of `YT` is the whole target and that target has trivial
two-core, every normal two-subgroup of `YT` lies in this intersection.
Thus `O₂(YT) = T ∩ ker(f)`.

The image lemma transports this identity from a local subgroup to its
ambient group. No normality of `Y` is required for the core calculation.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.7, printed p.1122; the commutator bound comes from 14.1.17(3).
-/

namespace Subgroup
open scoped commutatorElement

variable {G A : Type*} [Group G] [Group A]

/-- A surjective action of `YT` with trivial target two-core identifies its
intrinsic two-core with the Sylow intersection of the action kernel. -/
public theorem twoCore_join_eq_sylow_inf_ker (f : G →* A) (Y : Subgroup G) (T : Sylow 2 G)
    (hcomm : ⁅f.ker, Y⁆ ≤ pCore 2 G)
    (honto : Function.Surjective (f.domRestrict (Y ⊔ (T : Subgroup G))))
    (hcore : pCore 2 A = ⊥) :
    (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ f.ker := by
  let X := Y ⊔ (T : Subgroup G)
  let D := (T : Subgroup G) ⊓ f.ker
  have hQT : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hDn : X ≤ normalizer (D : Set G) := by
    apply sup_le
    · apply le_normalizer_iff.mpr
      intro y hy d hd
      have hc : ⁅y, d⁆ ∈ pCore 2 G := by
        rw [commutator_comm] at hcomm
        exact hcomm (commutator_mem_commutator hy hd.2)
      refine ⟨?_, (inferInstance : f.ker.Normal).conj_mem d hd.2 y⟩
      change y * d * y⁻¹ ∈ (T : Subgroup G)
      have h := (T : Subgroup G).mul_mem (hQT hc) hd.1
      simpa only [commutatorElement_def, inv_mul_cancel_right] using h
    · exact (le_inf (T : Subgroup G).le_normalizer le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
  have hDX : D ≤ X := inf_le_left.trans le_sup_right
  apply le_antisymm
  · have hRT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hTX : (T : Subgroup G) ≤ X := le_sup_right
      have h := pCoreIn_le_sylow X (T.subtype hTX)
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] using h
    have himage : ((pCore 2 X).map (f.domRestrict X)).Normal :=
      (inferInstance : (pCore 2 X).Normal).map _ honto
    have hsmall : (pCore 2 X).map (f.domRestrict X) ≤ pCore 2 A :=
      le_sSup ⟨himage, pCore_isPGroup.map _⟩
    have hker : X.pCoreIn 2 ≤ f.ker := by
      apply (Subgroup.map_eq_bot_iff _).mp
      apply le_bot_iff.mp
      rw [pCoreIn, map_map]
      exact hcore ▸ hsmall
    exact le_inf hRT hker
  · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left) hDX hDn

/-- Faithful embeddings preserve ambient prime cores. -/
public theorem map_pCoreIn_of_injective (p : ℕ) (H : Subgroup G) (f : G →* A) (hf : Function.Injective f) :
    (H.pCoreIn p).map f = (H.map f).pCoreIn p := by
  let e := Subgroup.equivMapOfInjective H f hf
  have h := pCore_map_iso p e
  rw [pCoreIn, pCoreIn, map_map]
  calc
    (pCore p H).map (f.comp H.subtype) =
        ((pCore p H).map e.toMonoidHom).map (H.map f).subtype := by
      rw [map_map]
      rfl
    _ = (pCore p (H.map f)).map (H.map f).subtype := by rw [h]

end Subgroup
