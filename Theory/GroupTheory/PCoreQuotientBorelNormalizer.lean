module

public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Local Sylow normalizers with coprime outer action

Let an ambient Sylow p-subgroup T normalize K. If K/O_p(K) is centerless
and its outer automorphism group has order prime to p, the quotient action
of T is inner. The inner-supplement theorem gives
T = (T ∩ K) O_p(KT). Consequently N_K(T ∩ K) normalizes the actual T,
including its part outside K. Its image under a surjection from K is the
normalizer of the corresponding Sylow image.

Source application: Aschbacher--Smith 14.3.15, printed p.994. In that
application the image normalizer is the L₂(8) Borel; T need not lie in K.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Coprime outer action places the local Sylow normalizer in the full
ambient Sylow normalizer, without assuming T ≤ K. -/
theorem sylow_normalizer_le_of_coprime_outer
    (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore p K) = ⊥)
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (K ⧸ pCore p K))))
    (P : Sylow p K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (T : Set G) := by
  let a : T →* MulAut (K ⧸ pCore p K) :=
    (pCoreJoinAction p hn).comp (inclusion le_sup_right)
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore p K))).comp a
  have hi (t : T) : a t ∈ MulAut.innerSubgroup (K ⧸ pCore p K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f t = 1
    obtain ⟨n, hn⟩ := T.isPGroup' t
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (ho.pow_left n)
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hn, map_one]
    · exact _root_.orderOf_dvd_natCard (f t)
  have hPT : (P : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rintro _ ⟨k, hk, rfl⟩
    change k ∈ (T : Subgroup G).subgroupOf K
    rwa [← hP]
  have hfactor := sup_core_factor_of_inner_action K (T : Subgroup G) hn T.isPGroup'
    hz P hPT hi
  let W := K ⊔ (T : Subgroup G)
  have hcore : W ≤ normalizer (W.pCoreIn p : Set G) :=
    W.le_normalizer.trans (normalizer_le_normalizer_characteristic_image W (pCore p W))
  have h1 : (normalizer (P : Set K)).map K.subtype ≤
      normalizer ((P : Subgroup K).map K.subtype : Set G) :=
    (P : Subgroup K).le_normalizer_map K.subtype
  have h2 : (normalizer (P : Set K)).map K.subtype ≤
      normalizer (W.pCoreIn p : Set G) :=
    (map_subtype_le _).trans (le_sup_left.trans hcore)
  change _ ≤ normalizer ((T : Subgroup G) : Set G)
  rw [hfactor]
  exact (le_inf h1 h2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The quotient Borel has exactly the original local Sylow normalizer as
its inverse image when the kernel lies in that Sylow subgroup. -/
theorem comap_sylow_normalizer_of_ker_le
    {D : Type*} [Group D] (P : Sylow p G) (q : G →* D)
    (hq : Function.Surjective q) (hk : q.ker ≤ (P : Subgroup G)) :
    (normalizer (P.map q : Set D)).comap q = normalizer (P : Set G) := by
  rw [← P.normalizer_map_surjective q hq, comap_map_eq]
  exact sup_eq_left.mpr (hk.trans P.le_normalizer)

end Subgroup
