module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalSimpleTau
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedGeneration.Normalizer

/-!
# Normalized elementary actors in an actual component pair

If tau also normalizes the component, its simple local gives the E-member.
Otherwise the full tau orbit gives both factors, and faithfulness on one
factor bounds the original actor rank: an actor in the conjugation kernel
centralizes the entire tau orbit and hence lies in the ambient two-core.

Source: Aschbacher–Smith E.1.11 and E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem tau_centralizes (hcore : pCore 2 G = ⊥) (T A : Subgroup G) :
    tau T A ≤ centralizer (A : Set G) := by
  intro t ht a ha
  have h := (mem_centralizerModulo_iff.mp ht).2 a ha
  rw [hcore, mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem normalized_actor_rank_of_tau_orbit (T : Sylow 2 G)
    {K A : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hcore : pCore 2 G = ⊥)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hAN : A ≤ normalizer (K : Set G))
    (ho : componentOrbit K (tau (T : Subgroup G) A) = componentOrbit K (T : Subgroup G)) :
    Group.rank A ≤ primeRank 2 (MulAut K) := by
  let V := A ⊓ centralizer (K : Set G)
  have htv : tau (T : Subgroup G) A ≤ centralizer (V : Set G) :=
    (tau_centralizes hcore _ _).trans (centralizer_le inf_le_left)
  have he : componentOrbit K (tau (T : Subgroup G) A) ≤ centralizer (V : Set G) :=
    iSup_conjugates_le_of_le_normalizer K _ _ (le_centralizer_iff.mp inf_le_right)
      (htv.trans (centralizer (V : Set G)).le_normalizer)
  have hv : V = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore, ← hK.sylow_centralizer_orbit_eq_pCore T hgen, ← ho]
    exact le_inf (inf_le_left.trans hAT) (le_centralizer_iff.mp he)
  let f := K.normalizerMonoidHom.comp (inclusion hAN)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    have hc : (a:G) ∈ centralizer (K : Set G) := by
      change inclusion hAN a ∈ K.normalizerMonoidHom.ker at ha
      rw [normalizerMonoidHom_ker] at ha
      exact ha
    have hh : (a:G) ∈ V := ⟨a.property,hc⟩
    change (a:G) = 1
    simpa only [hv, mem_bot] using hh
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  calc
    Group.rank A = Group.rank f.range := Group.rank_congr e
    _ ≤ primeRank 2 (MulAut K) := f.range.rank_le_primeRank 2
      (IsElementaryAbelian.isPGroup 2 _)

theorem normalized_actor_member (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hrad : solvableRadical G = ⊥) (hlayer : pResidual 2 G = componentLayer G)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hAN : A ≤ normalizer (K : Set G)) (hne : ¬ A ≤ centralizer (K : Set G)) :
    IsEMemberAt f (T : Subgroup G) A (K ⊔ tau (T : Subgroup G) A) := by
  by_cases ht : tau (T : Subgroup G) A ≤ normalizer (K : Set G)
  · exact ChiefOrbit.NormalSimpleTau.component_tau_join_member T hK hr hAT ht hne
  · let : IsQuasisimple K := hK.2
    have ho := moved_pair_orbit_eq_residual T hK hgen hlayer hindex ht
    have hT : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) :=
      fun h => ht ((tau_le _ _).trans h)
    have hoT := moved_pair_orbit_eq_residual T hK hgen hlayer hindex hT
    have hcomm : K = ⁅K,A⁆ := by
      rcases simple_subnormal_commutator_dichotomy K A hK.1 with hb | he
      · exact (hne (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))).elim
      · rw [he]
        apply le_antisymm (le_componentOrbit K A)
        apply iSup_le
        intro a
        exact (mem_normalizer_iff_map_conj_eq.mp (hAN a.property)).le
    exact ChiefOrbit.tau_join_member_of_full_orbit T hK hrad hlayer hAT ho (.inl hcomm)
      ((normalized_actor_rank_of_tau_orbit T hK hgen (SimpleSocle.pCore_eq_bot hrad 2)
        hAT hAN (ho.trans hoT.symm)).trans hr)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
