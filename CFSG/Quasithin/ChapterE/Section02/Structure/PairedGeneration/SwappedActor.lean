module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalSimpleTau

/-!
# Swapped-actor norm diagonals are E-members

An elementary actor exchanging two simple components centralizes its swapping
involution. Since the component normalizer has index two, its tau normalizes
the actual norm diagonal. The prescribed Sylow intersection is inherited from
the component. Noncentral action of the component stabilizer survives on the
diagonal, and the genuine automorphism two-rank gives the required rank bound
in the radical quotient. The resulting nonsolvable member is the one used to
escape the solvable maximal subgroup in the paired minimal-parabolic argument.

Source: Aschbacher–Smith, E.1.11, printed pp.213–214; E.2.2 paired case.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
lemma tau_normalizes_norm (T A : Subgroup G) {K : Subgroup G}
    (hK : IsComponent G K) (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {a : G} (ha : a ∈ A) (ha2 : a ^ 2 = 1)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) :
    tau T A ≤ normalizer (NormPair.normRange hK hm : Set G) := by
  intro b hb
  have hc := (mem_centralizerModulo_iff.mp hb).2 a ha
  rw [hcore, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact NormPair.normalizes_norm_of_pair hK hm ha2 (show Commute b a from hc.symm)
    (NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hm b)

omit [Finite G] in
lemma actor_not_centralizes_norm {K A : Subgroup G}
    (hK : IsComponent G K) [IsElementaryAbelian 2 A]
    {a : G} (ha : a ∈ A) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    ¬ A ≤ centralizer (NormPair.normRange hK hm : Set G) := by
  intro h
  apply hne
  intro b hb
  have hc : Commute b a := by
    let : CommGroup A := IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨b,hb.1⟩ : A) ⟨a,ha⟩)
  exact NormPair.centralizes_norm_normalizes_component hK hm hc hb.2 (h hb.1)

/-- The actual swapped-actor norm diagonal, with its prescribed tau,
is an E-member at the genuine component automorphism two-rank bound. -/
theorem norm_tau_member (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    {a : G} (ha : a ∈ A) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    IsEMemberAt f (T : Subgroup G) A
      (NormPair.normRange hK hm ⊔ tau (T : Subgroup G) A) := by
  let I := NormPair.normRange hK hm
  let e : K ≃* I := NormPair.normEquivOfSimple hK hm
  let : IsSimpleGroup I := e.symm.isSimpleGroup
  let : IsQuasisimple I := componentSwapNorm_range_quasisimple hK hm
  have hrI : primeRank 2 (MulAut I) ≤ f := by
    rw [← primeRank_equiv 2 (MulAut.congr e)]
    exact hr
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
  exact ChiefOrbit.NormalSimpleTau.isEMemberAt_of_normalized_simple T I
    (tau (T : Subgroup G) A) (tau_le _ _)
    (tau_normalizes_norm _ _ hK hcore hindex ha ha2 hm) hrI A inferInstance hAT
    ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right)
    le_sup_right (NormPair.exists_sylow_intersection T hK hm (hAT ha))
    (actor_not_centralizes_norm hK ha hm hne)

omit [Finite G] in
/-- The literal norm-tau member is nonsolvable, so it escapes every
solvable proposed overgroup. -/
theorem norm_tau_not_solvable (T : Subgroup G) {K A : Subgroup G}
    (hK : IsComponent G K) {a : G}
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) :
    ¬ Group.IsSolvable (NormPair.normRange hK hm ⊔ tau T A : Subgroup G) := by
  let I := NormPair.normRange hK hm
  let : IsQuasisimple I := componentSwapNorm_range_quasisimple hK hm
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : Nontrivial I := (QuotientGroup.mk'_surjective (center I)).nontrivial
  intro hs
  let := hs
  have hsolv : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show I ≤ I ⊔ tau T A from le_sup_left)) (inclusion_injective _)
  exact Group.IsPerfect.not_isSolvable I hsolv

/-- Existence form used by the paired minimal-parabolic generation argument. -/
theorem exists_nonsolvable_member (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hmove : ¬ A ≤ normalizer (K : Set G))
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    ∃ X : Subgroup G, IsEMemberAt f (T : Subgroup G) A X ∧ ¬ Group.IsSolvable X := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hmove
  have hm : K.map (MulAut.conj a).toMonoidHom ≠ K :=
    fun h => han (mem_normalizer_iff_map_conj_eq.mpr h)
  exact ⟨_, norm_tau_member T hK hcore hindex hr hAT ha hm hne,
    norm_tau_not_solvable _ hK hm⟩

end CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
