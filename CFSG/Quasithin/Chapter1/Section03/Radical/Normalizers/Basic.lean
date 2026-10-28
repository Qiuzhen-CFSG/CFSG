module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Quotient
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator
public import Theory.GroupTheory.SolvableResidual

/-!
# The normalizers in the radical uniqueness argument

We use the actual two-core R = O₂(Ξ_p(L)T) and the terminal derived
subgroups N_L(D)^∞. The latter are solvable residuals, not two-residuals.
The Sylow hypothesis and relative normality of L put O₂(L) inside R.
Mutual normalization puts [Ξ_p(L),R] inside O₂(Ξ_p(L)).

These are the elementary construction steps in Aschbacher–Smith,
combined manuscript of 1 March 2004, proof of Proposition 1.3.8,
printed pp.512–513. The nonsolvable structure of N_L(R)^∞ and the
multiple-prime embedding argument are separate obligations.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G : Type*} [Group G]

/-- The source's R = O₂(XT), with X = Ξ_p(L). -/
def radicalCore (p : ℕ) (L T : Subgroup G) : Subgroup G :=
  (XiP p L ⊔ T).pCoreIn 2

/-- N_L(D)^∞, embedded in G. In particular, Y is obtained by taking D = R. -/
def normalizerResidual (L D : Subgroup G) : Subgroup G :=
  (solvableResidual (L ⊓ normalizer (D : Set G) : Subgroup G)).map
    (L ⊓ normalizer (D : Set G)).subtype

theorem radicalCore_isTwoGroup (p : ℕ) (L T : Subgroup G) :
    IsPGroup 2 (radicalCore p L T) := isPGroup_pCoreIn 2 _

theorem radicalCore_le_join (p : ℕ) (L T : Subgroup G) :
    radicalCore p L T ≤ XiP p L ⊔ T := pCoreIn_le 2 _

theorem radicalCore_ne_bot (p : ℕ) {L T : Subgroup G} (hL : L ∈ Chapter1.L G T) :
    radicalCore p L T ≠ ⊥ := XiP_join_mem_H p hL

theorem join_le_normalizer_radicalCore (p : ℕ) (L T : Subgroup G) :
    XiP p L ⊔ T ≤ normalizer (radicalCore p L T : Set G) :=
  (XiP p L ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem t_le_normalizer_radicalCore (p : ℕ) (L T : Subgroup G) :
    T ≤ normalizer (radicalCore p L T : Set G) :=
  le_sup_right.trans (join_le_normalizer_radicalCore p L T)

/-- This uses Sylow membership inside LT, and only relative normality of L. -/
theorem twoCore_le_radicalCore (p : ℕ) {L T : Subgroup G}
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    L.pCoreIn 2 ≤ radicalCore p L T := by
  have hLT : L ⊔ T ≤ normalizer (L : Set G) := sup_le L.le_normalizer hT
  have hcore : L.pCoreIn 2 ≤ (L ⊔ T).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left hLT
  obtain ⟨S, hS⟩ := hSyl
  have hcoreT : L.pCoreIn 2 ≤ T := by
    rw [← hS]
    exact hcore.trans (pCoreIn_le_sylow _ S)
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
    (hcoreT.trans le_sup_right)
    ((sup_le_sup_right (XiP_le p L) T).trans
      (hLT.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))

/-- R fixes X/O₂(X): the commutator is an actual normal two-subgroup of X. -/
theorem commutator_radicalCore_le (p : ℕ) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) :
    ⁅XiP p L, radicalCore p L T⁆ ≤ (XiP p L).pCoreIn 2 := by
  exact commutator_le_pCore_of_mutual_normalization _ _
    (radicalCore_isTwoGroup p L T)
    (le_sup_left.trans (join_le_normalizer_radicalCore p L T))
    ((radicalCore_le_join p L T).trans
      (sup_le (XiP p L).le_normalizer (XiP_invariant p hT)))

theorem normalizerResidual_le (L D : Subgroup G) : normalizerResidual L D ≤ L :=
  (map_subtype_le _).trans inf_le_left

theorem normalizerResidual_le_normalizer (L D : Subgroup G) :
    normalizerResidual L D ≤ normalizer (D : Set G) :=
  (map_subtype_le _).trans inf_le_right

theorem normalizerResidual_perfect [Finite G] (L D : Subgroup G) :
    Group.IsPerfect (normalizerResidual L D) := by
  exact Group.IsPerfect.ofSurjective
    (f := ((solvableResidual (L ⊓ normalizer (D : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (D : Set G)).subtype
      (L ⊓ normalizer (D : Set G)).subtype_injective).toMonoidHom)
    ((solvableResidual (L ⊓ normalizer (D : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (D : Set G)).subtype
      (L ⊓ normalizer (D : Set G)).subtype_injective).surjective

/-- Any subgroup normalizing both L and D normalizes N_L(D)^∞. -/
theorem le_normalizer_normalizerResidual {L D A : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G)) (hAD : A ≤ normalizer (D : Set G)) :
    A ≤ normalizer (normalizerResidual L D : Set G) := by
  have hAN : A ≤ normalizer (normalizer (D : Set G) : Set G) :=
    hAD.trans (normalizer (D : Set G)).le_normalizer
  exact ((le_inf hAL hAN).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- In particular T acts on the constructed Y. -/
theorem t_le_normalizer_Y (p : ℕ) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) :
    T ≤ normalizer (normalizerResidual L (radicalCore p L T) : Set G) :=
  le_normalizer_normalizerResidual hT (t_le_normalizer_radicalCore p L T)

/-- The local group N_LT(R) has nontrivial two-core, since it contains R
as a normal two-subgroup. -/
theorem localNormalizer_mem_H (p : ℕ) {L T : Subgroup G}
    (hL : L ∈ Chapter1.L G T) :
    (L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G) ∈ H G := by
  have hle : radicalCore p L T ≤
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (radicalCore_isTwoGroup p L T)
      (le_inf ((radicalCore_le_join p L T).trans (sup_le_sup_right (XiP_le p L) T))
        (radicalCore p L T).le_normalizer) inf_le_right
  exact fun he => radicalCore_ne_bot p hL (bot_unique (he ▸ hle))

/-- The construction gives relative normality of Y in N_LT(R). -/
theorem Y_normal_in_localNormalizer (p : ℕ) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) :
    ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer
    (le_normalizer_normalizerResidual
      (inf_le_left.trans (sup_le L.le_normalizer hT)) inf_le_right)

/-- Once the structural argument identifies Y as a C-component of N_LT(R),
the genuine 1.2.6 local-family conclusion follows. -/
theorem Y_mem_L_of_cComponent (p : ℕ) {L T : Subgroup G}
    (hL : L ∈ Chapter1.L G T)
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent) :
    normalizerResidual L (radicalCore p L T) ∈ Chapter1.L G T := by
  apply mem_L_of_cComponent (localNormalizer_mem_H p hL)
    (hL.2.1.restrict (le_inf le_sup_right (t_le_normalizer_radicalCore p L T))
      inf_le_left) _ hY
  exact le_inf ((normalizerResidual_le _ _).trans le_sup_left)
    (normalizerResidual_le_normalizer _ _)

/-- For C characteristic inside R, the actual residuals satisfy Y ≤ L_C. -/
theorem normalizerResidual_le_of_characteristic (L R : Subgroup G)
    (C : Subgroup R) [C.Characteristic] :
    normalizerResidual L R ≤ normalizerResidual L (C.map R.subtype) :=
  map_solvableResidual_mono (inf_le_inf_left L
    (normalizer_le_normalizer_characteristic_image R C))

/-- The reverse core containment at the end of p.513. If T normalizes K and
X ≤ K, then O₂(KR) ≤ R. This does not assume that K normalizes R. -/
theorem twoCore_join_le_radicalCore (p : ℕ) (L K : Subgroup G) (T : Sylow 2 G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) (hXK : XiP p L ≤ K) :
    (K ⊔ radicalCore p L T).pCoreIn 2 ≤ radicalCore p L T := by
  have hRT : radicalCore p L T ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow (XiP p L ⊔ (T : Subgroup G))
      (T.subtype le_sup_right)
    simpa only [radicalCore, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le le_sup_right] using h
  have hTN : (T : Subgroup G) ≤
      normalizer ((K ⊔ radicalCore p L T : Subgroup G) : Set G) :=
    (le_inf hTK (t_le_normalizer_radicalCore p L T)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hc : (K ⊔ radicalCore p L T).pCoreIn 2 ≤
      (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (sup_le_sup_left hRT K)
      (sup_le (le_sup_left.trans (K ⊔ radicalCore p L T).le_normalizer) hTN)
  exact hc.trans (pCoreIn_le_pCoreIn_of_sylow T le_sup_right
    (sup_le_sup_right hXK T))

/-- The first reduction on p.513: if L normalizes R, uniqueness for LT
controls all characteristic-subgroup normalizers of R. -/
theorem characteristicNormalizerClosure_le_of_L_normalizes [Finite G]
    (p : ℕ) {L T M : Subgroup G}
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hLR : L ≤ normalizer (radicalCore p L T : Set G)) :
    characteristicNormalizerClosure (radicalCore p L T) ≤ M :=
  characteristicNormalizerClosure_le_of_unique_twoLocal
    (radicalCore_isTwoGroup p L T)
    (sup_le hLR (t_le_normalizer_radicalCore p L T)) hunique

end CFSG.Quasithin.Chapter1.RadicalNormalizers
