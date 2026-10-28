module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The actual outer action in the swapped-component argument

Conjugation on a normal subgroup descends through its characteristic two-core.
For the normalizer of an odd subgroup in a Sylow two-subgroup, the kernel of
this outer action centralizes the odd subgroup, provided the quotient is
centerless and the odd image normalizes the Sylow image.

An inner automorphism in this action is conjugation by a two-element of the
centerless quotient. Sylow restriction and quotient transport place that
element in the Sylow image. Mutual normalization and coprimality force it to
centralize the odd image. The quotient is faithful on the odd subgroup, so
centralization lifts back to the original group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter
variable {M : Type*} [Group M] (N : Subgroup M) [N.Normal]

/-- The image of the actual intersection with N in N/O₂(N). -/
abbrev Image (A : Subgroup M) : Subgroup (N ⧸ pCore 2 N) :=
  (A.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))

/-- Ambient conjugation descends through the characteristic two-core. -/
def quotientAction : M →* MulAut (N ⧸ pCore 2 N) :=
  (quotientAut (pCore 2 N)).comp MulAut.conjNormal

/-- The quotient action is induced by ambient conjugation on representatives. -/
theorem quotientAction_mk (a : M) (x : N) :
    quotientAction N a (QuotientGroup.mk' (pCore 2 N) x) =
      QuotientGroup.mk' (pCore 2 N) (MulAut.conjNormal a x) :=
  quotientAut_apply_mk _ _ _

/-- The outer action of the actual subgroup N_T(P). -/
def outerAction (T P : Subgroup M) : (T ⊓ normalizer P : Subgroup M) →*
    MulAut.Outer (N ⧸ pCore 2 N) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (N ⧸ pCore 2 N))).comp
    ((quotientAction N).comp (T ⊓ normalizer P).subtype)

/-- Normalization of an ambient subgroup preserves its quotient image. -/
theorem action_mem_image {A : Subgroup M} {a : M} (ha : a ∈ normalizer A)
    {x : N ⧸ pCore 2 N} (hx : x ∈ Image N A) :
    quotientAction N a x ∈ Image N A := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [quotientAction_mk]
  apply mem_map_of_mem
  change a * (y : M) * a⁻¹ ∈ A
  exact (mem_normalizer_iff.mp ha _).mp hy

/-- Normal restriction followed by the quotient map gives the Sylow image. -/
theorem image_sylow [Finite M] (T : Sylow 2 M) :
    ∃ S : Sylow 2 (N ⧸ pCore 2 N), (S : Subgroup _) = Image N T := by
  obtain ⟨R, hR⟩ := T.exists_subgroupOf_eq_of_normal N
  refine ⟨R.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hR]

omit [N.Normal] in
/-- Quotienting by the two-core is injective on every odd p-subgroup. -/
theorem odd_quotient_injective {p : ℕ} [Fact p.Prime] {P : Subgroup M}
    (hp : Odd p) (hP : IsPGroup p P) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 N)).subgroupMap (P.subgroupOf N)) := by
  have hd : Disjoint (pCore 2 N) (P.subgroupOf N) :=
    pCore_isPGroup.disjoint_of_coprime hP.comap_subtype (Nat.coprime_two_left.mpr hp)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hc : (x : N) ∈ pCore 2 N := (QuotientGroup.eq_one_iff _).mp
    (congrArg Subtype.val hx)
  exact Subtype.ext (hd.le_bot ⟨hc, x.property⟩)

/-- Coprime mutual normalization forces the inner normalizer to centralize. -/
theorem inner_normalizer_centralizes {p : ℕ} [Fact p.Prime] {L : Type*} [Group L]
    (hp : Odd p) {S R : Subgroup L} (hS : IsPGroup 2 S) (hR : IsPGroup p R)
    (hn : R ≤ normalizer S) : S ⊓ normalizer R ≤ centralizer (R : Set L) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  have hcommR : ⁅S ⊓ normalizer R, R⁆ ≤ R :=
    le_normalizer_iff_commutator_le_right.mp inf_le_right
  have hcommS : ⁅S ⊓ normalizer R, R⁆ ≤ S :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hn)
  exact (le_inf hcommS hcommR).trans
    (hS.disjoint_of_coprime hR (Nat.coprime_two_left.mpr hp)).le_bot

/-- Inner actions in N_T(P) act trivially on P itself. -/
theorem outer_kernel_centralizes [Finite M] {p : ℕ} [Fact p.Prime]
    (T : Sylow 2 M) (P : Subgroup M) (hp : Odd p) (hP : IsPGroup p P)
    (hPN : P ≤ N) (hn : Image N P ≤ normalizer (Image N T))
    (hc : center (N ⧸ pCore 2 N) = ⊥) :
    (outerAction N T P).ker ≤ (centralizer (P : Set M)).subgroupOf
      ((T : Subgroup M) ⊓ normalizer P) := by
  intro a ha
  have hi : quotientAction N (a : M) ∈ MulAut.innerSubgroup (N ⧸ pCore 2 N) :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨z, hz⟩ := hi
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨a, a.property.1⟩
  have hka : (a : M) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hzp : z ^ (2 ^ k) = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hc
    rw [map_pow, hz, ← map_pow, hka, map_one, map_one]
  have hzgroup : IsPGroup 2 (zpowers z) := IsPGroup.of_card_dvd_pow (n := k)
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hzp)
  have hzT : z ∈ normalizer (Image N T) := by
    apply mem_normalizer_fintype
    intro x hx
    change MulAut.conj z x ∈ Image N T
    rw [hz]
    exact action_mem_image N (le_normalizer a.property.1) hx
  have hzP : z ∈ normalizer (Image N P) := by
    apply mem_normalizer_fintype
    intro x hx
    change MulAut.conj z x ∈ Image N P
    rw [hz]
    exact action_mem_image N a.property.2 hx
  obtain ⟨S, hS⟩ := image_sylow N T
  have hzS : z ∈ (S : Subgroup _) := by
    have hmem : z ∈ zpowers z ⊓ normalizer (S : Set (N ⧸ pCore 2 N)) :=
      ⟨mem_zpowers z, by
        change z ∈ normalizer ((S : Subgroup (N ⧸ pCore 2 N)) : Set _)
        rw [hS]
        exact hzT⟩
    rw [hzgroup.inf_normalizer_sylow S] at hmem
    exact hmem.2
  have hcentral : z ∈ centralizer (Image N P : Set _) :=
    inner_normalizer_centralizes hp S.isPGroup'
      (hP.comap_subtype.map (QuotientGroup.mk' (pCore 2 N)))
      (hS ▸ hn) ⟨hzS, hzP⟩
  intro x hx
  let y : P.subgroupOf N := ⟨⟨x, hPN hx⟩, hx⟩
  let y' : P.subgroupOf N := ⟨MulAut.conjNormal (a : M) (y : N),
    (mem_normalizer_iff.mp a.property.2 x).mp hx⟩
  have he : (QuotientGroup.mk' (pCore 2 N)).subgroupMap (P.subgroupOf N) y' =
      (QuotientGroup.mk' (pCore 2 N)).subgroupMap (P.subgroupOf N) y := by
    apply Subtype.ext
    change QuotientGroup.mk' (pCore 2 N) (MulAut.conjNormal (a : M) (y : N)) = _
    rw [← quotientAction_mk, ← hz]
    change z * _ * z⁻¹ = _
    rw [← hcentral _ (mem_map_of_mem _ y.property), mul_inv_cancel_right]
    rfl
  have hxy := congrArg (fun v : P.subgroupOf N => ((v : N) : M))
    (odd_quotient_injective N hp hP he)
  change (a : M) * x * (a : M)⁻¹ = x at hxy
  exact (mul_inv_eq_iff_eq_mul.mp hxy).symm

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter
