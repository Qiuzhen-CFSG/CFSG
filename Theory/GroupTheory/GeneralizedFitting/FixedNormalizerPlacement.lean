module

public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Components of fixed subgroups in a normalizer

Let L be centerless and have solvable outer automorphism group. If a set S
normalizes L, every component of C_{N_G(L)}(S) lies in L or in C_G(L).
Perfectness, applied to the actual action N_G(L)/C_G(L), first puts the
component in L C_G(L). Uniqueness of direct-product coordinates splits the
S-centralizer in this product. The relative component dichotomy for its two
normal factors then gives the conclusion.

This is the component-theoretic inference used in Aschbacher–Smith,
combined manuscript of 1 March 2004, Lemma 16.4.8, printed p.1188. The proof
uses ordinary components and relative normality; it requires no classification
hypothesis beyond the explicitly stated solvability of Out(L).
-/

namespace Theory.GroupTheory
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The actual H/K action; the kernel is the relative centralizer. -/
private noncomputable def quotientAction (A : Subgroup G) :
    (normalizer (A : Set G) ⧸
      (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))) →* MulAut A :=
  QuotientGroup.lift _ A.normalizerMonoidHom (by rw [normalizerMonoidHom_ker])

private theorem perfect_le_product {A D : Subgroup G} [Group.IsPerfect D]
    [Group.IsSolvable (MulAut.Outer A)]
    (hDN : D ≤ normalizer (A : Set G)) : D ≤ A ⊔ centralizer (A : Set G) := by
  let incl := inclusion hDN
  let q := QuotientGroup.mk' ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)))
  let f : D →* MulAut.Outer A :=
    (QuotientGroup.mk' (MulAut.innerSubgroup A)).comp
      ((quotientAction A).comp (q.comp incl))
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro d hd
  have hf : f ⟨d, hd⟩ = 1 := congrArg f.range.subtype
    (hs.elim (⟨f ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ : f.range) 1)
  have hi : A.normalizerMonoidHom ⟨d, hDN hd⟩ ∈ MulAut.innerSubgroup A :=
    (QuotientGroup.eq_one_iff _).mp hf
  obtain ⟨a, ha⟩ := hi
  let aN : normalizer (A : Set G) := ⟨a, A.le_normalizer a.property⟩
  have haN : A.normalizerMonoidHom aN = MulAut.conj a := by ext x; rfl
  have hk : aN⁻¹ * ⟨d, hDN hd⟩ ∈ A.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, haN, ha, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hm := (A ⊔ centralizer (A : Set G)).mul_mem
    (mem_sup_left a.property) (mem_sup_right (show (a : G)⁻¹ * d ∈ centralizer (A : Set G) from hk))
  simpa only [mul_inv_cancel_left] using hm

/-- Uniqueness of the coordinates makes fixed points split over a direct product. -/
private theorem fixed_product {A B : Subgroup G} (hd : Disjoint A B)
    (hc : A ≤ centralizer (B : Set G)) {s : Set G}
    (hA : s ⊆ normalizer (A : Set G)) (hB : s ⊆ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ centralizer s ≤
      (A ⊓ centralizer s) ⊔ (B ⊓ centralizer s) := by
  intro x hx
  have hBA : B ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hp : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hBA]
    exact hx.1
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  change a * b = x at hab
  have hfix (t : G) (ht : t ∈ s) :
      t * a * t⁻¹ = a ∧ t * b * t⁻¹ = b := by
    have hmul : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
      calc
        _ = t * (a * b) * t⁻¹ := by group
        _ = t * x * t⁻¹ := by rw [hab]
        _ = x := by rw [hx.2 t ht, mul_inv_cancel_right]
        _ = a * b := hab.symm
    have he := mul_injective_of_disjoint hd
      (a₁ := (⟨t * a * t⁻¹, (mem_normalizer_iff.mp (hA ht) a).mp ha⟩,
        ⟨t * b * t⁻¹, (mem_normalizer_iff.mp (hB ht) b).mp hb⟩))
      (a₂ := (⟨a, ha⟩, ⟨b, hb⟩)) hmul
    exact ⟨congrArg (fun v : A × B => (v.1 : G)) he,
      congrArg (fun v : A × B => (v.2 : G)) he⟩
  have haC : a ∈ centralizer s := fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfix t ht).1
  have hbC : b ∈ centralizer s := fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfix t ht).2
  exact hab ▸ mul_mem_sup ⟨ha, haC⟩ ⟨hb, hbC⟩

/-- A component in a product of two normal subgroups lies in one of them. -/
private theorem component_le_factor {A B D M : Subgroup G}
    (hD : IsComponentIn D M) (hAle : A ≤ M) (hBle : B ≤ M)
    (hAM : M ≤ normalizer (A : Set G))
    (hBM : M ≤ normalizer (B : Set G)) (hDM : D ≤ A ⊔ B) :
    D ≤ A ∨ D ≤ B := by
  let : (A.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hAM
  let : (B.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hBM
  rcases hD.2.normal_dichotomy (A.subgroupOf M) with hA | hA
  · left
    intro d hd
    exact hA (show (⟨d, hD.1 hd⟩ : M) ∈ D.subgroupOf M from hd)
  rcases hD.2.normal_dichotomy (B.subgroupOf M) with hB | hB
  · right
    intro d hd
    exact hB (show (⟨d, hD.1 hd⟩ : M) ∈ D.subgroupOf M from hd)
  have hDA : D ≤ centralizer (A : Set G) := by
    intro d hd a ha
    have hc := commutator_eq_bot_iff_le_centralizer.mp hA
      (show (⟨d, hD.1 hd⟩ : M) ∈ D.subgroupOf M from hd)
      ⟨a, hAle ha⟩ ha
    exact congrArg M.subtype hc
  have hDB : D ≤ centralizer (B : Set G) := by
    intro d hd b hb
    have hc := commutator_eq_bot_iff_le_centralizer.mp hB
      (show (⟨d, hD.1 hd⟩ : M) ∈ D.subgroupOf M from hd)
      ⟨b, hBle hb⟩ hb
    exact congrArg M.subtype hc
  have hcomm : ⁅D, D⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hDM.trans (sup_le (le_centralizer_iff.mp hDA) (le_centralizer_iff.mp hDB))
  let := hD.quasisimple
  rw [commutator_eq_self] at hcomm
  exact (hD.ne_bot hcomm).elim

/-- Components in a fixed subgroup of N_G(L) lie in one of its commuting
factors, when L is centerless and Out(L) is solvable. -/
public theorem IsComponentIn.le_or_le_centralizer_of_fixed_normalizer
    {L D : Subgroup G} {s : Set G} [Group.IsSolvable (MulAut.Outer L)]
    (hD : IsComponentIn D (Subgroup.normalizer (L : Set G) ⊓ centralizer s))
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hs : s ⊆ Subgroup.normalizer (L : Set G)) :
    D ≤ L ∨ D ≤ centralizer (L : Set G) := by
  let K := centralizer (L : Set G)
  let C := centralizer s
  let M := Subgroup.normalizer (L : Set G) ⊓ C
  let := hD.quasisimple
  have hprod : D ≤ L ⊔ K := perfect_le_product (hD.1.trans inf_le_left)
  have hcomm : L ≤ centralizer (K : Set G) := le_centralizer_iff.mpr le_rfl
  have hsK : s ⊆ Subgroup.normalizer (K : Set G) :=
    fun _ hx => normalizer_le_normalizer_centralizer L (hs hx)
  have hsplit : D ≤ (L ⊓ C) ⊔ (K ⊓ C) :=
    (le_inf hprod (hD.1.trans inf_le_right)).trans
      (fixed_product hdisjoint hcomm hs hsK)
  have hLle : L ⊓ C ≤ M := le_inf (inf_le_left.trans L.le_normalizer) inf_le_right
  have hKle : K ⊓ C ≤ M :=
    le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right
  have hnormL : M ≤ Subgroup.normalizer (L ⊓ C : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnormK : M ≤ Subgroup.normalizer (K ⊓ C : Set G) :=
    (le_inf (inf_le_left.trans (normalizer_le_normalizer_centralizer L))
      (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  exact (component_le_factor hD hLle hKle hnormL hnormK hsplit).imp
    (fun hh => hh.trans inf_le_left) (fun hh => hh.trans inf_le_left)

end Theory.GroupTheory
