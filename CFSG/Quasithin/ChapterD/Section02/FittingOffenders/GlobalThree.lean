module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Injective
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Data.Finite.Perm

/-!
# The global three-plane endpoint

Suppose an elementary abelian three-core of order 27 has three binary
support planes spanning the faithful original module, and the whole group
normalizes each marked core factor. If involution centralizers in the core
are cyclic, any elementary four-subgroup supplements the core: the whole
group has order 108, and that four-subgroup is Sylow.

Restriction to the three nonzero vectors of each support plane embeds the
group in a product of three symmetric groups of degree three. The core and
four-subgroup generate a subgroup of order 108. If the ambient group has
order 216, the embedding is onto. An involution moving only the first
coordinate centralizes the kernel of that coordinate projection, of order
36. Its intersection with the normal three-core then has order greater
than three, contrary to cyclicity inside an elementary three-group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.22, the three invariant support planes furnished by D.2.14(7)(ii).
The source assembly supplies the involution-centralizer hypothesis from
the original SQTK quotient and D.2.21. The support factors, their original
module action, and the chosen four-subgroup are preserved literally.
-/

open Representation.BinaryOffender
open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.ChapterD.FittingConfigurations

private noncomputable def nonzeroPermutation
    {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) : G →* Equiv.Perm {w : W // w ≠ 0} := by
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp σ.asGroupHom
  exact {
    toFun := fun g => Equiv.Perm.subtypePerm (e g).toEquiv (fun w => by simp)
    map_one' := by ext w; exact congrArg (fun a : W ≃ₗ[ZMod 2] W => a w) (e.map_one)
    map_mul' := by intro g h; ext w; exact congrArg (fun a : W ≃ₗ[ZMod 2] W => a w) (e.map_mul g h) }

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {P : Subgroup G}

omit [Finite G] in
private theorem support_permutation_embedding (d : SupportFactors ρ P 3)
    (hf : Function.Injective ρ)
    (hn : ∀ g : G, ∀ i, g ∈ normalizer (d.ambient i : Set G)) :
    ∃ (X : Fin 3 → Type v) (_ : ∀ i, Fintype (X i)),
      (∀ i, Nat.card (X i) = 3) ∧
      ∃ f : G →* ((i : Fin 3) → Equiv.Perm (X i)), Function.Injective f := by
  classical
  let U (i : Fin 3) := subspaceCommutator ρ ⊤ (d.ambient i)
  have hstable (g : G) (i : Fin 3) : g ∈ subspaceStabilizer ρ (U i) := by
    have hh := subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (A := (⊤ : Subgroup G)) (by intros; trivial))
      (show (⊤ : Subgroup G) ≤ normalizer (d.ambient i : Set G) from fun a _ => hn a i)
    exact hh (mem_top g)
  let σ (i : Fin 3) : Representation (ZMod 2) G (U i) :=
    (stabilizerRepresentation ρ (U i)).comp
      { toFun := fun g => ⟨g,hstable g i⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  let X (i : Fin 3) := {u : U i // u ≠ 0}
  let _ (i : Fin 3) : Finite (U i) := Module.finite_of_finite (ZMod 2)
  let _ (i : Fin 3) : Fintype (X i) := Fintype.ofFinite (X i)
  have hc (i : Fin 3) : Nat.card (X i) = 3 := by
    let : Fintype (U i) := Fintype.ofFinite (U i)
    have hu : Nat.card (U i) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      change 2 ^ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient i)) = 4
      rw [SupportFactors.ambient, d.support_dim i]
      norm_num
    have hc := Fintype.card_subtype_compl (fun u : U i => u = 0)
    simp only [Fintype.card_unique] at hc
    simpa only [Nat.card_eq_fintype_card, X, ← Nat.card_eq_fintype_card, hu] using hc
  let f : G →* ((i : Fin 3) → Equiv.Perm (X i)) :=
    { toFun := fun g i => nonzeroPermutation (σ i) g
      map_one' := funext (fun i => (nonzeroPermutation (σ i)).map_one)
      map_mul' := fun g h => funext (fun i => (nonzeroPermutation (σ i)).map_mul g h) }
  refine ⟨X,inferInstance,hc,f,?_⟩
  intro a b hab
  apply hf
  ext v
  obtain ⟨w, hw⟩ := d.add_bijective.2 v
  have he (i : Fin 3) : ρ a (w i) = ρ b (w i) := by
    by_cases hzero : w i = 0
    · simp only [hzero, ZeroMemClass.coe_zero, map_zero]
    have hi := congrArg (fun q => (q i (⟨w i,hzero⟩ : X i)).val) hab
    change σ i a (w i) = σ i b (w i) at hi
    exact congrArg Subtype.val hi
  rw [← hw, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => he i)


omit [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
private theorem card_lt_216_of_three_permutations
    (X : Fin 3 → Type*) [∀ i, Fintype (X i)] (hX : ∀ i, Nat.card (X i) = 3)
    (f : G →* ((i : Fin 3) → Equiv.Perm (X i))) (hf : Function.Injective f)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P] (hP : Nat.card P = 27)
    (hc : ∀ t : G, orderOf t = 2 → IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    Nat.card G < 216 := by
  classical
  let H := (i : Fin 3) → Equiv.Perm (X i)
  have hH : Nat.card H = 216 := by
    simp only [H, Nat.card_pi, Nat.card_perm, hX]
    norm_num [Nat.factorial]
  have hle : Nat.card G ≤ 216 := hH ▸ Nat.card_le_card_of_injective f hf
  suffices Nat.card G ≠ 216 by omega
  intro hG
  have honto : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply f.range.eq_top_of_card_eq
    calc Nat.card f.range = Nat.card G := Nat.card_range_of_injective hf
         _ = Nat.card H := hG.trans hH.symm
  let : Nontrivial (X 0) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hX]; decide)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (X 0)
  let s : H := Function.update 1 0 (Equiv.swap x y)
  have hs : s ^ 2 = 1 := by
    funext i
    change s i * s i = 1
    by_cases hi : i = 0
    · subst i
      simp [s]
    · simp [s, hi]
  have hsne : s ≠ 1 := by
    intro he
    have hh := congrArg (fun a : H => a 0 x) he
    simp [s] at hh
    exact hxy hh.symm
  obtain ⟨t,ht⟩ := honto s
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · apply hf
      rw [map_pow,ht,hs,map_one]
    · intro he
      apply hsne
      rw [← ht,he,map_one]
  let f0 : G →* Equiv.Perm (X 0) :=
    { toFun := fun g => f g 0
      map_one' := congrFun f.map_one 0
      map_mul' := fun g h => congrFun (f.map_mul g h) 0 }
  have hf0 : Function.Surjective f0 := by
    intro a
    obtain ⟨g,hg⟩ := honto (Function.update 1 0 a)
    exact ⟨g,by change f g 0 = a; rw [hg]; simp⟩
  have hKcard : Nat.card f0.ker = 36 := by
    have hk := f0.ker.index_mul_card
    rw [index_ker, f0.range_eq_top_of_surjective hf0, card_top, Nat.card_perm,hX,hG] at hk
    norm_num [Nat.factorial] at hk
    change 6 * Nat.card f0.ker = 216 at hk
    omega
  have hKC : f0.ker ≤ centralizer ({t} : Set G) := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    apply hf
    rw [map_mul,map_mul,ht]
    funext i
    by_cases hi : i = 0
    · subst i
      change f g 0 = 1 at hg
      simp [s,hg]
    · simp [s,hi]
  let C := P ⊓ f0.ker
  let : IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G) := hc t ht2
  let : IsCyclic C := Subgroup.isCyclic_of_le (inf_le_inf_left P hKC)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.of_injective
    (Subgroup.inclusion (show C ≤ P from inf_le_left)) (Subgroup.inclusion_injective _)
  have hC : Nat.card C ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 C
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes P f0.ker
    (by rw [normalizer_eq_top]; exact le_top)
  have hjoin : Nat.card (P ⊔ f0.ker : Subgroup G) ≤ 216 :=
    hG ▸ (P ⊔ f0.ker : Subgroup G).card_le_card_group
  change Nat.card P * Nat.card f0.ker = Nat.card C * _ at hprod
  rw [hP,hKcard] at hprod
  nlinarith


/-- Three globally invariant binary support planes give the full D.2.22
three-plane group once involution centralizers in the core are cyclic. -/
public theorem SupportFactors.three_plane_global
    (d : SupportFactors ρ P 3) (hf : Function.Injective ρ)
    [P.Normal] [IsElementaryAbelian 3 P] (hP : Nat.card P = 27)
    (hn : ∀ g : G, ∀ i, g ∈ normalizer (d.ambient i : Set G))
    (hc : ∀ t : G, orderOf t = 2 → IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) :
    P ⊔ A = ⊤ ∧ Nat.card G = 108 ∧ ∃ S : Sylow 2 G, (S : Subgroup G) = A := by
  obtain ⟨X,hfin,hX,f,hf'⟩ := support_permutation_embedding d hf hn
  let := hfin
  have hlt := card_lt_216_of_three_permutations X hX f hf' P hP hc
  have hdis : Disjoint P A := IsPGroup.disjoint_of_coprime
    (IsElementaryAbelian.isPGroup 3 P) (IsElementaryAbelian.isPGroup 2 A) (by decide)
  have hjoin : Nat.card (P ⊔ A : Subgroup G) = 108 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P A
      (by rw [normalizer_eq_top]; exact le_top) hdis, hP,hA]
  obtain ⟨k,hk⟩ := (P ⊔ A : Subgroup G).card_subgroup_dvd_card
  rw [hjoin] at hk
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hG : Nat.card G = 108 := by omega
  refine ⟨(P ⊔ A : Subgroup G).eq_top_of_card_eq (hjoin.trans hG.symm), hG, ?_⟩
  exact ⟨Sylow.ofCard A (by rw [hA,hG]; decide +kernel), rfl⟩

end CFSG.Quasithin.ChapterD.FittingConfigurations
