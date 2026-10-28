module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralResidual
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import Theory.GroupTheory.AbelianIndexTwoCenter

/-!
# Two-group movement of the marked dihedral prime kernel

For a faithful binary action with quadratic ratio two and marked dihedral
Jhat of degree at most four, every starred actor has rank one. The cubic
minimum is therefore two, and every involution belongs to Jhat. Its odd
prime kernel is self-centralizing inside Jhat, so every nontrivial two-group
in the ambient actor moves that kernel. The exact Jhat marking is essential;
a merely normal dihedral subgroup need not have this property.

Source: Aschbacher--Smith15.2.1--3, printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem dihedral_involutions_mem_Jhat
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hq : quadraticRatio ρ = 2)
    (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) {p m : ℕ}
    (hp : PrimeDimensionOptions p m) (hd : DihedralMarking l p m)
    (t : D) (ht : orderOf t = 2) : t ∈ Jhat ρ := by
  let : (Jhat ρ).Normal := Jhat_normal ρ
  have hKcard := (hd.ambient_marks (Jhat ρ) hp).1
  have hstar : (QhatStar ρ).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hz : Jhat ρ = ⊥ := by simp [Jhat, he]
    have hh : Nat.card (Jhat ρ) = 1 := by rw [hz]; simp
    rw [hh] at hKcard
    omega
  obtain ⟨A,hA⟩ := hstar
  have hAK : A ≤ Jhat ρ := le_sSup hA
  have hr : rank A = 1 := by
    have hlow := hA.1.2.1.rank_pos
    have hhigh : rank A ≤ 1 := by
      by_contra! hh
      have hdiv : 4 ∣ Nat.card A := by
        rw [hA.1.2.1.card_eq_two_pow_rank]
        exact pow_dvd_pow 2 (by omega : 2 ≤ rank A)
      have hdiv' := hdiv.trans (card_dvd_of_le hAK)
      rw [hKcard] at hdiv'
      rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num at hdiv'
    omega
  have hq3 : cubicRatio ρ = 2 := by
    rcases QhatStar.ratio_one_or_two_of_rank_one ρ hf hA hr with h1 | h2
    · have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp
        ((isFFModule_iff_cubicRatio_le_one ρ).mpr h1.le)
      rw [hq] at hh
      norm_num at hh
    · exact h2
  obtain ⟨he,hr,hquad,hhalf⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  have hdim : Module.finrank (ZMod 2) W ≤ 4 := by
    have hh := hd.dimension
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> omega
  have hcodim : fixedCodim ρ (zpowers t) = 2 := by
    have hlo : quadraticRatio ρ ≤ actionRatio ρ (zpowers t) :=
      iInf_le_of_le (zpowers t) (iInf_le_of_le ⟨he,hquad⟩ le_rfl)
    rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hlo
    have hlo' : 2 ≤ fixedCodim ρ (zpowers t) := by exact_mod_cast hlo
    omega
  have hmin : zpowers t ∈ QhatMin ρ := by
    refine ⟨hq3.le,he,isCubic_of_isQuadratic hquad,?_⟩
    simp [actionRatio,hr,hcodim,hq3]
  have hs : zpowers t ∈ QhatStar ρ := by
    refine ⟨hmin,?_⟩
    intro B hB hBt
    apply eq_of_le_of_card_ge hBt
    rw [Nat.card_zpowers,ht]
    have hn := (one_lt_card_iff_ne_bot B).mpr hB.2.1.1
    omega
  exact (le_sSup hs) (mem_zpowers t)

theorem dihedral_prime_moves_twoGroup
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hq : quadraticRatio ρ = 2)
    (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) {p m : ℕ}
    (hp : PrimeDimensionOptions p m) (hd : DihedralMarking l p m)
    (R : Subgroup D) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ¬ R ≤ centralizer (l.kernel.map (Jhat ρ).subtype : Set D) := by
  have hpprime : Nat.Prime p := by
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  let : Fact p.Prime := ⟨hpprime⟩
  let : IsCyclic l.kernel := isCyclic_of_prime_card hd.card_kernel
  have hncomm : ¬ IsMulCommutative (Jhat ρ) := by
    intro hc
    let := hc
    apply l.nontrivial
    rw [←l.commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr (fun x _ y _ => mul_comm _ _)
  have hC := centralizer_eq_of_abelian_index_two l.kernel l.kernel_index_two hncomm
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  have hnpos : 0 < n := by
    have hcard := (one_lt_card_iff_ne_bot R).mpr hne
    rw [hn] at hcard
    by_contra! hz
    have : n = 0 := by omega
    simp [this] at hcard
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  have hto : orderOf (t : D) = 2 := (R.orderOf_coe t).trans ht
  have htK := dihedral_involutions_mem_Jhat ρ hf hq l hp hd (t : D) hto
  let tK : Jhat ρ := ⟨t,htK⟩
  intro hRC
  have htC : tK ∈ centralizer (l.kernel : Set (Jhat ρ)) := by
    intro x hx
    apply Subtype.ext
    exact hRC t.property (x : D) (mem_map_of_mem _ hx)
  have htP : tK ∈ l.kernel := hC ▸ htC
  have hdiv := l.kernel.orderOf_dvd_natCard htP
  rw [hd.card_kernel] at hdiv
  have hto' : orderOf tK = 2 := (Subgroup.orderOf_coe tK).symm.trans hto
  rw [hto'] at hdiv
  rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num at hdiv

end CFSG.Quasithin.ChapterD.CyclicSource
