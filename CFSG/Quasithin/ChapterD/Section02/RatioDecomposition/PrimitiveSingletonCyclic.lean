module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalSource
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Cyclic starred actors for a primitive odd residual

A noncyclic starred actor is faithful on O₃. Minimal normality identifies
that nontrivial normal subgroup with the elementary odd residual; the
prime-rank bound makes its order nine. The actual D.2.14 configuration
then supplies two complementary binary support planes. Ambient conjugation
permutes the canonical support family. Its isometry-group bound, together
with cubic ratio greater than one, makes the original group equal to O₃A.
The invariant order-three line in that group contradicts minimal normality.

This uses the genuine two-support geometry of the natural Ω₄⁺(2) tensor
module, and does not treat it as a sum of two natural S₃ modules. The final
theorem removes a globally fixed complementary summand; it applies to the
literal source quotient action in `SourceSingletonClassification`.
Elementary-nine extensions with cyclic starred actors remain possible.

Source: Aschbacher--Smith D.2.14, D.2.19--22, printed pp.186--189,
and the primitive residual step of 14.6.12, printed p.1031.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
open SourceReduction FittingConfigurations
section Local
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {C : GroupClass} (hH : IsSQTK C H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
  (hr : 1 < rank A)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
  (hfull : subspaceCommutator ρ ⊤ (pCore 3 G) = ⊤)
include hH f honto hf hA hr hF hcore hfull
private theorem reduced_of_threeCore_moved :
    ∃ s : ℕ, Reduced (ρ.comp (pCore 3 G ⊔ A).subtype)
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) (A.subgroupOf (pCore 3 G ⊔ A)) s := by
  let P := pCore 3 G
  let L := P ⊔ A
  let P₀ := P.subgroupOf L
  let A₀ := A.subgroupOf L
  let σ := ρ.comp L.subtype
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨hcard,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hsupport := source_lemma_D_2_14_hyperplaneSupport ρ hf hA hcard hfix
  obtain ⟨hElem, ⟨s, hs, hcP, _⟩, hcomm⟩ :=
    ElementaryCore.elementary_structure_of_hyperplaneSupport ρ hf P A pCore_isPGroup
      hcard le_normalizer_of_normal hfaith hfix hsupport
  let : IsElementaryAbelian 3 P := hElem
  have hσ : Function.Injective σ := hf.comp L.subtype_injective
  have hstar : A₀ ∈ QhatStar σ := starred_subgroupOf ρ hA le_sup_right
  have hcA : Nat.card A₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ L from le_sup_right)).toEquiv).trans hcard
  have hcore' : pCore 3 L = P₀ := local_threeCore P A pCore_isPGroup
    (IsElementaryAbelian.isPGroup 2 A)
  have hfaith' : A₀ ⊓ centralizer (P₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1, ?_⟩
    intro p hp
    exact congrArg Subtype.val (ha.2 ⟨p,(le_sup_left : P ≤ L) hp⟩ hp)
  have hfix' : P₀ ⊓ centralizer (A₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro p hp
    apply Subtype.ext
    apply hfix.le
    refine ⟨hp.1, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hp.2 ⟨a,(le_sup_right : A ≤ L) ha⟩ ha)
  refine ⟨s, ⟨hσ, inferInstance, IsElementaryAbelian.subgroupOf le_sup_left,
    ?_, hs, hcA, hstar, ?_, hfaith', hfix', ?_, ?_, ?_⟩⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toEquiv).trans hcP
  · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, hcomm]
  · rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le le_sup_left]
    exact hfull
  · have hh := source_lemma_D_2_14_hyperplaneSupport σ hσ hstar hcA (hcore'.symm ▸ hfix')
    rw [hcore'] at hh
    exact hh

end Local

section Primitive
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A primitive elementary odd residual of rank at most two admits no
noncyclic minimum cubic actor on its fully moved faithful module. -/
theorem primitive_star_cyclic
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (p : ℕ) [Fact p.Prime] (hodd : Odd p)
    (hE : IsElementaryAbelian p (pResidual 2 G)) (hbound : primeRank p G ≤ 2)
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ pResidual 2 G →
      B = ⊥ ∨ B = pResidual 2 G)
    (hfull : subspaceCommutator ρ ⊤ (pResidual 2 G) = ⊤)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (A : Subgroup G) (hA : A ∈ QhatStar ρ) : IsCyclic A := by
  classical
  by_contra hncyc
  have hr : 1 < rank A := by
    have hp := hA.1.2.1.rank_pos
    by_contra hn
    have he : rank A = 1 := by omega
    have hc : Nat.card A = 2 := by rw [hA.1.2.1.card_eq_two_pow_rank,he]; norm_num
    exact hncyc (isCyclic_of_prime_card hc)
  let := hE
  have hF := generalizedFitting_eq_fitting_of_solvable G
  have hRF : pResidual 2 G ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
  have hFm : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤ := by
    apply top_unique
    apply hfull.ge.trans
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hRF hg,v,hv,rfl⟩
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hPne : pCore 3 G ≠ ⊥ := by
    intro hz
    have hh : A ⊓ centralizer (pCore 3 G : Set G) = A := by
      apply inf_eq_left.mpr
      intro a ha x hx
      have hx1 : x = 1 := mem_bot.mp (hz ▸ hx)
      simp only [hx1,mul_one,one_mul]
    exact hA.1.2.1.1 (hh.symm.trans hfaith)
  have hPR : pCore 3 G ≤ pResidual 2 G := by
    have ho : Odd (Nat.card (pCore 3 G)) := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
      exact hn ▸ (by decide : Odd 3).pow
    intro x hx
    exact mem_pResidual_of_orderOf_coprime
      ((Nat.coprime_two_left.mpr ho).coprime_dvd_right
        ((pCore 3 G).orderOf_dvd_natCard hx))
  have hP : pCore 3 G = pResidual 2 G := (hmin _ inferInstance hPR).resolve_left hPne
  have hp3 : p = 3 := by
    by_contra hp
    have hd := IsPGroup.disjoint_of_ne p 3 hp (pCore 3 G) (pCore 3 G)
      ((IsElementaryAbelian.isPGroup p (pResidual 2 G)).to_le hPR) pCore_isPGroup
    exact hPne (disjoint_self.mp hd)
  subst p
  let : IsElementaryAbelian 3 (pCore 3 G) := hP.symm ▸ hE
  have hPc : Nat.card (pCore 3 G) ≤ 9 := by
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 3)]
    exact Nat.pow_le_pow_right (by decide)
      ((Theory.GroupTheory.primeRank_le_of_injective 3 (pCore 3 G).subtype
        (pCore 3 G).subtype_injective).trans hbound)
  have hPfull : subspaceCommutator ρ ⊤ (pCore 3 G) = ⊤ := hP.symm ▸ hfull
  obtain ⟨s,hs⟩ := reduced_of_threeCore_moved ρ hH f honto hf hA hr hF hcore hPfull
  let L := pCore 3 G ⊔ A
  have hsc : Nat.card (pCore 3 G) = 3 ^ s :=
    (Nat.card_congr (subgroupOfEquivOfLe (show pCore 3 G ≤ L from le_sup_left)).toEquiv).symm.trans hs.card_core
  have hs2 : s = 2 := by
    rcases hs.rank_cases with he | he
    · exact he
    · rw [hsc,he] at hPc
      norm_num at hPc
  subst s
  have hPc9 : Nat.card (pCore 3 G) = 9 := hsc
  obtain ⟨d,_,_,_⟩ := hs.configurations _
  let D := d.ofSubgroup ρ (show pCore 3 G ≤ L from le_sup_left)
  have hAc : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ L from le_sup_right)).toEquiv).symm.trans hs.card_actor
  have hLc : Nat.card L = 36 := by
    have hd : Disjoint (pCore 3 G) A :=
      Subgroup.disjoint_of_coprime_natCard (by rw [hPc9,hAc]; decide)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal hd,hPc9,hAc]
  have hlow : 1 < cubicRatio ρ := by
    rw [(solvable_source_ratio_and_noncyclic ρ hH f honto hf hA hr hcore hFm).2.1]
    norm_num [ENNReal.lt_div_iff_mul_lt]
  have hL : L = ⊤ := D.eq_top_of_card_thirty_six ρ hf (D.factor_conj_closed ρ hf) L hLc hlow
  obtain ⟨Z,hZ⟩ := hs.exists_invariant_line _
  let : Z.Normal := normalizer_eq_top_iff.mp (top_unique (hs.invariant_line_normalizer _ hZ))
  have hontoL : Function.Surjective L.subtype := MonoidHom.range_eq_top.mp ((range_subtype L).trans hL)
  let : (Z.map L.subtype).Normal := (inferInstance : Z.Normal).map _ hontoL
  have hZc : Nat.card (Z.map L.subtype) = 3 :=
    (Subgroup.card_map_of_injective L.subtype_injective).trans hZ.2.1
  have hZP : Z.map L.subtype ≤ pResidual 2 G := by
    apply le_trans (map_mono hZ.1)
    rw [map_subgroupOf_eq_of_le (show pCore 3 G ≤ L from le_sup_left),hP]
  rcases hmin (Z.map L.subtype) inferInstance hZP with hz | hz
  · rw [hz,card_bot] at hZc
    norm_num at hZc
  · rw [hz,←hP,hPc9] at hZc
    norm_num at hZc

/-- The primitive cyclicity argument allows the actual globally fixed
complement occurring in the source quotient module. -/
theorem primitive_star_cyclic_of_fixed_complement
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (p : ℕ) [Fact p.Prime] (hodd : Odd p)
    (hE : IsElementaryAbelian p (pResidual 2 G)) (hbound : primeRank p G ≤ 2)
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ pResidual 2 G →
      B = ⊥ ∨ B = pResidual 2 G)
    (hspan : subspaceCommutator ρ ⊤ (pResidual 2 G) ⊔ fixedSpace ρ ⊤ = ⊤)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (A : Subgroup G) (hA : A ∈ QhatStar ρ) : IsCyclic A := by
  let P := pResidual 2 G
  let U := subspaceCommutator ρ ⊤ P
  have hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  let W : Subrepresentation ρ := {
    toSubmodule := U
    apply_mem_toSubmodule := fun g _ hv => (hU (mem_top g) _).mpr hv }
  have hfaith : Function.Injective W.toRepresentation :=
    subrepresentation_faithful_of_fixed_complement ρ hf W hspan
  have hstar : A ∈ QhatStar W.toRepresentation := fixed_complement_starred ρ W hspan hA
  let := hE
  have ho : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p P).exists_card_eq
    exact hn ▸ hodd.pow
  have hfull : subspaceCommutator W.toRepresentation ⊤ P = ⊤ := by
    apply Submodule.map_injective_of_injective U.subtype_injective
    have hh := subspaceCommutator_map_embedding ρ W.toRepresentation
      (MonoidHom.id G) U.subtype (fun _ _ => rfl) P ⊤
    have hm := NormalOddSeed.odd_moved_self ρ P ho
    change subspaceCommutator ρ U P = U at hm
    simpa only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,hm] using hh.symm
  exact primitive_star_cyclic W.toRepresentation hfaith hcore p hodd hE hbound hmin
    hfull hH f honto A hstar

end Primitive

end CFSG.Quasithin.ChapterD.RatioDecomposition
