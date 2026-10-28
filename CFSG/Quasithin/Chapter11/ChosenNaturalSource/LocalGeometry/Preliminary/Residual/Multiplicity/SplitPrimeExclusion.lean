module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SourceActors
public import CFSG.KnownSimple.PrimeToFifteen

/-!
# Split-prime exclusions for the actual full-orbit actor kernel

The proved prime-residual clause of 11.0.4 survives under the literal
full-orbit action map. Thus, for every prime p > 3 dividing q - 1, a
p-element in the component centralizer lies in the marked full SL₃
component. Its centre has order at most three, so that centralizer has
order prime to p. This uses the original residual equality and needs no
new rank-descent or covering-kernel hypothesis.

In even degree, a perfect subgroup of this centralizer already has order
prime to three. The full known-simple catalogue then forces every such
nontrivial subgroup to have order divisible by five. If five divides
q - 1, there is no such subgroup. Apply this to the actual moved component
and its retained actor orbit from `SourceActors`: every starred actor is
faithful on the component. The literal injective conjugation homomorphism
is supplied, in particular whenever the original field degree is divisible
by four.

The unconditional selected-actor fork retains the same moved component,
orbit, centralizer placement and commutator equality. Its nonfaithful
branch now forces n congruent to two modulo four and a five-element in
the three-free component. This does not exclude that remaining branch,
and faithfulness alone still gives no two-copy bound. Cubic containment
in unconditional 11.0.4 remains with qt-d-1222-natural-preliminary-source;
qt-d-1222-natural-local-geometry retains final chapter assembly.

Source: Aschbacher--Smith, A.3.18, pp.51--54; the nonfaithful argument
of D.3.9, pp.200--201; and 11.0.4, p.760, combined manuscript of
1 March 2004. The complete carrier exclusions are supplied by
`CFSG.KnownSimple.PrimeToFifteen`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The exact source prime residual passes to the original faithful action image. -/
theorem sl3_fullAction_component_prime_residual
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ 2 ^ S.field.degree - 1) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) =
      primeToResidual p (actionImage ρ) := by
  let := fullModule_elementary D S
  let : Fact p.Prime := ⟨hp⟩
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let f := actionHom (fullModuleConjugation D S)
  have he : K = primeToResidual p M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le L.le_normalizer]
    exact sl3_prime_residual D S m hp hp3 hd
  change K.map f = _
  rw [he,map_primeToResidual_of_surjective p f
    (fullModuleConjugation D S).asGroupHom.rangeRestrict_surjective]

/-- The actual component centralizer has order prime to every split prime greater than three. -/
theorem sl3_fullAction_centralizer_coprime_splitPrime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ 2 ^ S.field.degree - 1) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    Nat.Coprime p (Nat.card (centralizer (K : Set (actionImage ρ)))) := by
  let := fullModule_elementary D S
  let : Fact p.Prime := ⟨hp⟩
  let ρ := fullModuleConjugation D S
  let H := actionImage ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  dsimp only
  apply hp.coprime_iff_not_dvd.mpr
  intro hdC
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hdC
  have hxH : orderOf (x : H) = p :=
    (orderOf_injective (centralizer (K : Set H)).subtype Subtype.val_injective x).trans hx
  have hxK : (x : H) ∈ K := by
    apply (sl3_fullAction_component_prime_residual D S m hp hp3 hd).ge
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one,hxH] using pow_orderOf_eq_one (x : H)
  let z : center K := ⟨⟨x,hxK⟩,mem_center_iff.mpr
    (fun k => Subtype.ext (x.property k k.property))⟩
  have hz : orderOf z = p := by
    rw [← orderOf_injective (center K).subtype Subtype.val_injective,
      ← orderOf_injective K.subtype Subtype.val_injective]
    exact hxH
  have hpz : p ∣ Nat.card (center K) := hz ▸ orderOf_dvd_natCard z
  have hcard : Nat.card (center K) ≤ 3 := sl3_fullAction_component_center_card D S m
  have hpos : 0 < Nat.card (center K) := Nat.card_pos
  have := Nat.le_of_dvd hpos hpz
  omega

/-- When five is split, the complete catalogue excludes every nontrivial perfect subgroup of the component centralizer. -/
theorem sl3_fullAction_perfect_centralizer_eq_bot_of_five_split
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) (hfive : 5 ∣ 2 ^ S.field.degree - 1) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ (J : Subgroup (actionImage ρ)) [Group.IsPerfect J],
      J ≤ centralizer (K : Set (actionImage ρ)) → J = ⊥ := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  dsimp only
  intro J hJ hc
  have h3 := sl3_fullAction_perfect_centralizer_coprime D S m heven J hc
  have h5 : Nat.Coprime 5 (Nat.card J) :=
    (sl3_fullAction_centralizer_coprime_splitPrime D S m Nat.prime_five (by decide) hfive).of_dvd_right (card_dvd_of_le hc)
  have hknown : IsKGroup KnownSimple.IsKnownSimple (actionImage ρ) :=
    (normalizer_sqtk D S).isKGroup.of_surjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective
  let := KnownSimple.isSolvable_of_coprime_three_five J (hknown.subgroup J) h3 h5
  by_contra hn
  let : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hn
  exact Group.IsPerfect.not_isSolvable J inferInstance

/-- Apply the exclusion to the actual moved component and its orbit: the starred actor has trivial component kernel. -/
theorem sl3_fullAction_starred_kernel_eq_bot_of_five_split
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) (hfive : 5 ∣ 2 ^ S.field.degree - 1) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup (actionImage ρ), A ∈ ChapterD.QhatStar (imageRepresentation ρ) →
      A ⊓ centralizer (K : Set (actionImage ρ)) = ⊥ := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA
  by_contra hn
  obtain ⟨J,hJ,hm,ho,_,_⟩ :=
    sl3_fullAction_starred_nonfaithful_component D S m heven A hA hn
  let := hJ.2
  have he := sl3_fullAction_perfect_centralizer_eq_bot_of_five_split D S m heven hfive J
    ((le_componentOrbit J A).trans ho)
  rw [he,commutator_bot_left] at hm
  exact hm rfl


/-- A trivial component kernel gives the literal injective conjugation action, with the full component and its inclusion retained. -/
theorem fullAction_component_actor_faithful :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup H, A ⊓ centralizer (K : Set H) = ⊥ →
      ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let H := actionImage ρ
  let K₀ := L.subgroupOf (normalizer (L : Set G))
  let K := K₀.map (actionHom ρ)
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  dsimp only
  intro A hk
  let α : A →* MulAut K := K.normalizerMonoidHom.comp
    (inclusion (show A ≤ normalizer (K : Set H) from le_normalizer_of_normal))
  refine ⟨α,?_,fun _ _ => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff α).mp
  apply bot_unique
  intro a ha
  have hc : (a : H) ∈ centralizer (K : Set H) := by
    intro k hk
    have he := congrArg (fun f : MulAut K => (f ⟨k,hk⟩ : H)) ha
    change (a : H) * k * (a : H)⁻¹ = k at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact Subtype.ext (mem_bot.mp (hk ▸ ⟨a.property,hc⟩))

/-- Every starred actor acts faithfully on the actual component when five is split; no faithfulness premise remains. -/
theorem sl3_fullAction_starred_faithful_of_five_split
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) (hfive : 5 ∣ 2 ^ S.field.degree - 1) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup H, A ∈ ChapterD.QhatStar (imageRepresentation ρ) →
      ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA
  exact fullAction_component_actor_faithful D S A
    (sl3_fullAction_starred_kernel_eq_bot_of_five_split D S m heven hfive A hA)

private theorem five_split_of_four_dvd (n : ℕ) (hn : 4 ∣ n) : 5 ∣ 2 ^ n - 1 :=
  (by decide : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)

/-- Select an actual faithful starred actor on the original full orbit when four divides the original field degree. -/
theorem sl3_fullAction_exists_faithful_starred_actor_of_four_dvd
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hfour : 4 ∣ S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∃ A : Subgroup H, A ∈ ChapterD.QhatStar (imageRepresentation ρ) ∧
      ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
  let := fullModule_elementary D S
  have heven : Even S.field.degree := by
    obtain ⟨k,hk⟩ := hfour
    exact ⟨2*k,by omega⟩
  obtain ⟨A,hA⟩ := fullAction_exists_starred_actor D S
  exact ⟨A,hA,sl3_fullAction_starred_faithful_of_five_split D S m heven
    (five_split_of_four_dvd _ hfour) A hA⟩

/-- A nonfaithful starred actor in even degree forces the original degree to be two modulo four. -/
theorem sl3_fullAction_starred_nonfaithful_degree
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup (actionImage ρ), A ∈ ChapterD.QhatStar (imageRepresentation ρ) →
      A ⊓ centralizer (K : Set (actionImage ρ)) ≠ ⊥ →
      S.field.degree % 4 = 2 := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA hn
  have h4 : ¬ 4 ∣ S.field.degree := by
    intro h4
    exact hn (sl3_fullAction_starred_kernel_eq_bot_of_five_split D S m heven
      (five_split_of_four_dvd _ h4) A hA)
  rw [Nat.dvd_iff_mod_eq_zero] at h4
  obtain ⟨k,hk⟩ := heven
  omega

/-- The complete known-simple catalogue forces a five-element in every nontrivial perfect subgroup of the actual component centralizer. -/
theorem sl3_fullAction_perfect_centralizer_five_dvd
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ (J : Subgroup (actionImage ρ)) [Group.IsPerfect J], J ≠ ⊥ →
      J ≤ centralizer (K : Set (actionImage ρ)) → 5 ∣ Nat.card J := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  dsimp only
  intro J hJ hn hc
  have h3 := sl3_fullAction_perfect_centralizer_coprime D S m heven J hc
  by_contra h5
  have hknown : IsKGroup KnownSimple.IsKnownSimple (actionImage ρ) :=
    (normalizer_sqtk D S).isKGroup.of_surjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective
  let := KnownSimple.isSolvable_of_coprime_three_five J (hknown.subgroup J) h3
    (Nat.prime_five.coprime_iff_not_dvd.mpr h5)
  let : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hn
  exact Group.IsPerfect.not_isSolvable J inferInstance

/-- Unconditional refined actor selection on D and S. The nonfaithful branch retains the original component, orbit and commutator, and supplies its five-divisibility and the degree restriction. -/
theorem sl3_fullAction_exists_starred_actor_refined_cases
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∃ A : Subgroup H, A ∈ ChapterD.QhatStar (imageRepresentation ρ) ∧
      ((A ⊓ centralizer (K : Set H) = ⊥ ∧
        ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹) ∨
       (S.field.degree % 4 = 2 ∧
        ∃ J : Subgroup H, IsComponent H J ∧
          ⁅J,A ⊓ centralizer (K : Set H)⁆ ≠ ⊥ ∧
          componentOrbit J A ≤ centralizer (K : Set H) ∧
          ⁅componentOrbit J A,A ⊓ centralizer (K : Set H)⁆ = componentOrbit J A ∧
          Nat.Coprime 3 (Nat.card J) ∧ 5 ∣ Nat.card J)) := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let H := actionImage ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  obtain ⟨A,hA⟩ := fullAction_exists_starred_actor D S
  refine ⟨A,hA,?_⟩
  by_cases hn : A ⊓ centralizer (K : Set H) = ⊥
  · exact Or.inl ⟨hn,fullAction_component_actor_faithful D S A hn⟩
  · obtain ⟨J,hJ,hm,ho,he,h3⟩ :=
      sl3_fullAction_starred_nonfaithful_component D S m heven A hA hn
    let := hJ.2
    have hJne : J ≠ ⊥ := by
      intro hz
      rw [hz,commutator_bot_left] at hm
      exact hm rfl
    exact Or.inr ⟨sl3_fullAction_starred_nonfaithful_degree D S m heven A hA hn,
      J,hJ,hm,ho,he,h3,sl3_fullAction_perfect_centralizer_five_dvd D S m heven J hJne
        ((le_componentOrbit J A).trans ho)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
