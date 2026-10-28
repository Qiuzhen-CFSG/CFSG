module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.RowKernels
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.InvariantNormalizer
public import Theory.GroupAction.FixedComponentActionKernel

/-!
# The exact source kernel in the retained invariant rows

The retained row fixes the original source component uniquely and bounds its commuting pointwise fixer by two. The marked involution realizes the nonidentity actor. Thus the literal R-intersection with the containing-component centralizer has index two.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection PrimeRows
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_invariant_kernel
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (t i : G) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hKi : K ≤ centralizer ({i} : Set G))
    (htI : t ∈ centralizer ({i} : Set G))
    (X : Subgroup (centralizer ({i} : Set G))) [X.Normal]
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (hKX : K.subgroupOf (centralizer ({i} : Set G)) ≤ X)
    (a : MulAut X) (ha : orderOf a = 2)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      t * ((x : centralizer ({i} : Set G)) : G) * t⁻¹)
    (hB : IsComponentIn ((K.subgroupOf (centralizer ({i} : Set G))).subgroupOf X) a.fixedSubgroup)
    (hm : PrimeFixedQuotientModels (X ⧸ center X) (quotientAut (center X) a)) :
    ((S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤ normalizer (K : Set G)) ∧
    (let Gi := centralizer ({i} : Set G)
     let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
     ((R ⊓ centralizer (X.map Gi.subtype : Set G)).subgroupOf R).index = 2) := by
  let Gi := centralizer ({i} : Set G)
  let Y := (S : Subgroup H).map H.subtype
  let D := K.subgroupOf Gi
  let B := (D.subgroupOf X).subgroupOf a.fixedSubgroup
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
  let RI := R.subgroupOf Gi
  let tI : Gi := ⟨t,htI⟩
  let : IsQuasisimple X := hX.2
  have haq : orderOf (quotientAut (center X) a) = 2 :=
    (orderOf_injective (quotientAut (center X)) MulAut.quotient_center_injective a).trans ha
  have hunique := prime_fixed_quotient_componentIn_unique (quotientAut (center X) a) haq hm
  have hnorm := source_invariant_normalizes_component t i htZ hKi X hKX a hact hB hunique
  let eK : K ≃* B := ((subgroupOfEquivOfLe hB.1).trans
    ((subgroupOfEquivOfLe hKX).trans (subgroupOfEquivOfLe hKi))).symm
  have hcard := source_prime_quotient_fixer_card_le_two c hG hempty hgen hb a ha B hB.2 eK hm
  have hRN : RI ≤ normalizer (X : Set Gi) := by rw [normalizer_eq_top]; exact le_top
  have htCK : t ∈ centralizer (K : Set G) := by
    intro k hk
    let x : X := ⟨⟨k,hKi hk⟩,hKX hk⟩
    have hxfix : a x = x := (MulAut.mem_fixedSubgroup a x).mp (hB.1 hk)
    have he := hact x
    rw [hxfix] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have htR : tI ∈ RI := ⟨⟨htZ.1,htCK⟩,htI⟩
  have hRt : RI ≤ centralizer ({tI} : Set Gi) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (htZ.2 r hr.1.1)
  have hRB : ∀ r ∈ RI, ∀ x : B,
      r * (((x : a.fixedSubgroup) : X) : Gi) = (((x : a.fixedSubgroup) : X) : Gi) * r := by
    intro r hr x
    apply Subtype.ext
    exact (hr.1.2 _ x.property).symm
  have hidx := MulAut.fixed_component_action_kernel_index_two X RI hRN tI htR a ha
    (fun x => Subtype.ext (hact x)) B hRt hRB hcard
  refine ⟨hnorm, ?_⟩
  have hRi : R ≤ Gi := inf_le_right
  have hdmap : (RI ⊓ centralizer (X : Set Gi)).map Gi.subtype =
      R ⊓ centralizer (X.map Gi.subtype : Set G) := by
    ext b
    constructor
    · rintro ⟨r,⟨hr,hc⟩,rfl⟩
      refine ⟨hr, ?_⟩
      rintro x ⟨y,hy,rfl⟩
      exact congrArg Subtype.val (hc y hy)
    · rintro ⟨hr,hc⟩
      refine ⟨⟨b,hRi hr⟩,⟨hr,?_⟩,rfl⟩
      intro x hx
      exact Subtype.ext (hc x (mem_map_of_mem Gi.subtype hx))
  have he := relIndex_map_map_of_injective
    (RI ⊓ centralizer (X : Set Gi)) RI Gi.subtype_injective
  rw [hdmap,map_subgroupOf_eq_of_le hRi] at he
  exact he.trans hidx
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
