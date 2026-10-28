module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.ExceptionalElimination
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Generation

/-!
# Conditional source assembly for Lemma 2.5.26

This proves m₂(S_C) = 1 from the earlier source setup, the actual alternatives
of 2.5.19, Φ(S_C) ≠ 1, tˣ = zK, and z = t zK. The last identity excludes
the first alternative of 2.5.19(4). The remaining A₈ alternative is eliminated
by the dihedral, TI-fusion, and C₂ × S₈ selection argument. Thus K is a
component of every involution centralizer C_G(i), i ∈ S_C, and its relative
normality follows from the quasithin obstruction to commuting A₆ copies.

For an involution i ≠ t, the two centralizers at tˣ and iˣ generate H and
normalize Kˣ. The source index |N_T(S):S| = 2 gives x² ∈ S, so conjugation
also makes Kˣ normalize K. These distinct components commute, producing
the genuine E₉ × A₄ local-rank obstruction. The Generation module then
converts uniqueness of the involution in S_C into primeRank 2 S_C = 1.

All five remaining finite-model inputs are enumerated in FiniteModelIdentities:
the quotient Sylow order, maximality of S in H, C_H(tˣ) = S, the outside
centralizer C_K(iˣ), and the order-four square identity. EarlierSelection
contains precisely the earlier Chapter 1 and 2 selection consequences.
The source assembly owner must supply these inputs, the alternatives, and
the earlier identities; this conditional theorem does not assert them.
In particular, it assumes neither universal component normality nor the
component claim, the two-conjugate conclusion, or rank one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed pp.568–569. Conjugation is
x a x⁻¹ throughout, as in the prerequisite modules. Components and normality
are relative to the displayed centralizers; the residual is the solvable
residual mapped into G.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne

/-- The earlier A₆ shadow setup, with Φ(S_C) ≠ 1 from 2.5.24. The component
at the single involution t is source 2.5.18; no component claim at other
involutions is included. The compatible action identifies H/S_C with Aut(A₆). -/
structure RankOneSetup (G : Type*) [Group G] where
  H : Subgroup G
  K : Subgroup G
  S : Subgroup G
  SC : Subgroup G
  t : G
  x : G
  centralizer_t : H = centralizer {t}
  generated : H = K ⊔ S
  modelK : K ≃* alternatingGroup (Fin 6)
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H).map H.subtype = S
  centralizer_K : SC = S ⊓ centralizer (K : Set G)
  core : SC = H.pCoreIn 2
  t_mem : t ∈ SC
  t_order : orderOf t = 2
  t_central : ∀ s : G, s ∈ S → s * t = t * s
  x_normalizes : x ∈ normalizer (S : Set G)
  disjoint_conjugate : Disjoint SC (SC.map (MulAut.conj x).toMonoidHom)
  frattini_ne : frattini SC ≠ ⊥
  component_t : Theory.GroupTheory.IsComponent (centralizer ({t} : Set G))
    (K.subgroupOf (centralizer {t}))
  action : H →* MulAut (alternatingGroup (Fin 6))
  action_surjective : Function.Surjective action
  action_compatible : ∀ (h : H) (k : K),
    (modelK.symm (action h (modelK k)) : G) = (h : G) * k * (h : G)⁻¹
  action_kernel : action.ker = SC.subgroupOf H

/-- The actual marked A₈ component in the second alternative of 2.5.19(4). -/
structure A8Alternative {G : Type*} [Group G] (d : RankOneSetup G) (i : G) where
  Ki : Subgroup G
  modelKi : Ki ≃* alternatingGroup (Fin 8)
  Ki_le_centralizer : Ki ≤ centralizer {i}
  component : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
    (Ki.subgroupOf (centralizer {i}))
  residual : d.K = (solvableResidual (Ki ⊓ centralizer ({d.t} : Set G) : Subgroup G)).map
    (Ki ⊓ centralizer ({d.t} : Set G)).subtype
  t_action : ∀ k : Ki,
    (modelKi.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (modelKi k)) : G) =
      d.t * k * d.t⁻¹

variable {G : Type*} [Group G]

/-- Precisely the finite Aut(A₆) identities used by this conditional route.
The square statement is confined to S and cyclic fours in S_C; it does not
postulate fusion, the order of T, or the rank of S_C. -/
structure FiniteModelIdentities (d : RankOneSetup G) (z : G) : Prop where
  quotient_order : (d.SC.subgroupOf d.S).index = 32
  sylow_maximal : IsCoatom (d.S.subgroupOf d.H)
  centralizer_conjugate_t : d.H ⊓ centralizer ({MulAut.conj d.x d.t} : Set G) = d.S
  outside_centralizer : ∀ i : G, i ∈ d.SC → orderOf i = 2 → i ≠ d.t →
    ¬ d.K ⊓ centralizer ({MulAut.conj d.x i} : Set G) ≤ d.S
  squares : ∀ (V : Subgroup G) (v : G), V ≤ d.SC → V = zpowers v →
    orderOf v = 4 → v ^ 2 = d.t →
    ∀ a : G, a ∈ d.S → a ∈ centralizer (V : Set G) → orderOf a = 4 →
      a ^ 2 ∈ zpowers d.t ⊔ zpowers z

/-- Applicable consequences of 2.5.19 in the A₆ setup (where K = K₀).
Part (2) is the exact centralizer identity. Part (4) retains the alternative
z = zK ∈ K with tz conjugate to t; in the other alternative, part (3)(II)
identifies K with the solvable residual and t acts as a transposition. -/
@[expose] def SourceAlternatives (d : RankOneSetup G) (z zK : G) : Prop :=
  ∀ (i : G) (hi : i ∈ d.SC), orderOf i = 2 →
    ¬ Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
      (d.K.subgroupOf (centralizer {i})) →
    centralizer ({(⟨i, hi⟩ : d.SC)} : Set d.SC) =
      zpowers (⟨i, hi⟩ : d.SC) ⊔ zpowers (⟨d.t, d.t_mem⟩ : d.SC) ∧
    ((z = zK ∧ z ∈ d.K ∧ ∃ g : G, MulAut.conj g d.t = d.t * z) ∨
      Nonempty (A8Alternative d i))

private def RankOneSetup.toLocalData (d : RankOneSetup G) (i : G) (hi : i ∈ d.SC)
    (hi2 : orderOf i = 2) (hit : i ≠ d.t)
    (hci : centralizer ({(⟨i, hi⟩ : d.SC)} : Set d.SC) =
      zpowers (⟨i, hi⟩ : d.SC) ⊔ zpowers (⟨d.t, d.t_mem⟩ : d.SC))
    (a : A8Alternative d i) : A8Reduction.LocalData G where
  H := d.H
  K := d.K
  S := d.S
  SC := d.SC
  Ki := a.Ki
  t := d.t
  i := i
  x := d.x
  centralizer_t := d.centralizer_t
  generated := d.generated
  modelK := d.modelK
  modelKi := a.modelKi
  sylow := d.sylow
  sylow_eq := d.sylow_eq
  centralizer_K := d.centralizer_K
  core := d.core
  t_mem := d.t_mem
  t_order := d.t_order
  t_central := d.t_central
  x_normalizes := d.x_normalizes
  disjoint_conjugate := d.disjoint_conjugate
  frattini_ne := d.frattini_ne
  i_mem := hi
  i_order := hi2
  i_ne_t := hit
  centralizer_i := hci
  Ki_le_centralizer := a.Ki_le_centralizer
  component := a.component
  residual := a.residual
  t_action := a.t_action
  action := d.action
  action_surjective := d.action_surjective
  action_compatible := d.action_compatible
  action_kernel := d.action_kernel

private theorem RankOneSetup.centralizer_in_sylow (d : RankOneSetup G) (T : Sylow 2 G) (hST : d.S ≤ T) :
    (T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.S := by
  have hle : (d.sylow : Subgroup d.H) ≤ (T : Subgroup G).subgroupOf d.H := by
    intro s hs
    exact hST (d.sylow_eq ▸ mem_map_of_mem d.H.subtype hs)
  have he := d.sylow.is_maximal' T.isPGroup'.comap_subtype hle
  have hm := congrArg (Subgroup.map d.H.subtype) he
  change ((T : Subgroup G).subgroupOf d.H).map d.H.subtype = _ at hm
  rw [subgroupOf_map_subtype, d.sylow_eq, d.centralizer_t] at hm
  exact hm

variable [Finite G]

/-- The component claim in the first part of 2.5.26, with relative normality.
The z = zK branch is excluded using z = t zK and t ≠ 1; the A₈ branch is
excluded by the actual symmetric extension and Chapter 2 selection. -/
theorem components_and_normalizers_of_source_alternatives (d : RankOneSetup G) (hG : IsQuasithin G)
    (T : Sylow 2 G) (M : Subgroup G) (z zK : G)
    (hST : d.S ≤ T) (hxT : d.x ∈ T) (hxS : d.x ∉ d.S)
    (hz : z = d.t * zK)
    (hmodel : FiniteModelIdentities d z)
    (h2519 : SourceAlternatives d z zK)
    (hfusion : ∀ g : G, MulAut.conj g d.t ∈ zpowers d.t ⊔ zpowers z →
      MulAut.conj g d.t = d.t ∨ MulAut.conj g d.t = MulAut.conj d.x d.t)
    (hselection : EarlierSelection M T)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅) :
    ∀ i : G, i ∈ d.SC → orderOf i = 2 →
      Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
        (d.K.subgroupOf (centralizer {i})) ∧
      centralizer ({i} : Set G) ≤ normalizer (d.K : Set G) := by
  have hzne : z ≠ zK := by
    intro he
    have ht1 : d.t = 1 := mul_right_cancel (show d.t * zK = 1 * zK by
      simpa only [one_mul] using hz.symm.trans he)
    have ho := d.t_order
    simp [ht1] at ho
  intro i hi hi2
  have hc : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
      (d.K.subgroupOf (centralizer {i})) := by
    by_contra hc
    have hit : i ≠ d.t := by
      intro he
      subst i
      exact hc d.component_t
    obtain ⟨hci, hcase⟩ := h2519 i hi hi2 hc
    rcases hcase with he | ha
    · exact hzne he.1
    · obtain ⟨a⟩ := ha
      exact exceptional_branch_impossible (d.toLocalData i hi hi2 hit hci a) hG T M z
        hmodel.quotient_order (d.centralizer_in_sylow T hST) hxT hxS hmodel.squares
        hfusion hselection hempty
  have hKi : d.K ≤ centralizer ({i} : Set G) := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    have hSC : d.SC ≤ centralizer (d.K : Set G) := d.centralizer_K ▸ inf_le_right
    exact hSC hi k hk
  have hn := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.subgroup (centralizer {i})) _ ((subgroupOfEquivOfLe hKi).trans d.modelK) hc
  exact ⟨hc, (normal_subgroupOf_iff_le_normalizer hKi).mp hn⟩

/-- Conditional Lemma 2.5.26, with every exceptional branch discharged.
The remaining hypotheses are enumerated earlier-source and finite-model
inputs. In particular, the component and normality claims are conclusions
of the preceding theorem, and x² ∈ S follows from the source normalizer index. -/
theorem primeRank_eq_one_of_source_alternatives (d : RankOneSetup G) (hG : IsQuasithin G)
    (T : Sylow 2 G) (M : Subgroup G) (z zK : G)
    (hST : d.S ≤ T) (hxT : d.x ∈ T) (hxS : d.x ∉ d.S)
    (hindex : d.S.relIndex ((T : Subgroup G) ⊓ normalizer (d.S : Set G)) = 2)
    (htx : MulAut.conj d.x d.t = zK) (hzK : zK ∈ d.K) (hz : z = d.t * zK)
    (hmodel : FiniteModelIdentities d z)
    (h2519 : SourceAlternatives d z zK)
    (hfusion : ∀ g : G, MulAut.conj g d.t ∈ zpowers d.t ⊔ zpowers z →
      MulAut.conj g d.t = d.t ∨ MulAut.conj g d.t = MulAut.conj d.x d.t)
    (hselection : EarlierSelection M T)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅) :
    primeRank 2 d.SC = 1 := by
  have hc := components_and_normalizers_of_source_alternatives d hG T M z zK hST hxT hxS hz hmodel h2519 hfusion
    hselection hempty
  have hx2 : d.x * d.x ∈ d.S := by
    let N := (T : Subgroup G) ⊓ normalizer (d.S : Set G)
    exact (d.S.subgroupOf N).mul_self_mem_of_index_two hindex
      (⟨d.x, hxT, d.x_normalizes⟩ : N)
  exact primeRank_eq_one_of_component_centralizers hG d.K d.H d.S d.SC d.t d.x
    d.modelK (d.generated ▸ le_sup_left) (d.generated ▸ le_sup_right) d.centralizer_t
    (d.centralizer_K ▸ inf_le_right) (d.core ▸ isPGroup_pCoreIn 2 d.H)
    d.t_mem d.t_order (fun i hi hi2 => (hc i hi hi2).1)
    hmodel.sylow_maximal hmodel.centralizer_conjugate_t hmodel.outside_centralizer
    (htx ▸ hzK) hx2

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
