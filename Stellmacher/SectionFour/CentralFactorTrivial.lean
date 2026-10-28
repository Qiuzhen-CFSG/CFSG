module
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Eliminating a central factor in a critical pair

Let `(P,Pstar)` be a Section Four critical pair, with `P` centralizing
`Ω₁(Z(S))`. Suppose `W ≤ S` is normalized by `S`, centralized by `L`,
and `Pstar ≤ L ⊔ S`. Then `W` is trivial. No elementary-abelian hypothesis
on `W` or containment `W ≤ L` is needed.

A nontrivial normal subgroup of the finite two-group `S` has a nontrivial
central element. Taking the appropriate power gives an involution `z` in
`W ∩ Ω₁(Z(S))`. Its cyclic subgroup `K` is centralized by `P` and `L`.
Since `S ≤ P`, the generation hypothesis makes `K` normal in `P ⊔ Pstar`.
But `K` is a two-subgroup, contradicting the defining trivial two-core of
the critical join.

This isolates the step `V₀ ∩ Z = 1`, hence `V₀ = 1`, in Stellmacher,
*An Application of the Amalgam Method: The 2-Local Structure of N-Groups
of Characteristic 2 Type*, (4.6), Journal of Algebra 190 (1997), p.26,
`refs/latex/stellmacher-n-group.tex`. The construction of `V₀` and the
normalization and centralization hypotheses belongs to the separate factor
argument; none of them is inferred here from a decomposition witness.
-/

namespace Stellmacher.SectionFour

/-- A factor normal in the Sylow subgroup and centralized by a supplement of
a critical partner is trivial when the other partner centralizes the Sylow's
central involutions. -/
public theorem critical_pair_central_factor_eq_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (P Pstar L W : Subgroup G)
    (hpair : (P, Pstar) ∈ Lambda S) (hPC : P ≤ cSubgroup S)
    (hWS : W ≤ (S : Subgroup G))
    (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    (hLW : L ≤ Subgroup.centralizer (W : Set G))
    (hgen : Pstar ≤ L ⊔ (S : Subgroup G)) : W = ⊥ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  by_contra hWne
  let WS := W.subgroupOf (S : Subgroup G)
  have hWSne : WS ≠ ⊥ := by
    intro hbot
    apply hWne
    rw [← Subgroup.map_subgroupOf_eq_of_le hWS]
    change WS.map (S : Subgroup G).subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  let _ : Nontrivial WS := (Subgroup.nontrivial_iff_ne_bot WS).mpr hWSne
  let _ : WS.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWS).mpr hSW
  obtain ⟨x, hxne, hxcenter⟩ := exists_nontrivial_center_mem_normal (p := 2) WS
  let z : WS := x ^ (orderOf x / 2)
  have hzorder : orderOf z = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne'
      ((S.isPGroup'.to_subgroup WS).dvd_orderOf hxne)
  obtain ⟨hzpow, hzne⟩ := (orderOf_eq_prime_iff).mp hzorder
  have hzcenter : (z : S) ∈ Subgroup.center S :=
    (Subgroup.center S).pow_mem hxcenter _
  have hzZ : ((z : S) : G) ∈ zSubgroup S := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(z : S).property, ?_, ?_⟩
    · exact congrArg (fun t : WS => ((t : S) : G)) hzpow
    · intro s hs
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨s, hs⟩)
  let K := Subgroup.zpowers ((z : S) : G)
  have hKZ : K ≤ zSubgroup S := Subgroup.zpowers_le.mpr hzZ
  have hKW : K ≤ W := Subgroup.zpowers_le.mpr z.property
  have hKS : K ≤ (S : Subgroup G) := hKW.trans hWS
  have hSP : (S : Subgroup G) ≤ P := by
    obtain ⟨T, hT⟩ := hpair.1.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hPK : P ≤ Subgroup.centralizer (K : Set G) :=
    hPC.trans (Subgroup.centralizer_le hKZ)
  have hLK : L ≤ Subgroup.centralizer (K : Set G) :=
    hLW.trans (Subgroup.centralizer_le hKW)
  have hjoin : P ⊔ Pstar ≤ Subgroup.normalizer (K : Set G) :=
    (sup_le hPK (hgen.trans (sup_le hLK (hSP.trans hPK)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKJ : K ≤ P ⊔ Pstar := hKS.trans (hSP.trans le_sup_left)
  have hKN : (K.subgroupOf (P ⊔ Pstar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hjoin
  have hKp : IsPGroup 2 (K.subgroupOf (P ⊔ Pstar)) :=
    (S.isPGroup'.to_le hKS).comap_of_injective (P ⊔ Pstar).subtype
      (P ⊔ Pstar).subtype_injective
  have hKcore : K ≤ twoCoreAmbient (P ⊔ Pstar) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKJ]
    exact Subgroup.map_mono (le_sSup ⟨hKN, hKp⟩)
  have hKbot : K = ⊥ := le_bot_iff.mp (hKcore.trans_eq hpair.2.2)
  have hzG : ((z : S) : G) = 1 :=
    Subgroup.mem_bot.mp (hKbot ▸ Subgroup.mem_zpowers ((z : S) : G))
  exact hzne (Subtype.ext (Subtype.ext hzG))

end Stellmacher.SectionFour
