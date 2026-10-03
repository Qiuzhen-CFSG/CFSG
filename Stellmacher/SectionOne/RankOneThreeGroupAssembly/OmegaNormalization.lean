module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting

/-!
# Normalization and characters of the ambient omega factors

The local omega cover generates the odd core. A factor distinct from every local generator would fix its own faithful module, so every factor is normalized by the Sylow subgroup and has a binary action character.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The inclusion consequence of `exists_local_generic_omega_family`. -/
public theorem local_commutator_le_oneOmegaGenerated_of_generic
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2)
    (hgeneric : RankOneLocalGenericHypothesis
      (G := G) (V := V) S A) :
    ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ≤
      oneOmegaGenerated (G := G) (V := V) := by
  obtain ⟨d⟩ := exists_local_generic_omega_family S A hlocal hAmax hAcard hgeneric
  rw [d.generated]
  refine iSup_le ?_
  intro i
  exact le_iSup
    (fun F : {F : Subgroup G //
      F ∈ oneOmegaFinset (G := G) (V := V)} => (F : Subgroup G))
    ⟨d.factor i, (mem_oneOmegaFinset_iff (G := G) (V := V) _).mpr
      (d.omega i)⟩

/-- In the generic branch every ambient `oneOmega` factor is normalized by
`S`.  The locally lifted normalized factors generate the odd core; coordinate
uniqueness for the full omega decomposition then identifies any ambient
factor with one of those lifts. -/
public theorem all_oneOmega_normalized_generic
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hlocal : RankOneAssemblyLocalHypothesis
      (G := G) (V := V) (S : Subgroup G))
    (hgeneric : RankOneAssemblyGenericHypothesis
      (G := G) (V := V) (S : Subgroup G)) :
    ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      (S : Subgroup G) ≤ Subgroup.normalizer F := by
  classical
  have hlocalLe : ∀ A : Subgroup G,
      oneAmax (G := G) (V := V) (S : Subgroup G) A →
      Nat.card A = 2 →
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ ≤
          oneOmegaGenerated (G := G) (V := V) := by
    intro A hAmax hAcard
    exact local_commutator_le_oneOmegaGenerated_of_generic
      (S : Subgroup G) A hlocal hAmax hAcard (hgeneric A hAmax hAcard)
  have hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V) :=
    oddCore_eq_oneOmegaGenerated_of_local_commutators
      h S hS_elem hScard hW hlocalLe
  have hdecomp := oneOmegaGenerated_decomposition h S hWthree
  let IA := {A : Subgroup G //
    oneAmax (G := G) (V := V) (S : Subgroup G) A ∧ Nat.card A = 2}
  let WA : IA → Subgroup G := fun A =>
    ⁅oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G),
      (S : Subgroup G)⁆
  have hd_exists (A : IA) : Nonempty
      (LocalGenericOmegaFamily (G := G) (V := V) (WA A) (S : Subgroup G)) := by
    exact exists_local_generic_omega_family (S : Subgroup G) (A : Subgroup G)
      hlocal A.property.1 A.property.2
      (hgeneric (A : Subgroup G) A.property.1 A.property.2)
  let d (A : IA) : LocalGenericOmegaFamily
      (G := G) (V := V) (WA A) (S : Subgroup G) :=
    Classical.choice (hd_exists A)
  let K : (Σ A : IA, (d A).index) → Subgroup G := fun i =>
    (d i.1).factor i.2
  have hgenWA : oddCore G = ⨆ A : IA, WA A := by
    simpa only [IA, WA] using
      oddCore_eq_iSup_local_commutators_of_oneOmega_decomposition
        h S hS_elem hScard hW hcoreEq hdecomp
  have hgenK : oddCore G = ⨆ i, K i := by
    calc
      oddCore G = ⨆ A : IA, WA A := hgenWA
      _ = ⨆ A : IA, ⨆ i, (d A).factor i := by
        congr 1
        funext A
        exact (d A).generated
      _ = ⨆ i : Σ A : IA, (d A).index, K i := by
        exact iSup_sigma' (f := fun A i => (d A).factor i)
  intro F hFomega
  obtain ⟨i, hi⟩ := oneOmega_eq_member_of_iSup_eq_oddCore
    hdecomp K (fun i => (d i.1).omega i.2) hgenK F hFomega
  rw [hi]
  exact (d i.1).normalized i.2

public theorem mul_ne_one_iff_exclusive_of_natCard_eq_two
    {Q : Type*} [Group Q] (hcard : Nat.card Q = 2) (a b : Q) :
    a * b ≠ 1 ↔ (a ≠ 1 ∧ b = 1) ∨ (a = 1 ∧ b ≠ 1) := by
  obtain ⟨z, hz, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hcard
  by_cases ha : a = 1 <;> by_cases hb : b = 1
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · have hab : a = b := (hzuniq a ha).trans (hzuniq b hb).symm
    have haa : a * a = 1 := by
      simpa [hcard, pow_two] using (pow_card_eq_one' (x := a))
    have hbb : b * b = 1 := by rw [← hab]; exact haa
    have habone : a * b = 1 := by rw [hab]; exact hbb
    constructor
    · intro hne
      exact (hne habone).elim
    · rintro (h | h)
      · exact (hb h.2).elim
      · exact (ha h.1).elim

@[expose] public def omegaFactorCharacter
    {G : Type u} [Group G] (S F : Subgroup G)
    (hSF : S ≤ Subgroup.normalizer F) : S →* MulAut F :=
  F.normalizerMonoidHom.comp (Subgroup.inclusion hSF)

public theorem oneOmega_mulAut_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F) :
    Nat.card (MulAut F) = 2 := by
  let hprime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (Nat.Prime 3) := hprime
  let hcyc : IsCyclic F := isCyclic_of_prime_card hF.2.1
  let _ : IsCyclic F := hcyc
  rw [IsCyclic.card_mulAut, hF.2.1, Nat.totient_prime Nat.prime_three]

/-- Under `W = [W,S]`, every complete omega coordinate is acted on
nontrivially by `S`; since it has prime order, its commutator with `S` is the
whole coordinate.  This is the projection-free form of the source's use of
the direct product `W = F₁ × ⋯ × Fᵣ`. -/
public theorem commutator_oneOmega_sylow_eq_self
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F) :
    ⁅F, S⁆ = F := by
  classical
  have hcommLeF : ⁅F, S⁆ ≤ F :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hnorm F hF)
  let C : Subgroup F := ⁅F, S⁆.subgroupOf F
  let hprime : Fact (Nat.card F).Prime := ⟨hF.2.1 ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card F).Prime := hprime
  rcases C.eq_bot_or_eq_top_of_prime_card with hCbot | hCtop
  · have hcommBot : ⁅F, S⁆ = ⊥ := by
      calc
        ⁅F, S⁆ = C.map F.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hcommLeF).symm
        _ = ⊥ := by rw [hCbot, Subgroup.map_bot]
    let W : Subgroup G := oddCore G
    let H : Subgroup G := W ⊔ S
    let Ω := {K : Subgroup G // K ∈ oneOmegaFinset (G := G) (V := V)}
    let Other := {K : Ω // (K : Subgroup G) ≠ F}
    let KH (K : Ω) : Subgroup H := (K : Subgroup G).subgroupOf H
    let OH (K : Other) : Subgroup H := (K : Subgroup G).subgroupOf H
    let N : Subgroup H := ⨆ K : Other, OH K
    let SH : Subgroup H := S.subgroupOf H
    have hKomega (K : Ω) : oneOmega (G := G) (V := V) (K : Subgroup G) :=
      (mem_oneOmegaFinset_iff (G := G) (V := V) (K : Subgroup G)).mp K.property
    have hKleW (K : Ω) : (K : Subgroup G) ≤ W := (hKomega K).1
    have hKleH (K : Ω) : (K : Subgroup G) ≤ H :=
      (hKleW K).trans le_sup_left
    have hWcomm : IsMulCommutative W := by
      change IsMulCommutative (oddCore G)
      rw [hcoreEq]
      exact oneOmegaGenerated_isMulCommutative hdecomp
    have hKHnormal (K : Ω) : (KH K).Normal := by
      have hWnorm : W ≤ Subgroup.normalizer (K : Subgroup G) :=
        ((Subgroup.le_centralizer_iff).mpr
          ((hKleW K).trans
            (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWcomm))).trans
          (Subgroup.centralizer_le_normalizer ((K : Subgroup G) : Set G))
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hKleH K)).2
        (sup_le hWnorm (hnorm (K : Subgroup G) (hKomega K)))
    have hOHnormal (K : Other) : (OH K).Normal := hKHnormal K
    have hNnormal : N.Normal := by
      dsimp only [N]
      simpa using Subgroup.biSup_normal Set.univ OH
        (fun K _ => hOHnormal K)
    let _ : N.Normal := hNnormal
    have hgenW : W = ⨆ K : Ω, (K : Subgroup G) := by
      calc
        W = oneOmegaGenerated (G := G) (V := V) := hcoreEq
        _ = ⨆ K : Ω, (K : Subgroup G) := hdecomp.part_a.1
    have hgenWH : W.subgroupOf H = ⨆ K : Ω, KH K := by
      apply Subgroup.map_injective H.subtype_injective
      calc
        (W.subgroupOf H).map H.subtype = W :=
          Subgroup.map_subgroupOf_eq_of_le le_sup_left
        _ = ⨆ K : Ω, (K : Subgroup G) := hgenW
        _ = ⨆ K : Ω, (KH K).map H.subtype := by
          congr 1
          funext K
          exact (Subgroup.map_subgroupOf_eq_of_le (hKleH K)).symm
        _ = (⨆ K : Ω, KH K).map H.subtype := by rw [Subgroup.map_iSup]
    have hlocalComm (K : Ω) : ⁅KH K, SH⁆ ≤ N := by
      by_cases hKF : (K : Subgroup G) = F
      · have hsubBot : ⁅KH K, SH⁆ = ⊥ := by
          apply Subgroup.map_injective H.subtype_injective
          rw [commutator_subgroupOf_map_eq (S := H) (H := S)
            (R := (K : Subgroup G)) le_sup_right (hKleH K), hKF,
            hcommBot, Subgroup.map_bot]
        rw [hsubBot]
        exact bot_le
      · let hnormalK : (KH K).Normal := hKHnormal K
        let _ : (KH K).Normal := hnormalK
        exact (Subgroup.commutator_le_left (KH K) SH).trans
          (le_iSup OH ⟨K, hKF⟩)
    have hcommLeN : ⁅W.subgroupOf H, SH⁆ ≤ N :=
      commutator_le_normal_of_eq_iSup
        (W.subgroupOf H) SH N KH hgenWH hlocalComm
    have hWsubEq : W.subgroupOf H = ⁅W.subgroupOf H, SH⁆ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [commutator_subgroupOf_map_eq (S := H) (H := S) (R := W)
        le_sup_right le_sup_left,
        Subgroup.map_subgroupOf_eq_of_le le_sup_left]
      exact hW
    have hFsubLeN : F.subgroupOf H ≤ N := by
      have hFsubLeW : F.subgroupOf H ≤ W.subgroupOf H := fun x hx => hF.1 hx
      rw [hWsubEq] at hFsubLeW
      exact hFsubLeW.trans hcommLeN
    have hNmap : N.map H.subtype =
        ⨆ K : Other, (K : Subgroup G) := by
      calc
        N.map H.subtype = ⨆ K : Other, (OH K).map H.subtype := by
          dsimp only [N]
          rw [Subgroup.map_iSup]
        _ = ⨆ K : Other, (K : Subgroup G) := by
          congr 1
          funext K
          exact Subgroup.map_subgroupOf_eq_of_le (hKleH K)
    have hFleOther : F ≤ ⨆ K : Other, (K : Subgroup G) := by
      calc
        F = (F.subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hF.1.trans le_sup_left)).symm
        _ ≤ N.map H.subtype := Subgroup.map_mono hFsubLeN
        _ = ⨆ K : Other, (K : Subgroup G) := hNmap
    have hdisj : Disjoint F (⨆ K : Other, (K : Subgroup G)) :=
      oneOmega_disjoint_iSup_of_distinct hdecomp F hF
        (fun K : Other => (K : Subgroup G))
        (fun K => hKomega K)
        (fun K => K.property)
    have hFbot : F = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact Subgroup.disjoint_def.mp hdisj hx (hFleOther hx)
    have := hF.2.1
    rw [hFbot] at this
    norm_num at this
  · calc
      ⁅F, S⁆ = C.map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hcommLeF).symm
      _ = F := by rw [hCtop, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
