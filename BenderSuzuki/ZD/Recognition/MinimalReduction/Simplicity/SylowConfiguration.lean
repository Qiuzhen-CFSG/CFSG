module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import BenderSuzuki.SE.StrongEmbeddingConjugacy
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.PGroup.Omega

/-!
# The Sylow configuration for the ZD simplicity argument

A distinguished involution `z` centralizes an ambient Sylow two-subgroup `S`.
Product disconnection puts `S` inside `M`. An even normal subgroup omitting
`z` supplies an involution in a different ambient conjugacy class, so `M`
cannot be strongly embedded. Fusion control then forces an involution of
`S` whose full centralizer escapes `M`.

The normal subgroup also meets `S` nontrivially: conjugate one of its
involutions into `S`, retaining membership by normality. The resulting
nontrivial normal subgroup of `S` contains a central involution. This
involution differs from `z`, so the first omega subgroup of the Sylow center
cannot be cyclic. No odd-core or Lemma 4.10 conclusion is assumed.

Source: GLS, Volume 4, Chapter 2, Proposition 4.3, final paragraph;
`refs/KGroup/GLS4/Chapter2.tex`, lines 711–719. The supplied single-class
hypothesis is retained in the interface but is not needed for this step.
-/

open scoped Pointwise
namespace BenderSuzuki.ZD
open PFAppendixIII PFchapter1section1 Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem conjugate_involution_into_sylow (S : Sylow 2 G)
    {x : G} (hx : IsInvolution x) : ∃ g : G, g * x * g⁻¹ ∈ S := by
  obtain ⟨P, hxP⟩ := (isPGroup_zpowers_of_involution hx).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  refine ⟨g, ?_⟩
  rw [← hg]
  change g * x * g⁻¹ ∈ (P : Subgroup G).map (MulAut.conj g).toMonoidHom
  exact Subgroup.mem_map_of_mem _ (hxP (Subgroup.mem_zpowers x))

private theorem conjugate_involution_into_sylow_in (M : Subgroup G)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    {x : G} (hxM : x ∈ M) (hx : IsInvolution x) :
    ∃ m : M, (m : G) * x * (m : G)⁻¹ ∈ S := by
  obtain ⟨m, hm⟩ := conjugate_involution_into_sylow (S.subtype hSM)
    (BenderSuzuki.IsInvolution.subtype hx hxM)
  exact ⟨m, hm⟩

private theorem stronglyEmbedded_of_fusion_and_centralizers
    (M : Subgroup G) (hproper : M ≠ ⊤)
    (S T : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hTM : (T : Subgroup G) ≤ M) (hf : ControlsFusionIn M (T : Subgroup G))
    (hne : ∃ x ∈ M, IsInvolution x)
    (hC : ∀ x ∈ S, IsInvolution x → Subgroup.centralizer ({x} : Set G) ≤ M) :
    BenderSuzuki.IsStronglyEmbedded M := by
  have hCM : ∀ x ∈ M, IsInvolution x → Subgroup.centralizer ({x} : Set G) ≤ M := by
    intro x hxM hx c hc
    obtain ⟨m, hm⟩ := conjugate_involution_into_sylow_in M S hSM hxM hx
    have hx' : IsInvolution ((m : G) * x * (m : G)⁻¹) :=
      BenderSuzuki.IsInvolution.map_of_injective hx (MulAut.conj (m : G)).toMonoidHom
        (MulAut.conj (m : G)).injective
    have hcm : (m : G) * c * (m : G)⁻¹ ∈ M := by
      apply hC _ hm hx'
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hc' := congrArg (MulAut.conj (m : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      simpa only [map_mul, MulAut.conj_apply] using hc'
    have := M.mul_mem (M.mul_mem (M.inv_mem m.property) hcm) m.property
    simpa [mul_assoc] using this
  refine ⟨hproper, hne, ?_⟩
  intro g hg x hxM hxg hx
  have hyM : g * x * g⁻¹ ∈ M := by
    have hh := rightConjugateElem_mem_of_mem_rightConjugate
      (g := g⁻¹) (by simpa only [inv_inv] using hxg)
    simpa only [rightConjugateElem, inv_inv] using hh
  have hy : IsInvolution (g * x * g⁻¹) :=
    BenderSuzuki.IsInvolution.map_of_injective hx (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  obtain ⟨a, ha⟩ := conjugate_involution_into_sylow_in M T hTM hxM hx
  obtain ⟨b, hb⟩ := conjugate_involution_into_sylow_in M T hTM hyM hy
  have hconj : IsConj ((a : G) * x * (a : G)⁻¹)
      ((b : G) * (g * x * g⁻¹) * (b : G)⁻¹) := by
    apply isConj_iff.mpr
    refine ⟨(b : G) * g * (a : G)⁻¹, ?_⟩
    group
  obtain ⟨e, he⟩ := hf.exists_conjugator ha hb hconj
  let c : G := (b : G)⁻¹ * (e : G) * (a : G)
  have hcM : c ∈ M := M.mul_mem (M.mul_mem (M.inv_mem b.property) e.property) a.property
  have hcx : c * x * c⁻¹ = g * x * g⁻¹ := by
    calc
      c * x * c⁻¹ = (b : G)⁻¹ *
          ((e : G) * ((a : G) * x * (a : G)⁻¹) * (e : G)⁻¹) * (b : G) := by
            dsimp [c]; group
      _ = g * x * g⁻¹ := by rw [he]; group
  have hcg : c⁻¹ * g ∈ M := by
    apply hCM x hxM hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (c⁻¹ * g) * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
      _ = x := by rw [← hcx]; group
  apply hg
  simpa only [mul_inv_cancel_left] using M.mul_mem hcM hcg

private theorem noncyclic_omega_center_of_even_normal
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal] (hNe : Even (Nat.card N))
    {z : G} (hz : IsInvolution z) (hzS : z ∈ S)
    (hzc : ∀ s : S, Commute z (s : G)) (hzN : z ∉ N) :
    ¬ IsCyclic (omega₁ (Subgroup.center S) (p := 2)) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hNe.two_dvd
  have hwI : IsInvolution (w : G) := by
    have hwG : orderOf (w : G) = 2 := by simpa using hw
    exact ⟨fun he => by simp [he] at hwG, by simpa [hwG] using pow_orderOf_eq_one (w : G)⟩
  obtain ⟨g, hg⟩ := conjugate_involution_into_sylow S hwI
  let K := N.subgroupOf (S : Subgroup G)
  have hKN : g * (w : G) * g⁻¹ ∈ N :=
    (inferInstance : N.Normal).conj_mem w w.property g
  have hKnt : Nontrivial K := by
    apply (Subgroup.nontrivial_iff_ne_bot K).mpr
    intro he
    have hh : (⟨g * (w : G) * g⁻¹, hg⟩ : S) ∈ K := hKN
    rw [he, Subgroup.mem_bot] at hh
    have hh' : g * (w : G) * g⁻¹ = 1 := congrArg Subtype.val hh
    apply hwI.ne_one
    have := congrArg (MulAut.conj g).symm hh'
    simpa [MulAut.conj_symm_apply, mul_assoc] using this
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨C, _, hCK, hCcard, hCZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) K hKnt
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hCcard])
  let zC : Subgroup.center S := ⟨⟨z, hzS⟩, by
    apply Subgroup.mem_center_iff.mpr
    intro s
    exact Subtype.ext (hzc s).eq.symm⟩
  let vC : Subgroup.center S := ⟨v, hCZ v.property⟩
  have hzC : orderOf zC = 2 := by
    simpa only [zC, Subgroup.orderOf_mk] using
      (orderOf_eq_prime hz.sq_eq_one hz.ne_one : orderOf z = 2)
  have hvC : orderOf vC = 2 := by
    simpa only [vC, Subgroup.orderOf_mk, Subgroup.orderOf_coe] using hv
  have memOmega (a : Subgroup.center S) (ha : orderOf a = 2) :
      a ∈ omega₁ (Subgroup.center S) (p := 2) := by
    apply Subgroup.subset_closure
    simpa only [Set.mem_ofPred_eq, pow_one, ha] using pow_orderOf_eq_one a
  intro hcyc
  let := hcyc
  have he := IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨zC, memOmega zC hzC⟩ : omega₁ (Subgroup.center S) (p := 2)))
    (y := (⟨vC, memOmega vC hvC⟩ : omega₁ (Subgroup.center S) (p := 2)))
    (by simpa only [Subgroup.orderOf_mk] using hzC)
    (by simpa only [Subgroup.orderOf_mk] using hvC)
  have heG : z = ((v : S) : G) :=
    congrArg (fun a : omega₁ (Subgroup.center S) (p := 2) => (((a : Subgroup.center S) : S) : G)) he
  apply hzN
  rw [heG]
  exact hCK v.property

/-- The Sylow and escaping-centralizer configuration in the final paragraph
of GLS Proposition 4.3. The normal subgroup is an actual subgroup of `G`. -/
public theorem exists_sylow_configuration_of_even_normal
    {Z : Set G} {M : Subgroup G} (h : IsProductDisconnected Z M)
    (_hone : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (htwo : ∀ z ∈ Z, ∃ S : Sylow 2 G,
      z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hf : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ M ∧
      ControlsFusionIn M (T : Subgroup G))
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M)
    (N : Subgroup G) [N.Normal] (hNe : Even (Nat.card N)) (hzN : z ∉ N) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ z ∈ S ∧
      (∀ s : S, Commute z (s : G)) ∧
      ¬ IsCyclic (omega₁ (Subgroup.center S) (p := 2)) ∧
      ∃ u : G, u ∈ S ∧ IsInvolution u ∧
        ¬ Subgroup.centralizer ({u} : Set G) ≤ M := by
  obtain ⟨S, hzS, hzc⟩ := htwo z hzZ
  have hSM : (S : Subgroup G) ≤ M := fun s hs =>
    mem_of_commute h hzZ hzM (hzc ⟨s, hs⟩)
  have hz := h.involutions z hzZ
  have hnot : ¬ BenderSuzuki.IsStronglyEmbedded M := by
    intro hstrong
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hNe.two_dvd
    have hwG : orderOf (w : G) = 2 := by simpa using hw
    have hwI : IsInvolution (w : G) :=
      ⟨fun he => by simp [he] at hwG, by simpa [hwG] using pow_orderOf_eq_one (w : G)⟩
    obtain ⟨g, hg⟩ := hstrong.involutions_conjugate hwI hz
    apply hzN
    rw [← hg]
    simpa only [rightConjugateElem, inv_inv] using
      (inferInstance : N.Normal).conj_mem w w.property g⁻¹
  refine ⟨S, hSM, hzS, hzc,
    noncyclic_omega_center_of_even_normal S N hNe hz hzS hzc hzN, ?_⟩
  by_contra! hnone
  obtain ⟨T, hTM, hTf⟩ := hf
  exact hnot (stronglyEmbedded_of_fusion_and_centralizers M h.proper S T hSM hTM hTf
    ⟨z, hzM, hz⟩ hnone)

end BenderSuzuki.ZD
