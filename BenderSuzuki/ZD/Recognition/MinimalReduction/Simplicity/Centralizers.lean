module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.Local
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.Obstruction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.OddLayer
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.Isolation

/-!
# The centralizer conclusions of GLS Lemma 4.10

The local reduction proves relative normality, local involution conjugacy,
and odd order of the intersection with the supplied normal subgroup.
The global obstruction proves triviality of the ambient odd core and rules
out a Sylow-central weakly closed distinguished involution by Z-star.

The normal odd-layer calculation gives centrality modulo the actual odd
core of H and forces that core outside M. If u were central in an ambient
Sylow subgroup, that subgroup would lie in H; Sylow isolation would then
produce the forbidden weakly closed distinguished involution.

All three source clauses are proved conditional on the actual even simple
normal subgroup supplied by Lemma 4.9 and on the preliminary local embedding
and solvable-normal-subgroup conclusions. No construction of that normal
subgroup is assumed as a theorem here. The proof only needs product
disconnection from the minimal-counterexample hypotheses; generation, global
conjugacy, two-centrality of Z, and fusion control are not additional inputs.
The final export has exactly the pair of conclusions used by the simplicity
contradiction, without importing that assembly module.

Source: GLS, Volume 4, Chapter 2, Lemma 4.10,
`refs/KGroup/GLS4/Chapter2.tex`, lines 692–708.
-/

namespace BenderSuzuki.ZD.Centralizers
open PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- GLS Lemma 4.10(a–c), conditional on the supplied normal subgroup from
Lemma 4.9. Clause (a) states centrality in the odd-core quotient of H;
clause (b) maps the intrinsic odd core into G. -/
public theorem centralizer_conclusions
    (h : IsProductDisconnected Z M)
    (hsol : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A = ⊥)
    (hlocal : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ z ∈ Z, z ∈ H ∧ z ∈ M) →
      IsStronglyEmbedded
        ((M.comap H.subtype).comap (Subgroup.closure (H.subtype ⁻¹' Z)).subtype))
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hNeven : Even (Nat.card N)) {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hgen : N ⊔ Subgroup.zpowers z = ⊤) (hzN : z ∉ N)
    {u : G} (hu : PFAppendixIII.IsInvolution u) (huz : Commute u z)
    (huM : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    let H := Subgroup.centralizer ({u} : Set G)
    let zH : H := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq⟩
    QuotientGroup.mk' (pPrimeCore 2 H) zH ∈ Subgroup.center (H ⧸ pPrimeCore 2 H) ∧
      (¬ (pPrimeCore 2 H).map H.subtype ≤ M) ∧
      ¬ ∃ T : Sylow 2 G, u ∈ (T : Subgroup G) ∧
        ∀ t : T, Commute u (t : G) := by
  let H := Subgroup.centralizer ({u} : Set G)
  let L := Subgroup.closure (H.subtype ⁻¹' Z)
  have hzH : z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq
  obtain ⟨_, hnormal, _, hodd⟩ :=
    centralizer_local_structure h hsol hlocal N hz hzM hzN hu huz huM
  let : L.Normal := hnormal
  obtain ⟨hcentral, hcover⟩ := normal_odd_layer_central_and_cover H N
    (h.involutions z hz) hzH hzN hgen L (Subgroup.subset_closure hz) hodd
  refine ⟨hcentral, oddCore_not_le_of_local_cover h H huM hz hzH hzM hcover, ?_⟩
  rintro ⟨U, _, huC⟩
  have hUH : (U : Subgroup G) ≤ H := by
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr (huC ⟨t, ht⟩).symm.eq
  obtain ⟨T, _, hzT, hzC, hweak⟩ :=
    exists_weaklyClosed_sylow_of_odd_local_intersection h.invariant h.involutions
      N hz hzN hgen H hzH ⟨U, hUH⟩ hodd
  exact not_weaklyClosed_of_simple_normal_extension hsol N hNeven
    (h.involutions z hz) hgen hzN T hzT hzC hweak

/-- The pair of Lemma 4.10(b,c) conclusions in the form consumed by
`false_of_centralizer_oddCore_configuration`. The preliminary and normal
subgroup premises are supplied by the parent minimal-counterexample reduction. -/
public theorem centralizer_oddCore_configuration
    (h : MinimalCounterexample Z M)
    (hsol : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A = ⊥)
    (hlocal : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ z ∈ Z, z ∈ H ∧ z ∈ M) →
      IsStronglyEmbedded
        ((M.comap H.subtype).comap (Subgroup.closure (H.subtype ⁻¹' Z)).subtype))
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hNeven : Even (Nat.card N)) {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hgen : N ⊔ Subgroup.zpowers z = ⊤) (hzN : z ∉ N) :
    ∀ u : G, PFAppendixIII.IsInvolution u → Commute u z →
      ¬ Subgroup.centralizer ({u} : Set G) ≤ M →
      (¬ (pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype ≤ M) ∧
      ¬ ∃ T : Sylow 2 G, u ∈ (T : Subgroup G) ∧
        ∀ t : T, Commute u (t : G) := by
  intro u hu huz huM
  exact (centralizer_conclusions h.disconnected hsol hlocal N hNeven hz hzM
    hgen hzN hu huz huM).2

end BenderSuzuki.ZD.Centralizers
