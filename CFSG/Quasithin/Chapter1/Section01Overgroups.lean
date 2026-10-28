module

public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.PGroup.NormalChain

/-!
# Even-characteristic overgroups: Lemma 1.1.4

This module completes Aschbacher–Smith 1.1.4(1),(3),(5), and re-exports
the proved clauses (2),(4),(6),(7) through the inheritance and Sylow
extensions. The only even-characteristic input is condition (E) at the
specified Sylow subgroup; quasithinness and classification are not needed.

For (1), first suppose U is normal in V. Characteristic two passes from
N_G(U) to N_{N_G(U)}(V). This intersection contains the centralizer of
O₂(N_G(V)), so the core-centralizer overgroup criterion makes N_G(V)
characteristic two. A genuine subnormal chain in the finite two-group V
then gives the general case. For (3), Z(T) ∩ U is normal in T, so (2)
and (1) apply. For (5), condition (E) gives M ∈ He and (4) applies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 1.1.4, printed pp.500–501 (PDF pp.517–518).
-/

public section

namespace CFSG.Quasithin.Chapter1
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem mem_S2e_of_normal_step {U V : Subgroup G} (hU : U ∈ S2e G)
    (hV : IsPGroup 2 V) (hUV : U ≤ V) (hVN : V ≤ normalizer (U : Set G)) :
    V ∈ S2e G := by
  let N := normalizer (U : Set G)
  let L := normalizer (V : Set G)
  let K := N ⊓ L
  have hK : K ∈ He G := normalizer_mem_He_of_isPGroup hU.2.2 hV hVN
  have hcore : V ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes hV V.le_normalizer le_rfl
  refine ⟨fun he => hU.1 (bot_unique (he ▸ hUV)), hV, mem_He_iff.mpr ?_⟩
  apply centralizer_pCore_le_of_overgroup 2 (K.subgroupOf L)
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show K ≤ L from inf_le_right))).mpr (mem_He_iff.mp hK)
  · intro x hx
    have hxC : (x : G) ∈ centralizer (L.pCoreIn 2 : Set G) := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
    exact ⟨centralizer_le_normalizer (U : Set G)
      (centralizer_le hUV (centralizer_le hcore hxC)), x.property⟩

/-- 1.1.4(1): S₂e is upward closed among two-subgroups.
The larger subgroup is automatically nontrivial because it contains U. -/
theorem lemma_1_1_4_1 {U V : Subgroup G} (hU : U ∈ S2e G)
    (hUV : U ≤ V) (hV : IsPGroup 2 V) : V ∈ S2e G := by
  have hchain := hV.subgroup_isSubnormal (U.subgroupOf V)
  have lift : ∀ W : Subgroup V, W.IsSubnormal →
      W.map V.subtype ∈ S2e G → V ∈ S2e G := by
    intro W hW
    induction hW with
    | top =>
      intro ht
      simpa only [← MonoidHom.range_eq_map, range_subtype] using ht
    | step A B hAB _ hn ih =>
      intro hA
      apply ih
      apply mem_S2e_of_normal_step hA (hV.to_subgroup B |>.map V.subtype) (map_mono hAB)
      exact (map_mono ((normal_subgroupOf_iff_le_normalizer hAB).mp hn)).trans
        (le_normalizer_map V.subtype)
  exact lift _ hchain (by simpa only [map_subgroupOf_eq_of_le hUV] using hU)

/-- 1.1.4(3): a nontrivial intersection with the center of T puts a
nontrivial two-subgroup U in S₂e. The intersection is taken in G. -/
theorem lemma_1_1_4_3 (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {U : Subgroup G} (_hU : U ≠ ⊥) (hUp : IsPGroup 2 U)
    (hne : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ U ≠ ⊥) :
    U ∈ S2e G := by
  let Z := (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ U
  have hZT : Z ≤ (T : Subgroup G) := inf_le_left.trans (map_subtype_le _)
  have hTnorm : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht z hz
    have hcomm : t * z = z * t := by
      obtain ⟨a, ha, he⟩ := mem_map.mp hz.1
      exact he ▸ congrArg Subtype.val (mem_center_iff.mp ha ⟨t, ht⟩)
    simpa only [← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one] using hz
  exact lemma_1_1_4_1 (lemma_1_1_4_2 T hE hne hZT
    ((normal_subgroupOf_iff_le_normalizer hZT).mpr hTnorm)) inf_le_right hUp

/-- 1.1.4(5): the core-centralizer criterion for a maximal two-local
containing T. There is no normality assumption on N in M. -/
theorem lemma_1_1_4_5 (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {M N : Subgroup G} (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hN : N ≠ ⊥) (hNM : N ≤ M)
    (hR : M.pCoreIn 2 ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N) : N ∈ He G :=
  lemma_1_1_4_4 hN hNM (mem_He_iff.mpr (hE M hM hTM)) hR

end CFSG.Quasithin.Chapter1
