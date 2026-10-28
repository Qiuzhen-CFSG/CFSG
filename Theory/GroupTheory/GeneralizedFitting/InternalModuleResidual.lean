module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Internal-module residual structure

A subnormal subgroup's generalized Fitting subgroup embeds in the ambient
one. If the ambient two-core is trivial and its generalized Fitting subgroup
is quasisimple or has order three, every normal subgroup containing a
nontrivial two-subgroup has the same generalized Fitting subgroup. The
component dichotomy and generalized-Fitting self-centralization exclude the
centralizing case: it would make the normal subgroup abelian, forcing every
two-subgroup into the ambient two-core.

Separately, a normal Sylow two-subgroup of the kernel of a surjection to a
group with trivial two-core maps onto the original two-core. Intersecting any
ambient Sylow subgroup with that kernel therefore gives the two-core.

These are the normal-subgroup and Sylow deductions in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.2.10(2), printed p.77, under
Hypothesis B.2.1, printed p.74 (combined 1 March 2004 manuscript).
The quasisimple-or-three image identification remains a separate input.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Generalized Fitting subgroups increase along subnormal inclusions. -/
theorem generalizedFitting_map_subtype_le_of_isSubnormal
    (N : Subgroup G) (hN : N.IsSubnormal) :
    (generalizedFitting N).map N.subtype ≤ generalizedFitting G := by
  rw [generalizedFitting, Subgroup.map_sup]
  apply sup_le
  · exact (fittingSubgroup_map_subtype_le_of_isSubnormal N hN).trans
      (fitting_le_generalizedFitting G)
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro K hK
    let := hK.2
    apply map_le_iff_le_comap.mp
    exact component_le_generalizedFitting G _
      ⟨hK.1.trans' hN, IsQuasisimple.of_mulEquiv
        (K.equivMapOfInjective N.subtype N.subtype_injective)⟩

omit [Finite G] in
private theorem two_subgroup_eq_bot_of_commutative_normal
    (hcore : pCore 2 G = ⊥) (N A : Subgroup G) [N.Normal]
    [IsMulCommutative N] (hA : IsPGroup 2 A) (hAN : A ≤ N) : A = ⊥ := by
  have hAcore : A.subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, hA.comap_subtype⟩
  have hcoreN : (pCore 2 N).map N.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map N.subtype⟩
  have hle := (map_mono (f := N.subtype) hAcore).trans hcoreN
  rw [map_subgroupOf_eq_of_le hAN, hcore] at hle
  exact le_bot_iff.mp hle

omit [Finite G] in
private theorem normal_le_or_centralizes_simple
    (K N : Subgroup G) [K.Normal] [N.Normal] [IsSimpleGroup K] :
    K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hb | ht
  · right
    exact commutator_eq_bot_of_disjoint ((subgroupOf_eq_bot.mp hb).symm)
  · exact Or.inl (subgroupOf_eq_top.mp ht)

private theorem contains_generalizedFitting_of_two_subgroup
    (hcore : pCore 2 G = ⊥)
    (hshape : IsQuasisimple (generalizedFitting G) ∨ Nat.card (generalizedFitting G) = 3)
    (N A : Subgroup G) [N.Normal] (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hAN : A ≤ N) : generalizedFitting G ≤ N := by
  let K := generalizedFitting G
  have hd : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
    rcases hshape with hq | hc
    · let := hq
      exact (show IsComponent G K from
        ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩).normal_dichotomy N
    · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      let : IsSimpleGroup K := isSimpleGroup_of_prime_card hc
      exact normal_le_or_centralizes_simple K N
  rcases hd with hn | hc
  · exact hn
  · have hNC : N ≤ centralizer (K : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    have hNK : N ≤ K := hNC.trans (centralizer_generalizedFitting_le G)
    let : IsMulCommutative N := le_centralizer_iff_isMulCommutative.mp
      (hNC.trans (centralizer_le hNK))
    exact (hne (two_subgroup_eq_bot_of_commutative_normal hcore N A hA hAN)).elim

/-- A normal subgroup containing a nontrivial two-subgroup retains the
quasisimple or order-three generalized Fitting subgroup when the two-core
is trivial. No quotient or residual identification is assumed. -/
theorem generalizedFitting_normal_eq_of_quasisimple_or_three
    (hcore : pCore 2 G = ⊥)
    (hshape : IsQuasisimple (generalizedFitting G) ∨ Nat.card (generalizedFitting G) = 3)
    (N A : Subgroup G) [N.Normal] (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hAN : A ≤ N) : (generalizedFitting N).map N.subtype = generalizedFitting G := by
  have hKN := contains_generalizedFitting_of_two_subgroup hcore hshape N A hA hne hAN
  apply le_antisymm (generalizedFitting_map_subtype_le_of_isSubnormal N
    (inferInstance : N.Normal).isSubnormal)
  have hle : (generalizedFitting G).subgroupOf N ≤ generalizedFitting N := by
    rcases hshape with hq | hc
    · let := hq
      exact component_le_generalizedFitting N _
        ((show IsComponent G (generalizedFitting G) from
          ⟨(inferInstance : (generalizedFitting G).Normal).isSubnormal, inferInstance⟩).subgroupOf hKN)
    · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hp : IsPGroup 3 (generalizedFitting G) := IsPGroup.of_card (n := 1) (by simpa using hc)
      exact (show (generalizedFitting G).subgroupOf N ≤ fittingSubgroup N from
        le_sSup ⟨inferInstance, hp.comap_subtype.isNilpotent⟩).trans
          (fitting_le_generalizedFitting N)
  simpa only [map_subgroupOf_eq_of_le hKN] using map_mono (f := N.subtype) hle

/-- A normal Sylow subgroup of the kernel is precisely the ambient two-core
when the image has trivial two-core. The equality retains the actual map
and holds for every ambient Sylow two-subgroup. -/
theorem normalSylow_structure_of_coreFree_image
    {H : Type*} [Group H] (q : G →* H) (hq : Function.Surjective q)
    (hcore : pCore 2 H = ⊥) (C : Subgroup G) [C.Normal]
    (hC : q.ker = C) (T : Sylow 2 G)
    (hsyl : ∃ P : Sylow 2 C, (P : Subgroup C).Normal) :
    pCore 2 G = (T : Subgroup G) ⊓ C ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).Normal ∧
        (P : Subgroup C).map C.subtype = pCore 2 G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (pCore 2 G).map q ≤ pCore 2 H :=
    le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  have hker : pCore 2 G ≤ C := by
    rw [← hC]
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (hmap.trans hcore.le))
  obtain ⟨P, hn⟩ := hsyl
  let : (P : Subgroup C).Characteristic := P.characteristic_of_normal hn
  have hPc : (P : Subgroup C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, P.isPGroup'.map _⟩
  have hcP : pCore 2 G ≤ (P : Subgroup C).map C.subtype := by
    have hh := (pCore_isPGroup (p := 2) (G := G)).comap_subtype.le_sylow_of_normal P
    change (pCore 2 G).subgroupOf C ≤ (P : Subgroup C) at hh
    have hm := map_mono (f := C.subtype) hh
    simpa only [map_subgroupOf_eq_of_le hker] using hm
  have he := le_antisymm hPc hcP
  have hPT : (P : Subgroup C).map C.subtype ≤ (T : Subgroup G) :=
    hPc.trans (pCore_isPGroup.le_sylow_of_normal T)
  exact ⟨he.symm.trans (inf_eq_sylow_map P T.isPGroup' hPT).symm, P, hn, he⟩

end Theory.GroupTheory
