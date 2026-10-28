module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual

/-!
# The quasisimple branch of internal-module residual structure

Let V be a normal elementary abelian two-subgroup of a finite group G,
and let q : G → H be onto with kernel C_G(V) and O₂(H) = 1. If G = LT
for a Sylow two-subgroup T and a C-component L with L/O₂(L) quasisimple
and [V,L] nontrivial, then C_G(V) has a normal Sylow two-subgroup and
q(L) = F*(H) is quasisimple. The actual Sylow-to-core application also
identifies O₂(G) with T ∩ C_G(V), retaining the embedded Sylow subgroup.

The literal factorization first forces the perfect C-component layer to
equal L: its quotient by L is both perfect and a two-group. Thus L is
normal. In G/O₂(G), the image of L is a normal quasisimple subgroup with
two-group quotient, hence is F*. The noncentral action excludes its
containment in the image of C_G(V). Component dichotomy and self-centralization
of F* make that latter image abelian, so it has no nontrivial two-subgroup.
Consequently every Sylow two-subgroup of C_G(V) lies in O₂(G).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.2.10(2), printed p.77, under B.2.1, printed p.74, combined manuscript
of 1 March 2004. This proves the C-component structural branch; the
order-three branch and relative-offender assembly have separate owners.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The literal two-group supplement forces a C-component to be normal. -/
theorem cComponent_normal_of_two_factorization
    (L S : Subgroup G) (hL : L.IsCComponent) (hS : IsPGroup 2 S)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ s ∈ S, l * s = g) : L.Normal := by
  let D := cComponentLayer G
  let : D.Characteristic := cComponentLayer_characteristic
  have hLD : L ≤ D := le_cComponentLayer hL
  let : (L.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (cComponentLayer_le_normalizer hL)
  have hsup : S.subgroupOf D ⊔ L.subgroupOf D = ⊤ := by
    apply top_unique
    intro d _
    obtain ⟨l, hl, s, hs, he⟩ := hprod d
    have hlD := hLD hl
    have hsD : s ∈ D := by
      have he' : s = l⁻¹ * (d : G) := by rw [← he]; simp
      rw [he']
      exact D.mul_mem (D.inv_mem hlD) d.property
    have hd : d = (⟨l, hlD⟩ : D) * ⟨s, hsD⟩ := Subtype.ext he.symm
    rw [hd]
    exact mul_mem (mem_sup_right hl) (mem_sup_left hs)
  have hp := quotient_isPGroup_of_sup_eq_top (S.subgroupOf D) (L.subgroupOf D)
    hS.comap_subtype hsup
  let : Group.IsNilpotent (D ⧸ L.subgroupOf D) := hp.isNilpotent
  let : Group.IsPerfect D := cComponentLayer_isPerfect
  have ht : L.subgroupOf D = ⊤ := top_le_iff.mp
    (le_of_isPerfect_of_solvable_quotient ⊤ (L.subgroupOf D))
  have he : L = D := le_antisymm hLD (subgroupOf_eq_top.mp ht)
  rw [he]
  infer_instance

omit [Finite G] in
private theorem two_subgroup_eq_bot_of_abelian_normal
    (hcore : pCore 2 G = ⊥) (N A : Subgroup G) [N.Normal]
    [IsMulCommutative N] (hA : IsPGroup 2 A) (hAN : A ≤ N) : A = ⊥ := by
  have hAcore : A.subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, hA.comap_subtype⟩
  have hcoreN : (pCore 2 N).map N.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map N.subtype⟩
  have hle := (map_mono (f := N.subtype) hAcore).trans hcoreN
  rw [map_subgroupOf_eq_of_le hAN, hcore] at hle
  exact le_bot_iff.mp hle

private theorem normalSylow_of_abelian_twoCore_image
    (C : Subgroup G) [C.Normal]
    [IsMulCommutative (C.map (QuotientGroup.mk' (pCore 2 G)))] :
    ∃ P : Sylow 2 C, (P : Subgroup C).Normal := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let r := QuotientGroup.mk' (pCore 2 G)
  let N := C.map r
  let : N.Normal := Normal.map inferInstance r (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 C := Classical.choice inferInstance
  let A := (P : Subgroup C).map (r.comp C.subtype)
  have hAN : A ≤ N := by
    change (P : Subgroup C).map (r.comp C.subtype) ≤ C.map r
    rw [← Subgroup.map_map]
    exact map_mono (map_subtype_le _)
  have hzero : A = ⊥ := two_subgroup_eq_bot_of_abelian_normal
    (pCore_quotient_pCore_eq_bot 2) N A (P.isPGroup'.map _) hAN
  have hP : (P : Subgroup C) ≤ (pCore 2 G).subgroupOf C := by
    have hk := (Subgroup.map_eq_bot_iff _).mp hzero
    intro x hx
    have hh : r (x : G) = 1 := hk hx
    exact (QuotientGroup.eq_one_iff (N := pCore 2 G) (x : G)).mp hh
  have he : (pCore 2 G).subgroupOf C = (P : Subgroup C) :=
    P.is_maximal' pCore_isPGroup.comap_subtype hP
  exact ⟨P, he ▸ inferInstance⟩

/-- The C-component branch of the internal-module structure theorem. -/
theorem internalModule_quasisimple_structure
    {H : Type*} [Group H] [Finite H]
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (L : Subgroup G) (hL : L.IsCComponent)
    (hquasi : IsQuasisimple (L ⧸ pCore 2 L))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    (∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal) ∧
    L.map q = generalizedFitting H ∧ IsQuasisimple (L.map q) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer (V : Set G)
  let : L.Normal := cComponent_normal_of_two_factorization L T hL T.isPGroup' hprod
  have hsup : L ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l, hl, t, ht, rfl⟩ := hprod g
    exact mul_mem (mem_sup_left hl) (mem_sup_right ht)
  have hLC : ¬ L ≤ C := by
    intro h
    apply hcomm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr h
  have hQC : pCore 2 G ≤ C := by
    have hm : (pCore 2 G).map q ≤ pCore 2 H :=
      le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
    change pCore 2 G ≤ centralizer (V : Set G)
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (hm.trans hcore.le))
  let r := QuotientGroup.mk' (pCore 2 G)
  have hr : Function.Surjective r := QuotientGroup.mk'_surjective _
  let K := L.map r
  let N := C.map r
  let : K.Normal := Normal.map inferInstance r hr
  let : N.Normal := Normal.map inferInstance r hr
  let : IsQuasisimple (L ⧸ pCore 2 L) := hquasi
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)
  have hK : IsComponent (G ⧸ pCore 2 G) K :=
    ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  have hsupbar : K ⊔ (T : Subgroup G).map r = ⊤ := by
    rw [← Subgroup.map_sup, hsup, map_top_of_surjective r hr]
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ K) :=
    quotient_isPGroup_of_sup_eq_top _ K (T.isPGroup'.map r)
      (by simpa only [sup_comm] using hsupbar)
  have hF : generalizedFitting (G ⧸ pCore 2 G) = K :=
    generalizedFitting_eq_of_quasisimple_two_quotient K hquot
      (pCore_quotient_pCore_eq_bot 2)
  have hKN : ¬ K ≤ N := by
    intro h
    apply hLC
    have hh := map_le_iff_le_comap.mp h
    simpa only [N, r, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQC] using hh
  have hc : ⁅K, N⁆ = ⊥ := (hK.normal_dichotomy N).resolve_left hKN
  have hNC : N ≤ centralizer (K : Set (G ⧸ pCore 2 G)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hNK : N ≤ K := hNC.trans (by
    rw [← hF]
    exact centralizer_generalizedFitting_le _)
  let : IsMulCommutative N := le_centralizer_iff_isMulCommutative.mp
    (hNC.trans (centralizer_le hNK))
  have hsyl := normalSylow_of_abelian_twoCore_image C
  have hQker : pCore 2 G ≤ q.ker := hker.symm ▸ hQC
  let f := QuotientGroup.lift (pCore 2 G) q hQker
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ q hq _
  have hKimage : K.map f = L.map q := by
    rw [Subgroup.map_map, QuotientGroup.lift_comp_mk']
  have hLimage : L.map q ≠ ⊥ := by
    intro hb
    apply hLC
    simpa only [hker] using (Subgroup.map_eq_bot_iff _).mp hb
  have hqK : IsQuasisimple (L.map q) := by
    rcases hK.map_surjective f hf with hz | hi
    · exact (hLimage (hKimage.symm.trans hz)).elim
    · rw [hKimage] at hi
      exact hi.2
  let : IsQuasisimple (L.map q) := hqK
  let : (L.map q).Normal := Normal.map inferInstance q hq
  have hquotH : IsPGroup 2 (H ⧸ L.map q) :=
    quotient_isPGroup_of_sup_eq_top ((T : Subgroup G).map q) (L.map q)
      (T.isPGroup'.map q) (by
        rw [← Subgroup.map_sup, sup_comm, hsup, map_top_of_surjective q hq])
  exact ⟨hsyl, (generalizedFitting_eq_of_quasisimple_two_quotient
    (L.map q) hquotH hcore).symm, hqK⟩

/-- Applying the Sylow-to-core theorem to the actual centralizer and map
also gives the two-core intersection and the exact embedded Sylow subgroup. -/
theorem internalModule_quasisimple_core_structure
    {H : Type*} [Group H] [Finite H]
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (L : Subgroup G) (hL : L.IsCComponent)
    (hquasi : IsQuasisimple (L ⧸ pCore 2 L))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    pCore 2 G = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    (∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal ∧
      (P : Subgroup (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = pCore 2 G) ∧
    L.map q = generalizedFitting H ∧ IsQuasisimple (L.map q) := by
  obtain ⟨hsyl, hF, hquasiImage⟩ :=
    internalModule_quasisimple_structure V q hq hker hcore T L hL hquasi hcomm hprod
  obtain ⟨hcoreG, hP⟩ := normalSylow_structure_of_coreFree_image q hq hcore
    (centralizer (V : Set G)) hker T hsyl
  exact ⟨hcoreG, hP, hF, hquasiImage⟩

end Theory.GroupTheory
