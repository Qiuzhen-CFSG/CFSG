module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo.Coordinates
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The two-factor quotient of a nonnormal linear-two component orbit

Let L₀ be the span of the S-conjugates of the selected C-component L.
The index-two component normalizer makes L₀ the join of L and one moving
conjugate. Restrict these C-components to L₀ and pass to L₀/O₂(L₀).
Subnormal core transport identifies their images with their intrinsic
quotients, hence with the supplied projective SL₂ model. Perfectness and
the PSL₂ Iwasawa criterion give simplicity. The two images remain distinct
through the solvable quotient, so they commute and meet trivially; their
join is the whole quotient. Multiplication gives the actual product
isomorphism.

Normality of L₀ in I makes S ∩ L₀ Sylow in L₀. Conjugate the product
coordinates so its image is the pair of standard upper-unipotent Sylow
subgroups. The kernel O₂(L₀) lies in every Sylow two-subgroup, which proves
the full root-preimage equality in `LinearTwo.Coordinates`.

Only the explicit universal `EarlierOrbitResults` input and the actual
component model are used. No Borel, parity, rank, orbit-product or alignment
certificate is assumed. In particular the field-degree bound need not be
used again: the given component already supplies perfectness.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(1), printed p.1130 (PDF p.1147). The two-conjugate and multiplication
arguments adapt the checked Chapter 1 development in
`Section03/Embeddings/Swapped/Factors/Orbit.lean`; here the simple-subnormal
commutation theorem discharges commutation directly.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup OddBorel EvenBorelResidual
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel

private def productSylow {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (P : Sylow 2 A) (Q : Sylow 2 B) : Sylow 2 (A × B) where
  toSubgroup := (P : Subgroup A).prod Q
  isPGroup' := by
    obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := Q.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup A) (Q : Subgroup B)).toEquiv,
      Nat.card_prod, ha, hb, pow_add]
  is_maximal' := by
    intro U hU hPQ
    apply le_antisymm _ hPQ
    apply Subgroup.le_prod_iff.mpr
    constructor
    · exact le_of_eq (P.is_maximal' (hU.map (MonoidHom.fst A B)) (by
        intro x hx
        exact ⟨(x, 1), hPQ ⟨hx, Q.one_mem⟩, rfl⟩))
    · exact le_of_eq (Q.is_maximal' (hU.map (MonoidHom.snd A B)) (by
        intro x hx
        exact ⟨(1, x), hPQ ⟨P.one_mem, hx⟩, rfl⟩))

variable {G : Type*} [Group G] [Finite G]

/-- Sylow conjugacy aligns an actual product quotient with a specified Sylow intersection. -/
theorem linearTwo_coordinates_of_quotient {L S : Subgroup G}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hS : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (f : L →* (PSL(2,F) × PSL(2,F))) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 L) : Nonempty (LinearTwo.Coordinates L S F) := by
  obtain ⟨P, hP⟩ := hS
  have hPS : (P : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    simpa only [subgroupOf_map_subtype] using hP
  let Q := P.mapSurjective hf
  let U := productSylow (standardSylow F) (standardSylow F)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL(2,F) × PSL(2,F)) Q U
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  have hmap : (P : Subgroup L).map f' = (kernel F).prod (kernel F) := by
    change (P : Subgroup L).map (a.toMonoidHom.comp f) = _
    rw [← Subgroup.map_map]
    have he := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup L).map f).map a.toMonoidHom =
      (standardSylow F : Subgroup PSL(2,F)).prod (standardSylow F) at he
    simpa only [coe_standardSylow] using he
  have hk' : f'.ker = pCore 2 L := by
    exact (MonoidHom.ker_comp_of_injective f a.toMonoidHom a.injective).trans hk
  refine ⟨⟨f', a.surjective.comp hf, hk', ?_⟩⟩
  rw [← hmap, comap_map_eq_self, hPS]
  rw [hk']
  exact pCore_isPGroup.le_sylow_of_normal P

omit [Finite G] in
private theorem orbit_eq_two_conjugates (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    {t : G} (ht : t ∈ d.S) (htN : t ∉ normalizer (c.L : Set G)) :
    localSpan c.L d.S = c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom := by
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  let N := (normalizer (c.L : Set G)).subgroupOf I
  have hconj (s : G) (hs : s ∈ d.S) :
      c.L.map (MulAut.conj s).toMonoidHom = c.L ∨
      c.L.map (MulAut.conj s).toMonoidHom = c.L.map (MulAut.conj t).toMonoidHom := by
    by_cases hsN : s ∈ normalizer (c.L : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hsN)
    · have he : t⁻¹ * s ∈ normalizer (c.L : Set G) := by
        have ht' : (⟨t, hSI ht⟩ : I)⁻¹ ∉ N := by
          simpa only [inv_mem_iff] using
            (show (⟨t, hSI ht⟩ : I) ∉ N from htN)
        exact (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false ht'
          (show (⟨s, hSI hs⟩ : I) ∉ N from hsN))
      have heq : c.L.map (MulAut.conj (t⁻¹ * s)).toMonoidHom = c.L :=
        mem_normalizer_iff_map_conj_eq.mp he
      right
      calc
        c.L.map (MulAut.conj s).toMonoidHom =
            (c.L.map (MulAut.conj (t⁻¹ * s)).toMonoidHom).map
              (MulAut.conj t).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        _ = _ := by rw [heq]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨s, hs, l, hl, rfl⟩
    have hm : s * l * s⁻¹ ∈ c.L.map (MulAut.conj s).toMonoidHom :=
      mem_map.mpr ⟨l, hl, rfl⟩
    rcases hconj s hs with he | he
    · exact (show c.L ≤ c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom from le_sup_left) (he ▸ hm)
    · exact (show c.L.map (MulAut.conj t).toMonoidHom ≤
          c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom from le_sup_right) (he ▸ hm)
  · refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro x ⟨l, hl, rfl⟩
    exact subset_closure ⟨t, ht, l, hl, rfl⟩

omit [Finite G] in
private theorem conjugate_component {I L : Subgroup G} (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent) {t : G} (ht : t ∈ I) :
    (L.map (MulAut.conj t).toMonoidHom).subgroupOf I |>.IsCComponent := by
  have hle : L.map (MulAut.conj t).toMonoidHom ≤ I := by
    rintro x ⟨l, hl, rfl⟩
    exact I.mul_mem (I.mul_mem ht (hLI hl)) (I.inv_mem ht)
  have hc := hL.map_equiv (MulAut.conj (⟨t, ht⟩ : I))
  have he : (L.subgroupOf I).map (MulAut.conj (⟨t, ht⟩ : I)).toMonoidHom =
      (L.map (MulAut.conj t).toMonoidHom).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, map_map]
    change (L.subgroupOf I).map ((MulAut.conj t).toMonoidHom.comp I.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hLI]
  exact he ▸ hc

private theorem disjoint_of_simple_commuting {X : Type*} [Group X] (A B : Subgroup X)
    [IsSimpleGroup A] [Group.IsPerfect A] (hc : ⁅A, B⁆ = ⊥) : Disjoint A B := by
  have hz : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp hz)).elim
  apply disjoint_def.mpr
  intro x hx hy
  have hcenter : (⟨x, hx⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
  rw [hz] at hcenter
  exact congrArg Subtype.val (mem_bot.mp hcenter)

/-- The nonnormal orbit has two actual commuting simple quotient factors. -/
theorem linearTwo_orbit_quotient {K : GroupClass} (earlier : EarlierOrbitResults K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (hn : ¬ (c.L.subgroupOf I).Normal) (hS : Chapter1.IsSylowIn 2 d.S I)
    {F : Type*} [Field F]
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(2,F)) :
    Nonempty ((localSpan c.L d.S ⧸ pCore 2 (localSpan c.L d.S)) ≃*
      (PSL(2,F) × PSL(2,F))) := by
  let L₀ := localSpan c.L d.S
  have hi := (component_orbit_index_and_model earlier hG d hI c hn).1
  have hL₀I : L₀ ≤ I := (orbit_normal_and_le d c hS hi).1
  have hLI : c.L ≤ I := component_le c
  have hLL₀ : c.L ≤ L₀ := le_conjugateSpanBy _ _
  have hc := LocalData.thompson_component_in c.le_thompson c.component
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  obtain ⟨t, ht, htN⟩ : ∃ t ∈ d.S, t ∉ normalizer (c.L : Set G) := by
    by_contra! h
    exact (component_moved_by_sylow d c hS hi).not_ge (conjugateSpanBy_le le_rfl h)
  let C := c.L.map (MulAut.conj t).toMonoidHom
  have hCL₀ : C ≤ L₀ := by
    rintro x ⟨l, hl, rfl⟩
    exact subset_closure ⟨t, ht, l, hl, rfl⟩
  have hgen : L₀ = c.L ⊔ C := orbit_eq_two_conjugates d c hS hi ht htN
  let A := c.L.subgroupOf L₀
  let B := C.subgroupOf L₀
  have hA : A.IsCComponent := hc.subgroupOf_of_le hLL₀ hL₀I
  have hB : B.IsCComponent :=
    (conjugate_component hLI hc (hSI ht)).subgroupOf_of_le hCL₀ hL₀I
  let q := QuotientGroup.mk' (pCore 2 L₀)
  let Abar := A.map q
  let Bbar := B.map q
  let _ := pCore_isNilpotent (p := 2) (G := L₀)
  have hAbar : Abar.IsCComponent := hA.map_quotient _
  have hBbar : Bbar.IsCComponent := hB.map_quotient _
  let a₀ : A ≃* c.L := subgroupOfEquivOfLe hLL₀
  let a : Abar ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hA).symm.trans
    ((QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)).trans e)
  let ct : c.L ≃* C := equivMapOfInjective c.L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let b₀ : B ≃* c.L := (subgroupOfEquivOfLe hCL₀).trans ct.symm
  let b : Bbar ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hB).symm.trans
    ((QuotientGroup.congr _ _ b₀ (pCore_map_iso 2 b₀)).trans e)
  let _ := hAbar.perfect
  let _ := hBbar.perfect
  let _ : Group.IsPerfect PSL(2,F) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let _ : IsSimpleGroup PSL(2,F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  let _ : IsSimpleGroup Abar := a.isSimpleGroup
  let _ : IsSimpleGroup Bbar := b.isSimpleGroup
  have hne : Abar ≠ Bbar := by
    intro he
    have heq := hA.eq_of_map_quotient_eq hB (pCore 2 L₀) he
    have hh := congrArg (fun D : Subgroup L₀ => D.map L₀.subtype) heq
    rw [map_subgroupOf_eq_of_le hLL₀, map_subgroupOf_eq_of_le hCL₀] at hh
    exact htN (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hcomm : ⁅Abar, Bbar⁆ = ⊥ :=
    simple_subnormal_commute_of_ne Abar Bbar hAbar.subnormal hBbar.subnormal hne
  have hdisj := disjoint_of_simple_commuting Abar Bbar hcomm
  obtain ⟨m, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting Abar Bbar hdisj
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have htop : Abar ⊔ Bbar = ⊤ := by
    change A.map q ⊔ B.map q = ⊤
    rw [← Subgroup.map_sup]
    have he : A ⊔ B = ⊤ := by
      change c.L.subgroupOf L₀ ⊔ C.subgroupOf L₀ = ⊤
      rw [← subgroupOf_sup hLL₀ hCL₀, ← hgen, subgroupOf_self]
    rw [he]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let m' := m.trans ((MulEquiv.subgroupCongr htop).trans topEquiv)
  exact ⟨m'.symm.trans (a.prodCongr b)⟩

/-- The actual two-component quotient can be marked at the supplied Sylow
subgroup, giving all four fields required by the linear-two Borel argument. -/
theorem linearTwo_orbit_coordinates {K : GroupClass} (earlier : EarlierOrbitResults K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (hn : ¬ (c.L.subgroupOf I).Normal) (hS : Chapter1.IsSylowIn 2 d.S I)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(2,F)) :
    Nonempty (LinearTwo.Coordinates (localSpan c.L d.S) d.S F) := by
  let L₀ := localSpan c.L d.S
  obtain ⟨a⟩ := linearTwo_orbit_quotient earlier hG d hI c hn hS e
  let q := QuotientGroup.mk' (pCore 2 L₀)
  let f := a.toMonoidHom.comp q
  have hi := (component_orbit_index_and_model earlier hG d hI c hn).1
  obtain ⟨hle, hnormal⟩ := orbit_normal_and_le d c hS hi
  have hSL₀ : Chapter1.IsSylowIn 2 (d.S ⊓ L₀) L₀ :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hle hnormal.isSubnormal
  apply linearTwo_coordinates_of_quotient hSL₀ f (a.surjective.comp (QuotientGroup.mk'_surjective _))
  exact (MonoidHom.ker_comp_of_injective q a.toMonoidHom a.injective).trans
    (QuotientGroup.ker_mk' _)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
