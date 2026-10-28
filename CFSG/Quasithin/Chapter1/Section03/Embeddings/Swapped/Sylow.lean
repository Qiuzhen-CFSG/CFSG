module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# Sylow input and quotient transport for the swapped case

The unrestricted intrinsic embedding statement is false. `SwappedSylowInput`
retains the published intrinsic input and adds the genuine hypothesis that T
is Sylow two in H. The original source and its local applications supply this
hypothesis. No simplicity of H is assumed.

Intersecting the Sylow subgroup with the relatively normal component orbit K
and passing to K/O₂(K) gives the Sylow subgroup needed by the Borel argument.
The complement embeds in this quotient, and its join with the Sylow image is
solvable. Since O₂(K) lies in T, normalization of the Sylow image lifts back to
normalization of T ∩ K. Coprimality then makes N_(T∩K)(P) centralize P.

The final theorem here obtains the four initial models and the index-two
normalizer from the exact universal A.3.8 input. The conjugate direct product,
concrete Borel normalizers, and outer-action comparison remain separate proof
obligations; this module does not assert the completed embedding alternative.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 1.3.4, printed pp.509–510; Proposition
1.2.1(3), p.504. The sufficient Sylow hypothesis is also present in the local
applications on pp.874, 1052 and 1163–1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The separately named sufficient local input; the original intrinsic record is unchanged. -/
structure SwappedSylowInput (𝒦 : GroupClass.{u}) (p : ℕ) (T X P H L : Subgroup G)
    extends SwappedInput 𝒦 p T X P H L where
  sylow_two : IsSylowIn 2 T H

namespace SwappedSylow
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

/-- The orbit lies in the given overgroup, where its normality is assumed. -/
theorem orbit_le_overgroup (h : SwappedInput 𝒦 p T X P H L) :
    componentOrbit L T ≤ H :=
  (componentOrbit_le_sup L T).trans
    (sup_le h.component.1 (le_sup_right.trans h.overgroup))

/-- The actual intersection T ∩ K is Sylow two in the relatively normal orbit K. -/
theorem orbit_sylow [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    IsSylowIn 2 (T ⊓ componentOrbit L T) (componentOrbit L T) := by
  let _ := h.orbit_normal
  exact Section02.IndexTwo.isSylowIn_inf_of_subnormal h.sylow_two
    (orbit_le_overgroup h.toSwappedInput) h.orbit_normal.isSubnormal

/-- Subnormality also restricts the Sylow subgroup to the chosen C-component. -/
theorem component_sylow [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    IsSylowIn 2 (T ⊓ L) L :=
  Section02.IndexTwo.isSylowIn_inf_of_subnormal h.sylow_two h.component.1 h.component.2.subnormal

/-- The normal two-core of H is contained in its specified Sylow subgroup. -/
theorem core_le_two [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) : H.pCoreIn 2 ≤ T := by
  obtain ⟨S, hS⟩ := h.sylow_two
  exact hS ▸ pCoreIn_le_sylow H S

/-- The intrinsic two-core of the orbit lies in its Sylow intersection. -/
theorem orbit_core_le_two [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    (componentOrbit L T).pCoreIn 2 ≤ T ⊓ componentOrbit L T := by
  obtain ⟨S, hS⟩ := orbit_sylow h
  exact hS ▸ pCoreIn_le_sylow _ S

/-- The actual image of an ambient subgroup in K/O₂(K), for K = ⟨L^T⟩. -/
def imageInOrbit (L T A : Subgroup G) : Subgroup (XiQuotient (componentOrbit L T)) :=
  (A.subgroupOf (componentOrbit L T)).map (QuotientGroup.mk' (pCore 2 (componentOrbit L T)))

/-- The quotient image of T ∩ K is an actual Sylow two-subgroup of K/O₂(K). -/
theorem orbit_quotient_sylow [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    ∃ S : Sylow 2 (XiQuotient (componentOrbit L T)),
      (S : Subgroup _) = imageInOrbit L T T := by
  obtain ⟨S, hS⟩ := orbit_sylow h
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective]
  congr 1
  have hs := congrArg (fun A => A.subgroupOf (componentOrbit L T)) hS
  change ((S : Subgroup _).map (componentOrbit L T).subtype).comap
    (componentOrbit L T).subtype = _ at hs
  simpa only [comap_map_eq_self_of_injective (componentOrbit L T).subtype_injective,
    inf_subgroupOf_right] using hs

/-- The Sylow hypothesis justifies the intersection identity in H/O₂(H). -/
theorem quotient_inf [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    ((T ⊓ componentOrbit L T).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
      (T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
      ((componentOrbit L T).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) := by
  change ((T.subgroupOf H) ⊓ ((componentOrbit L T).subgroupOf H)).map _ = _
  rw [inf_comm (T.subgroupOf H), inf_comm ((T.subgroupOf H).map _)]
  apply map_inf_of_ker_le
  rw [QuotientGroup.ker_mk']
  intro x hx
  exact core_le_two h (mem_map_of_mem H.subtype hx)

/-- In H/O₂(H), the intersection of the two images is Sylow in the orbit image. -/
theorem ambient_quotient_sylow [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    IsSylowIn 2
      ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
        ((componentOrbit L T).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
      (((componentOrbit L T).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
  have hKH := orbit_le_overgroup h.toSwappedInput
  have hrel : IsSylowIn 2 ((T ⊓ componentOrbit L T).subgroupOf H)
      ((componentOrbit L T).subgroupOf H) :=
    (IsSylowIn.map_iff H.subtype H.subtype_injective).mp (by
      simpa only [map_subgroupOf_eq_of_le hKH,
        map_subgroupOf_eq_of_le (inf_le_right.trans hKH)] using orbit_sylow h)
  have him := Section02.IndexTwo.isSylowIn_map hrel (QuotientGroup.mk' (pCore 2 H))
  rwa [quotient_inf h] at him

/-- The odd complement and the two-group have trivial intersection. -/
theorem complement_disjoint_two (h : LocalInput p T X P H) : Disjoint P T := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  exact h.odd_complement.isPGroup.disjoint_of_coprime h.two_group
    (Nat.coprime_two_right.mpr h.odd)

/-- The complement and T generate exactly XT, because O₂(X) lies in T. -/
theorem complement_two_sup (h : LocalInput p T X P H) : P ⊔ T = X ⊔ T := by
  apply le_antisymm (sup_le_sup_right h.complement_le T)
  exact sup_le (h.complement ▸ sup_le
    (h.core_le_two_group.trans le_sup_right) le_sup_left) le_sup_right

/-- The source product PT is the whole subgroup XT, without assuming T normalizes P. -/
theorem complement_two_product (h : LocalInput p T X P H) :
    ((X ⊔ T : Subgroup G) : Set G) = (P : Set G) * T := by
  have hPQ : P ≤ normalizer (X.pCoreIn 2) := h.complement_le.trans
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hX : (X : Set G) = (P : Set G) * X.pCoreIn 2 := by
    rw [← coe_mul_of_left_le_normalizer_right P _ hPQ, sup_comm, h.complement]
  rw [coe_mul_of_right_le_normalizer_left X T h.invariant, hX, mul_assoc]
  congr 1
  apply Set.Subset.antisymm
  · exact Subgroup.mul_subset h.core_le_two_group (le_refl _)
  · intro t ht
    exact ⟨1, one_mem _, t, ht, one_mul _⟩

/-- Taking inverses gives the reverse product TP = XT as well. -/
theorem two_complement_product (h : LocalInput p T X P H) :
    ((X ⊔ T : Subgroup G) : Set G) = (T : Set G) * P := by
  apply Set.Subset.antisymm
  · intro g hg
    have hgi : g⁻¹ ∈ X ⊔ T := inv_mem hg
    change g⁻¹ ∈ ((X ⊔ T : Subgroup G) : Set G) at hgi
    rw [complement_two_product h] at hgi
    obtain ⟨a, ha, t, ht, he⟩ := hgi
    refine ⟨t⁻¹, inv_mem ht, a⁻¹, inv_mem ha, ?_⟩
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he
  · exact Subgroup.mul_subset (show T ≤ X ⊔ T from le_sup_right)
      (h.complement_le.trans le_sup_left)

/-- Dedekind intersection gives the actual product P(T ∩ K) = XT ∩ K. -/
theorem complement_orbit_product (h : SwappedInput 𝒦 p T X P H L) :
    (((X ⊔ T) ⊓ componentOrbit L T : Subgroup G) : Set G) =
      (P : Set G) * (T ⊓ componentOrbit L T) := by
  rw [coe_inf, complement_two_product h.toLocalInput,
    mul_inf_assoc P T _ h.complement_le_orbit]

/-- The subgroup generated by P and T ∩ K is XT ∩ K. -/
theorem complement_orbit_sup (h : SwappedInput 𝒦 p T X P H L) :
    P ⊔ (T ⊓ componentOrbit L T) = (X ⊔ T) ⊓ componentOrbit L T := by
  rw [sup_eq_closure_mul, ← complement_orbit_product h, closure_eq]

/-- The local product XT is solvable, by its normal solvable subgroup X and two-group supplement. -/
theorem local_solvable [Finite G] (h : LocalInput p T X P H) :
    Group.IsSolvable (X ⊔ T : Subgroup G) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  let _ := h.quotient.isPGroup.isNilpotent
  let _ : Group.IsSolvable X :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr ⟨inferInstance, inferInstance⟩
  let _ := h.two_group.isNilpotent
  let A := X.subgroupOf (X ⊔ T)
  let B := T.subgroupOf (X ⊔ T)
  let _ : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer h.invariant)
  let _ : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show X ≤ X ⊔ T from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show X ≤ X ⊔ T from le_sup_left)).injective
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ X ⊔ T from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ X ⊔ T from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  apply map_injective (X ⊔ T).subtype_injective
  simp only [A, B, Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]


/-- The odd complement embeds in the orbit quotient via the actual quotient map. -/
noncomputable def quotientComplementEquiv (h : SwappedInput 𝒦 p T X P H L) :
    P ≃* imageInOrbit L T P := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let K := componentOrbit L T
  let R := P.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hd : Disjoint (pCore 2 K) R :=
    pCore_isPGroup.disjoint_of_coprime h.odd_complement.isPGroup.comap_subtype
      (Nat.coprime_two_left.mpr h.odd)
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc : (a : K) ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val ha)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  exact (subgroupOfEquivOfLe h.complement_le_orbit).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap R) ⟨hi, q.subgroupMap_surjective R⟩)

/-- The quotient image retains the elementary or extraspecial alternative. -/
theorem quotient_complement_odd (h : SwappedInput 𝒦 p T X P H L) :
    XiOddQuotient p (imageInOrbit L T P) :=
  h.odd_complement.of_mulEquiv (quotientComplementEquiv h)

/-- The quotient image of the complement is still noncyclic. -/
theorem quotient_complement_not_cyclic [Finite G] (h : SwappedInput 𝒦 p T X P H L) :
    ¬ IsCyclic (imageInOrbit L T P) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  exact (quotient_complement_odd h).not_isCyclic

/-- The subgroup generated by the two quotient images is solvable. -/
theorem quotient_solvable [Finite G] (h : SwappedInput 𝒦 p T X P H L) :
    Group.IsSolvable (imageInOrbit L T P ⊔ imageInOrbit L T T : Subgroup _) := by
  let _ := local_solvable h.toLocalInput
  let K := componentOrbit L T
  let A := (P.subgroupOf K) ⊔ (T.subgroupOf K)
  let J : Subgroup G := X ⊔ T
  have hA : A ≤ J.subgroupOf K := sup_le
    (fun x hx => (show P ≤ J from h.complement_le.trans le_sup_left) hx)
    (fun x hx => (show T ≤ J from le_sup_right) hx)
  let f : A →* J := (K.subtype.subgroupComap J).comp (inclusion hA)
  let _ : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : J => (z : G)) he)
  let q := QuotientGroup.mk' (pCore 2 K)
  have he : imageInOrbit L T P ⊔ imageInOrbit L T T = A.map q :=
    (Subgroup.map_sup _ _ _).symm
  rw [he]
  exact Group.isSolvable_of_surjective (q.subgroupMap_surjective A)

/-- Containment of O₂(K) in T identifies the full preimage of the Sylow image. -/
theorem twoImage_preimage [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L) :
    (imageInOrbit L T T).comap (QuotientGroup.mk' (pCore 2 (componentOrbit L T))) =
      T.subgroupOf (componentOrbit L T) := by
  apply comap_map_eq_self
  rw [QuotientGroup.ker_mk']
  intro x hx
  exact (orbit_core_le_two h (mem_map_of_mem _ hx)).1

/-- A Borel normalization proved in K/O₂(K) lifts to normalization of T ∩ K. -/
theorem normalizes_two_of_quotient [Finite G] (h : SwappedSylowInput 𝒦 p T X P H L)
    (hn : imageInOrbit L T P ≤ normalizer (imageInOrbit L T T)) :
    P ≤ normalizer (T ⊓ componentOrbit L T) := by
  let K := componentOrbit L T
  let q := QuotientGroup.mk' (pCore 2 K)
  change P ≤ normalizer ((T ⊓ K : Subgroup G) : Set G)
  apply le_normalizer_iff.mpr
  intro a ha s hs
  have haK := h.complement_le_orbit ha
  let aK : K := ⟨a, haK⟩
  let sK : K := ⟨s, hs.2⟩
  have hc : q (aK * sK * aK⁻¹) ∈ imageInOrbit L T T := by
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hn (mem_map_of_mem q ha)) _).mp (mem_map_of_mem q hs.1)
  have ht : aK * sK * aK⁻¹ ∈ T.subgroupOf K := by
    rw [← twoImage_preimage h]
    exact hc
  exact ⟨ht, (aK * sK * aK⁻¹).property⟩

/-- Once P normalizes T ∩ K, its normalizer there centralizes P by coprimality. -/
theorem inner_normalizer_centralizes (h : SwappedInput 𝒦 p T X P H L)
    (hn : P ≤ normalizer (T ⊓ componentOrbit L T)) :
    (T ⊓ componentOrbit L T) ⊓ normalizer P ≤ centralizer (P : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  have hP : ⁅(T ⊓ componentOrbit L T) ⊓ normalizer P, P⁆ ≤ P :=
    le_normalizer_iff_commutator_le_right.mp inf_le_right
  have hT : ⁅(T ⊓ componentOrbit L T) ⊓ normalizer P, P⁆ ≤ T :=
    ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hn)).trans inf_le_left
  exact (le_inf hP hT).trans (complement_disjoint_two h.toLocalInput).le_bot

/-- The source Frattini commutator forces an actor outside K after Borel normalization. -/
theorem frattini_not_le_orbit [Finite G] (h : SwappedInput 𝒦 p T X P H L)
    (hn : P ≤ normalizer (T ⊓ componentOrbit L T)) :
    ¬ (frattini (T ⊓ normalizer P : Subgroup G)).map (T ⊓ normalizer P).subtype ≤
      componentOrbit L T := by
  intro hle
  have hc : (frattini (T ⊓ normalizer P : Subgroup G)).map (T ⊓ normalizer P).subtype ≤
      centralizer (P : Set G) := by
    apply le_trans ?_ (inner_normalizer_centralizes h hn)
    exact le_inf (le_inf ((map_subtype_le _).trans inf_le_left) hle)
      ((map_subtype_le _).trans inf_le_right)
  have he : P = ⊥ := h.frattini_commutator.trans (by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  apply h.complement_not_cyclic
  rw [he]
  infer_instance


/-- SQTK descends through the actual normal two-core; odd-prime rank uses coprime lifting. -/
theorem overgroup_quotient_sqtk [Finite G] (h : SwappedInput 𝒦 p T X P H L) :
    IsSQTK 𝒦 (XiQuotient H) := by
  refine ⟨?_, h.sqtk.isKGroup.quotient _⟩
  intro r hr ho
  let _ : Fact r.Prime := ⟨hr⟩
  exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
    (h.sqtk.stronglyQuasithin r hr ho)

/-- SQTK restricts to the orbit with its intrinsic group structure. -/
theorem orbit_sqtk [Finite G] (h : SwappedInput 𝒦 p T X P H L) :
    IsSQTK 𝒦 (componentOrbit L T) :=
  (IsSQTK.equiv (subgroupOfEquivOfLe (orbit_le_overgroup h))).mp
    (h.sqtk.subgroup _)

/-- The intrinsic orbit quotient is SQTK, as required for the earlier local results. -/
theorem orbit_quotient_sqtk [Finite G] (h : SwappedInput 𝒦 p T X P H L) :
    IsSQTK 𝒦 (XiQuotient (componentOrbit L T)) := by
  refine ⟨?_, (orbit_sqtk h).isKGroup.quotient _⟩
  intro r hr ho
  let _ : Fact r.Prime := ⟨hr⟩
  exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
    ((orbit_sqtk h).stronglyQuasithin r hr ho)

/-- The universal earlier A.3.8 theorem supplies index two and the four actual initial models. -/
theorem nonnormal_model_of_A_3_8 [Finite G]
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ B : Subgroup D, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set D)).index = 2 ∧ Section02.NonnormalCComponentModel B)
    (h : SwappedInput 𝒦 p T X P H L) :
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
      Section02.NonnormalCComponentModel (XiQuotient L) := by
  rcases Section02.proposition_1_2_1_three_index_of_A_3_8 hA38
    (overgroup_quotient_sqtk h) h.component.2 with hn | ⟨hi, hm⟩
  · exact (h.not_invariant ((le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer h.component.1).mp hn))).elim
  · let e := subgroupOfEquivOfLe h.component.1
    let eqv := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) e
      (pCore_map_iso 2 e)
    exact ⟨hi, hm.of_mulEquiv eqv.symm⟩

end SwappedSylow
end CFSG.Quasithin.Chapter1.XiEmbedding
