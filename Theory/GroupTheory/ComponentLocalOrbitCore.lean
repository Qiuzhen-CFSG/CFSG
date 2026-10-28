module

public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Prime cores in local component orbits

Let L be a component, K ≤ L, and A a p-subgroup whose stabilizer of L
normalizes K. Repeated conjugates of K coincide, and distinct conjugates
commute. The join of their p-cores is a p-subgroup normal in K ⊔ A.
A nontrivial seed core therefore gives a nontrivial core in this overgroup.

For a seed with self-centralizing p-core, a finite commuting-product
calculation bounds the centralizer in the orbit. The quotient of K ⊔ A
by the orbit is a p-group, so the centralizer bound extends to K ⊔ A.
Every p-perfect subgroup of the overgroup lies in the orbit. No hypothesis
that A normalizes L is used, nor is centerlessness of L needed here.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
2.3.9(7), printed p.526. These are general finite-group calculations;
construction of the source's local seed subgroups is separate.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A finite normalizing family of p-groups generates a p-group. -/
theorem isPGroup_iSup_of_normalizes {p : ℕ} {ι : Type*} [Finite ι]
    (Q : ι → Subgroup G) (hQ : ∀ i, IsPGroup p (Q i))
    (hn : ∀ i j, Q i ≤ normalizer (Q j : Set G)) :
    IsPGroup p (⨆ i, Q i : Subgroup G) := by
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) : IsPGroup p (s.sup Q : Subgroup G) := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      exact IsPGroup.of_bot
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact (hQ i).to_sup_of_normal_left' ih (Finset.sup_le fun j _ => hn j i)
  have ht := hs Finset.univ
  rwa [Finset.sup_univ_eq_iSup] at ht

/-- The factorwise centralizer calculation for a finite commuting product. -/
theorem inf_centralizer_iSup_le_iSup {ι : Type*} [Finite ι]
    (K Q : ι → Subgroup G) (hQK : ∀ i, Q i ≤ K i)
    (hcomm : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (hself : ∀ i, K i ⊓ centralizer (Q i : Set G) ≤ Q i) :
    (⨆ i, K i) ⊓ centralizer (⨆ i, Q i : Subgroup G) ≤ ⨆ i, Q i := by
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) :
      s.sup K ⊓ centralizer ((s.sup Q : Subgroup G) : Set G) ≤ s.sup Q := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sup_insert, Finset.sup_insert]
      have hcomm' : s.sup K ≤ centralizer (K i : Set G) :=
        Finset.sup_le fun j hj => hcomm j i (ne_of_mem_of_not_mem hj hi)
      have hcommQ : s.sup K ≤ centralizer (Q i : Set G) :=
        hcomm'.trans (centralizer_le (hQK i))
      have hother : K i ≤ centralizer ((s.sup Q : Subgroup G) : Set G) :=
        le_centralizer_iff.mp ((Finset.sup_mono_fun fun j _ => hQK j).trans hcomm')
      rintro x ⟨hx, hcx⟩
      have hxprod : x ∈ (K i : Set G) * ((s.sup K : Subgroup G) : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left (K i) (s.sup K)
          (hcomm'.trans (centralizer_le_normalizer _))]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hxprod
      have hca : a ∈ centralizer (Q i : Set G) := by
        exact (centralizer (Q i : Set G)).mul_mem_cancel_right (hcommQ hb) |>.mp
          ((centralizer_le (show Q i ≤ Q i ⊔ s.sup Q from le_sup_left)) hcx)
      have hcb : b ∈ centralizer ((s.sup Q : Subgroup G) : Set G) := by
        exact (centralizer ((s.sup Q : Subgroup G) : Set G)).mul_mem_cancel_left (hother ha) |>.mp
          ((centralizer_le (show s.sup Q ≤ Q i ⊔ s.sup Q from le_sup_right)) hcx)
      exact mul_mem (mem_sup_left (hself i ⟨ha, hca⟩)) (mem_sup_right (ih ⟨hb, hcb⟩))
  have ht := hs Finset.univ
  rwa [Finset.sup_univ_eq_iSup, Finset.sup_univ_eq_iSup] at ht

/-- Self-centralizing p-cores persist in an extension with p-group quotient,
using the ambient relative-centralizer bound on `D.pCoreIn p`.

This ambient variant was formerly named `centralizer_pCore_le_of_normal_pGroup_quotient`.
That name is reserved for the intrinsic variant in
`GeneralizedFitting.ComponentLocalClosure.Extension`, whose core bound precedes
the quotient hypothesis. -/
theorem centralizer_pCore_le_of_normal_pGroup_quotient_of_inf_centralizer_le {p : ℕ}
    (D : Subgroup G) [D.Normal] (hquot : IsPGroup p (G ⧸ D))
    (hself : D ⊓ centralizer (D.pCoreIn p : Set G) ≤ D.pCoreIn p) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  let C := centralizer (pCore p G : Set G)
  let f : C →* (G ⧸ D) := (QuotientGroup.mk' D).comp C.subtype
  have hn : (D.pCoreIn p).Normal := inferInstanceAs ((pCore p D).map D.subtype).Normal
  have hcore : D.pCoreIn p ≤ pCore p G :=
    le_sSup ⟨hn, isPGroup_pCoreIn p D⟩
  have hker : IsPGroup p f.ker := by
    have hk : f.ker.map C.subtype ≤ D.pCoreIn p := by
      rintro x ⟨y, hy, rfl⟩
      apply hself
      exact ⟨(QuotientGroup.eq_one_iff _).mp hy,
        centralizer_le hcore y.property⟩
    exact ((isPGroup_pCoreIn p D).to_le hk).of_equiv
      (equivMapOfInjective f.ker C.subtype C.subtype_injective).symm
  have hCp : IsPGroup p C := by
    have ht := (hquot.to_subgroup (⊤ : Subgroup (G ⧸ D))).comap_of_ker_isPGroup f hker
    simpa using ht.of_equiv Subgroup.topEquiv
  exact le_sSup ⟨inferInstance, hCp⟩

/-- The relative centralizer bound is invariant under faithful embeddings. -/
theorem inf_centralizer_map_le_iff {F : Type*} [Group F]
    (K Q : Subgroup G) (f : G →* F) (hf : Function.Injective f) :
    K.map f ⊓ centralizer (Q.map f : Set F) ≤ Q.map f ↔
      K ⊓ centralizer (Q : Set G) ≤ Q := by
  constructor
  · intro h x hx
    have hfx : f x ∈ Q.map f := by
      apply h
      refine ⟨mem_map_of_mem f hx.1, ?_⟩
      rintro y ⟨q, hq, rfl⟩
      simpa only [← map_mul] using congrArg f (hx.2 q hq)
    obtain ⟨q, hq, he⟩ := hfx
    exact hf he ▸ hq
  · rintro h x ⟨⟨a, ha, rfl⟩, hx⟩
    refine mem_map.mpr ⟨a, h ⟨ha, ?_⟩, rfl⟩
    intro q hq
    apply hf
    simpa only [map_mul] using hx (f q) (mem_map_of_mem f hq)

/-- Intrinsic and ambient formulations of a self-centralizing core agree. -/
theorem inf_centralizer_pCoreIn_le_iff (p : ℕ) (K : Subgroup G) :
    K ⊓ centralizer (K.pCoreIn p : Set G) ≤ K.pCoreIn p ↔
      centralizer (pCore p K : Set K) ≤ pCore p K := by
  have h := inf_centralizer_map_le_iff (⊤ : Subgroup K) (pCore p K)
    K.subtype K.subtype_injective
  simpa only [pCoreIn, ← MonoidHom.range_eq_map, K.range_subtype, top_inf_eq] using h

/-- Repeated local factors coincide; distinct factors commute. -/
theorem IsComponent.local_conjugates_eq_or_commute {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) (a b : A) :
    K.map (MulAut.conj (b : G)).toMonoidHom =
      K.map (MulAut.conj (a : G)).toMonoidHom ∨
    ⁅K.map (MulAut.conj (b : G)).toMonoidHom,
      K.map (MulAut.conj (a : G)).toMonoidHom⁆ = ⊥ := by
  have hseed (c : A) : K.map (MulAut.conj (c : G)).toMonoidHom = K ∨
      ⁅K.map (MulAut.conj (c : G)).toMonoidHom, K⁆ = ⊥ := by
    by_cases he : L.map (MulAut.conj (c : G)).toMonoidHom = L
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp
        (hinv ⟨c.property, mem_normalizer_iff_map_conj_eq.mpr he⟩))
    · exact Or.inr (le_bot_iff.mp ((commutator_mono (map_mono hK) hK).trans
        ((hL.map_conj (c : G)).commutator_eq_bot_of_ne hL he).le))
  have he : (MulAut.conj (a : G)).toMonoidHom.comp
      (MulAut.conj ((a⁻¹ * b : A) : G)).toMonoidHom =
        (MulAut.conj (b : G)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rcases hseed (a⁻¹ * b) with heq | hc
  · left
    have hm := congrArg (Subgroup.map (MulAut.conj (a : G)).toMonoidHom) heq
    simpa only [map_map, he] using hm
  · right
    have hm := congrArg (Subgroup.map (MulAut.conj (a : G)).toMonoidHom) hc
    simpa only [map_commutator, map_map, he, Subgroup.map_bot] using hm

/-- The orbit of the local core is a p-group normalized by the full overgroup. -/
theorem IsComponent.local_core_orbit {p : ℕ} [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    IsPGroup p (componentOrbit (K.pCoreIn p) A) ∧
      componentOrbit (K.pCoreIn p) A ≤ componentOrbit K A ∧
      K ⊔ A ≤ normalizer (componentOrbit (K.pCoreIn p) A : Set G) := by
  have hinvQ : A ⊓ normalizer (L : Set G) ≤ normalizer (K.pCoreIn p : Set G) :=
    hinv.trans (normalizer_le_normalizer_characteristic_image K (pCore p K))
  have hnorm : ∀ a : A, K ≤ normalizer
      ((K.pCoreIn p).map (MulAut.conj (a : G)).toMonoidHom : Set G) := by
    intro a
    rw [map_pCoreIn_of_injective p K _ (MulAut.conj (a : G)).injective]
    apply le_trans _ (normalizer_le_normalizer_characteristic_image _ (pCore p _))
    have hn := hL.local_conjugates_normalize hK hinv a 1
    have he : (MulAut.conj ((1 : A) : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rwa [he, Subgroup.map_id] at hn
  refine ⟨?_, ?_, sup_le ?_ (le_normalizer_componentOrbit _ A)⟩
  · exact isPGroup_iSup_of_normalizes _
      (fun a => (isPGroup_pCoreIn p K).map _)
      (fun a b => hL.local_conjugates_normalize ((pCoreIn_le p K).trans hK) hinvQ b a)
  · exact iSup_mono fun _ => map_mono (pCoreIn_le p K)
  · exact (le_iInf hnorm).trans (iInf_normalizer_le_normalizer_iSup _)

/-- The orbit of the local core lies in the actual core of the overgroup. -/
theorem IsComponent.local_core_orbit_le {p : ℕ} [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    componentOrbit (K.pCoreIn p) A ≤ (K ⊔ A).pCoreIn p := by
  obtain ⟨hp, hle, hn⟩ := hL.local_core_orbit (p := p) hK hinv
  exact le_pCoreIn_of_normalizes hp (hle.trans (componentOrbit_le_sup K A)) hn

/-- A nontrivial seed core remains nontrivial in the full local overgroup. -/
theorem IsComponent.local_adjoin_core_ne_bot {p : ℕ} [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hne : K.pCoreIn p ≠ ⊥) : (K ⊔ A).pCoreIn p ≠ ⊥ := by
  intro he
  apply hne
  exact le_bot_iff.mp (he ▸ (le_componentOrbit _ A).trans (hL.local_core_orbit_le hK hinv))

/-- The full local orbit has p-group quotient after adjoining a p-subgroup. -/
theorem local_orbit_quotient_isPGroup {p : ℕ} (K A : Subgroup G) (hA : IsPGroup p A) :
    let D := (componentOrbit K A).subgroupOf (K ⊔ A)
    let := componentOrbit_normal_subgroupOf_sup K A
    IsPGroup p ((K ⊔ A : Subgroup G) ⧸ D) := by
  let := componentOrbit_normal_subgroupOf_sup K A
  apply isPGroup_quotient_of_sup_eq_top _ (A.subgroupOf (K ⊔ A)) hA.comap_subtype
  rw [← subgroupOf_sup (componentOrbit_le_sup K A) le_sup_right, componentOrbit_sup,
    subgroupOf_self]

/-- P-perfect subgroups of a local overgroup are contained in its orbit. -/
theorem le_local_orbit_of_isPPerfect {p : ℕ} (K A : Subgroup G) (hA : IsPGroup p A)
    (B : Subgroup (K ⊔ A : Subgroup G)) (hB : IsPPerfect p B) :
    B ≤ (componentOrbit K A).subgroupOf (K ⊔ A) := by
  let := componentOrbit_normal_subgroupOf_sup K A
  exact (le_pResidual_of_isPPerfect B hB).trans
    (sInf_le ⟨inferInstance, local_orbit_quotient_isPGroup K A hA⟩)

/-- A finite product of the commuting local factors has self-centralizing core. -/
theorem IsComponent.local_orbit_centralizer {p : ℕ} [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : K ⊓ centralizer (K.pCoreIn p : Set G) ≤ K.pCoreIn p) :
    componentOrbit K A ⊓ centralizer (componentOrbit (K.pCoreIn p) A : Set G) ≤
      componentOrbit (K.pCoreIn p) A := by
  let F := fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom
  let I := {T : Subgroup G // T ∈ Set.range F}
  have hsup : (⨆ i : I, (i : Subgroup G)) = componentOrbit K A := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨T, a, rfl⟩
      exact le_iSup F a
    · exact iSup_le fun a => le_iSup (fun i : I => (i : Subgroup G)) ⟨F a, a, rfl⟩
  have hsupQ : (⨆ i : I, (i : Subgroup G).pCoreIn p) =
      componentOrbit (K.pCoreIn p) A := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨T, a, rfl⟩
      change (F a).pCoreIn p ≤ _
      rw [← map_pCoreIn_of_injective p K _ (MulAut.conj (a : G)).injective]
      exact le_iSup (fun b : A => (K.pCoreIn p).map (MulAut.conj (b : G)).toMonoidHom) a
    · apply iSup_le
      intro a
      rw [map_pCoreIn_of_injective p K _ (MulAut.conj (a : G)).injective]
      exact le_iSup (fun i : I => (i : Subgroup G).pCoreIn p) ⟨F a, a, rfl⟩
  rw [← hsup, ← hsupQ]
  refine inf_centralizer_iSup_le_iSup (fun i : I => i.val)
    (fun i : I => i.val.pCoreIn p) (fun i => pCoreIn_le p i.val) ?_ ?_
  · intro i j hij
    obtain ⟨a, ha⟩ := i.property
    obtain ⟨b, hb⟩ := j.property
    rcases hL.local_conjugates_eq_or_commute hK hinv b a with he | hc
    · exact (hij (Subtype.ext (ha.symm.trans (he.trans hb)))).elim
    · apply commutator_eq_bot_iff_le_centralizer.mp
      simpa only [← ha, ← hb] using hc
  · rintro ⟨T, a, rfl⟩
    change F a ⊓ centralizer ((F a).pCoreIn p : Set G) ≤ (F a).pCoreIn p
    rw [← map_pCoreIn_of_injective p K _ (MulAut.conj (a : G)).injective]
    exact (inf_centralizer_map_le_iff K (K.pCoreIn p) _
      (MulAut.conj (a : G)).injective).mpr hself

/-- Characteristic p passes from the seed to the full component-orbit overgroup. -/
theorem IsComponent.local_adjoin_centralizer {p : ℕ} [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L) (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : K ⊓ centralizer (K.pCoreIn p : Set G) ≤ K.pCoreIn p) :
    (K ⊔ A) ⊓ centralizer ((K ⊔ A).pCoreIn p : Set G) ≤ (K ⊔ A).pCoreIn p := by
  let X := K ⊔ A
  let D := componentOrbit K A
  let Q := componentOrbit (K.pCoreIn p) A
  have hDX : D ≤ X := componentOrbit_le_sup K A
  obtain ⟨hQp, hQD, hXQ⟩ := hL.local_core_orbit (p := p) hK hinv
  have hQcore : Q ≤ D.pCoreIn p :=
    le_pCoreIn_of_normalizes hQp hQD (hDX.trans hXQ)
  have hDC : D ⊓ centralizer (D.pCoreIn p : Set G) ≤ D.pCoreIn p :=
    (inf_le_inf_left D (centralizer_le hQcore)).trans
      ((hL.local_orbit_centralizer hK hinv hself).trans hQcore)
  let D' := D.subgroupOf X
  let : D'.Normal := componentOrbit_normal_subgroupOf_sup K A
  have hm : D'.map X.subtype = D := map_subgroupOf_eq_of_le hDX
  have hmc : (D'.pCoreIn p).map X.subtype = D.pCoreIn p := by
    rw [map_pCoreIn_of_injective p D' _ X.subtype_injective, hm]
  have hself' : D' ⊓ centralizer (D'.pCoreIn p : Set X) ≤ D'.pCoreIn p := by
    apply (inf_centralizer_map_le_iff D' (D'.pCoreIn p) X.subtype X.subtype_injective).mp
    rwa [hm, hmc]
  have hX : centralizer (pCore p X : Set X) ≤ pCore p X :=
    centralizer_pCore_le_of_normal_pGroup_quotient_of_inf_centralizer_le D'
      (local_orbit_quotient_isPGroup K A hA) hself'
  have ht : (⊤ : Subgroup X) ⊓ centralizer (pCore p X : Set X) ≤ pCore p X := by
    simpa only [top_inf_eq] using hX
  have hh := (inf_centralizer_map_le_iff (⊤ : Subgroup X) (pCore p X)
    X.subtype X.subtype_injective).mpr ht
  change X ⊓ centralizer ((pCore p X).map X.subtype : Set G) ≤ (pCore p X).map X.subtype
  simpa only [← MonoidHom.range_eq_map, X.range_subtype] using hh

/-- Homomorphisms carry the actual conjugate orbit to the orbit of the images. -/
theorem map_componentOrbit {F : Type*} [Group F] (K A : Subgroup G) (f : G →* F) :
    (componentOrbit K A).map f = componentOrbit (K.map f) (A.map f) := by
  have hm (a : G) : (K.map (MulAut.conj a).toMonoidHom).map f =
      (K.map f).map (MulAut.conj (f a)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  change (⨆ a : A, K.map (MulAut.conj (a : G)).toMonoidHom).map f = _
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro a
    rw [hm]
    exact le_iSup (fun b : A.map f => (K.map f).map (MulAut.conj (b : F)).toMonoidHom)
      ⟨f a, mem_map_of_mem f a.property⟩
  · apply iSup_le
    rintro ⟨b, a, ha, rfl⟩
    rw [← hm]
    exact le_iSup (fun b : A => (K.map (MulAut.conj (b : G)).toMonoidHom).map f) ⟨a, ha⟩

end Theory.GroupTheory

end
