module
public import Theory.Representation.SmallBinaryPrimeNormalizer.NormalClosure
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Dihedral groups on canonical binary four-spaces

An involution normalizing an order-five subgroup and fixing its fixed
complement generates a genuine dihedral group of order ten with it.
Restriction to the four-dimensional support is faithful for all actors
fixing the complement. The small binary normalizer calculation puts products
of involutions in the five-subgroup, so the full normalizer of that subgroup
preserves the dihedral extension. Adjoining the reflection leaves the
support and its fixed complement unchanged.

Source: Aschbacher–Smith, D.2.12–17, printed pp.183–187; the dihedral
factor construction used in 14.7.6, printed p.1044, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace SmallBinaryPrimeNormalizer
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]

/-- The five-factor's normalizer preserves the dihedral group supported there. -/
theorem supported_dihedral_normalizer
    (C R : Subgroup G) (hC : Nat.card C = 5) (hR : Nat.card R = 2)
    (hn : R ≤ normalizer (C : Set G))
    (hfix : FixedPoints.subgroup C V ≤ FixedPoints.subgroup R V)
    (hU : Nat.card (commutatorAction C V) = 16) :
    Nonempty ((C ⊔ R : Subgroup G) ≃* DihedralGroup 5) ∧
      normalizer (C : Set G) ≤ normalizer ((C ⊔ R : Subgroup G) : Set G) := by
  classical
  let F := FixedPoints.subgroup C V
  let U := commutatorAction C V
  let E := normalizer (C : Set G) ⊓ fixingSubgroup G (F : Set V)
  have hCE : C ≤ E := by
    intro c hc
    refine ⟨C.le_normalizer hc,?_⟩
    exact (mem_fixingSubgroup_iff G).mpr (fun v hv => hv ⟨c,hc⟩)
  have hRE : R ≤ E := by
    intro r hr
    refine ⟨hn hr,?_⟩
    exact (mem_fixingSubgroup_iff G).mpr (fun v hv => hfix hv ⟨r,hr⟩)
  let C₀ := C.subgroupOf E
  let R₀ := R.subgroupOf E
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer inf_le_left
  let : IsInvariant E V U := commutatorAction_isInvariant_of_normalizing_actor E C inf_le_left
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective U.subtype U.subtype_injective
  have hcop : Nat.Coprime (Nat.card C) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hC,hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hs := ActionSupport.fixed_support_isCompl C hcop
  let : FaithfulSMul E U := by
    constructor
    intro a b he
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    obtain ⟨f,hf,u,hu,rfl⟩ := Subgroup.mem_sup.mp
      (show v ∈ F ⊔ U from hs.sup_eq_top ▸ mem_top v)
    have ha : (a : G) • f = f := (mem_fixingSubgroup_iff G).mp a.property.2 f hf
    have hb : (b : G) • f = f := (mem_fixingSubgroup_iff G).mp b.property.2 f hf
    have hu' : (a : G) • u = (b : G) • u := congrArg Subtype.val (he ⟨u,hu⟩)
    simp only [smul_mul',ha,hb,hu']
  have hC₀ : Nat.card C₀ = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv).trans hC
  have hR₀ : Nat.card R₀ = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRE).toEquiv).trans hR
  let : IsCyclic R₀ := isCyclic_of_prime_card hR₀
  let : IsElementaryAbelian 2 R₀ := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      hR₀ ▸ pow_card_eq_one' (x := x) }
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := R₀) 2 (by rw [hR₀])
  let t₀ : E := t
  have ht₀ : IsInvolution t₀ := by
    have ho : orderOf t₀ = 2 := (orderOf_injective R₀.subtype R₀.subtype_injective t).trans ht
    exact ⟨fun he => by simp [he] at ho,ho ▸ pow_orderOf_eq_one t₀⟩
  have hprod (s : E) (hs : IsInvolution s) : s * t₀ ∈ C₀ :=
    involution_mul_mem_five (V := U) C₀ hC₀ hU s t₀ hs ht₀
  have htR : (t₀ : G) ∈ R := t.property
  have hconj (g : G) (hg : g ∈ normalizer (C : Set G))
      (r : G) (hr : r ∈ R) : g * r * g⁻¹ ∈ C ⊔ R := by
    by_cases hr1 : r = 1
    · simp [hr1]
    have hr2 : r ^ 2 = 1 := by
      have hp := pow_card_eq_one' (x := (⟨r,hr⟩ : R))
      rw [hR] at hp
      exact congrArg Subtype.val hp
    let : IsInvariant (normalizer (C : Set G)) V F :=
      fixedPoints_isInvariant_of_normalizing_actor _ C le_rfl
    have hsE : g * r * g⁻¹ ∈ E := by
      refine ⟨(normalizer (C : Set G)).mul_mem
        ((normalizer (C : Set G)).mul_mem hg (hn hr))
        ((normalizer (C : Set G)).inv_mem hg),?_⟩
      apply (mem_fixingSubgroup_iff G).mpr
      intro v hv
      have hv' : g⁻¹ • v ∈ F :=
        (IsInvariant.invariant (A := normalizer (C : Set G))
          (⟨g⁻¹,(normalizer (C : Set G)).inv_mem hg⟩) v).mp hv
      have hh := hfix hv' ⟨r,hr⟩
      change r • (g⁻¹ • v) = g⁻¹ • v at hh
      simp only [mul_smul,hh,smul_inv_smul]
    let s : E := ⟨g * r * g⁻¹,hsE⟩
    have hsi : IsInvolution s := by
      constructor
      · intro he
        apply hr1
        have hh := congrArg Subtype.val he
        change g * r * g⁻¹ = 1 at hh
        simpa [mul_assoc] using congrArg (fun x => g⁻¹ * x * g) hh
      · apply Subtype.ext
        change (g * r * g⁻¹)^2 = 1
        rw [conj_pow,hr2]
        simp
    have hm : (s : G) * (t₀ : G) ∈ C := hprod s hsi
    have hh : ((s : G) * (t₀ : G)) * (t₀ : G)⁻¹ ∈ C ⊔ R :=
      (C ⊔ R).mul_mem (mem_sup_left hm) ((C ⊔ R).inv_mem (mem_sup_right htR))
    simpa only [mul_inv_cancel_right] using hh
  have hnormal : normalizer (C : Set G) ≤ normalizer ((C ⊔ R : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hh : C ⊔ R ≤ (C ⊔ R).comap (MulAut.conj g).toMonoidHom := by
      apply sup_le
      · intro c hc
        exact mem_sup_left ((mem_normalizer_iff.mp hg c).mp hc)
      · exact fun r hr => hconj g hg r hr
    exact hh hx
  have hjoinCard : Nat.card (C ⊔ R : Subgroup G) = 10 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C R hn
      (disjoint_of_coprime_natCard (by rw [hC,hR]; decide)),hC,hR]
  let D₀ := (C ⊔ R).subgroupOf E
  let : D₀.Normal := normal_subgroupOf_of_le_normalizer (inf_le_left.trans hnormal)
  have hne : R₀ ≠ ⊥ := by intro he; simp [he] at hR₀
  obtain ⟨e⟩ := normalClosure_dihedral (V := U) hU C₀ R₀ hC₀ hne
  have hle : normalClosure (R₀ : Set E) ≤ D₀ :=
    normalClosure_le_normal (fun _ hx => mem_sup_right hx)
  have hcardD : Nat.card D₀ = 10 :=
    (Nat.card_congr (subgroupOfEquivOfLe (sup_le hCE hRE)).toEquiv).trans hjoinCard
  have heq : normalClosure (R₀ : Set E) = D₀ := eq_of_le_of_card_ge hle (by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card,hcardD])
  exact ⟨⟨(subgroupOfEquivOfLe (sup_le hCE hRE)).symm.trans
    ((MulEquiv.subgroupCongr heq).symm.trans e)⟩,hnormal⟩

omit [FaithfulSMul G V] in
/-- Adjoining actors fixing the coprime fixed complement does not enlarge the support. -/
theorem supported_join_support
    (C R : Subgroup G) (hC : Nat.card C = 5)
    (hn : R ≤ normalizer (C : Set G))
    (hfix : FixedPoints.subgroup C V ≤ FixedPoints.subgroup R V) :
    FixedPoints.subgroup C V ≤ FixedPoints.subgroup (C ⊔ R : Subgroup G) V ∧
      commutatorAction (C ⊔ R : Subgroup G) V = commutatorAction C V := by
  let F := FixedPoints.subgroup C V
  let U := commutatorAction C V
  let D := C ⊔ R
  have hDF : D ≤ fixingSubgroup G (F : Set V) := by
    apply sup_le
    · intro c hc
      exact (mem_fixingSubgroup_iff G).mpr (fun v hv => hv ⟨c,hc⟩)
    · intro r hr
      exact (mem_fixingSubgroup_iff G).mpr (fun v hv => hfix hv ⟨r,hr⟩)
  have hcop : Nat.Coprime (Nat.card C) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hC,hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hs := ActionSupport.fixed_support_isCompl C hcop
  let : IsInvariant D V U := commutatorAction_isInvariant_of_normalizing_actor D C
    (sup_le C.le_normalizer hn)
  refine ⟨fun v hv d => (mem_fixingSubgroup_iff G).mp (hDF d.property) v hv,?_⟩
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨d,v,rfl⟩
    obtain ⟨f,hf,u,hu,rfl⟩ := Subgroup.mem_sup.mp
      (show v ∈ F ⊔ U from hs.sup_eq_top ▸ mem_top v)
    have hdf : (d : G) • f = f := (mem_fixingSubgroup_iff G).mp (hDF d.property) f hf
    have hdu : (d : G) • u ∈ U := (IsInvariant.invariant d u).mp hu
    change (f * u)⁻¹ * (d : G) • (f * u) ∈ U
    simpa only [smul_mul',hdf,mul_inv_rev,mul_assoc,inv_mul_cancel_left] using
      U.mul_mem (U.inv_mem hu) hdu
  · rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c,v,rfl⟩
    exact ⟨⟨c,mem_sup_left c.property⟩,v,rfl⟩

end SmallBinaryPrimeNormalizer
