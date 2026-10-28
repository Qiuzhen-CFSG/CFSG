module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The literal inner subgroup of a quintic component action

Pull the whole original action image back through faithful conjugation on
the core-central quotient. The quotient of order five, two-perfectness and
solvability survive. The supplied component Sylow maps through the original
projection and normalizes this same subgroup. Its normalized product has
order a power of two times five.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem image_quintic_quotient {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 A) (hfive : Nat.card (A ⧸ pCore 2 A) = 5)
    (hne : Nat.card B ≠ 1) : Nat.card (B ⧸ pCore 2 B) = 5 := by
  have hle : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 A) (pCore 2 B) f (map_le_iff_le_comap.mp hle)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a,rfl⟩
  have hc : Nat.card (B ⧸ pCore 2 B) ∣ 5 := hfive ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc
  · have ht : pCore 2 B = ⊤ := index_eq_one.mp hc
    have hB : IsPGroup 2 B := pCore_isPGroup.of_surjective
      ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom
      ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
    have hz := hp.hom_eq_one_of_isPGroup hB f
    have hr : (⊤ : Subgroup B) = ⊥ := by
      rw [←f.range_eq_top_of_surjective hf,hz]
      simp
    apply (hne _).elim
    have he := congrArg (fun U : Subgroup B => Nat.card U) hr
    simpa using he
  · exact hc

private theorem quintic_normalized_join_card {C : Type*} [Group C] [Finite C]
    (Y P : Subgroup C) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (Y : Set C))
    (hfive : Nat.card (Y ⧸ pCore 2 Y) = 5) :
    ∃ a : ℕ, Nat.card (Y ⊔ P : Subgroup C) = 2^a * 5 := by
  obtain ⟨b,hb⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  obtain ⟨c,hc⟩ := hP.exists_card_eq
  obtain ⟨d,hd⟩ := (hP.to_le (show Y ⊓ P ≤ P from inf_le_right)).exists_card_eq
  have hdc : d ≤ c := by
    have hh := card_le_of_le (show Y ⊓ P ≤ P from inf_le_right)
    rw [hd,hc] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hY : Nat.card Y = 2^b * 5 := by
    have hh := (pCore 2 Y).card_mul_index
    rw [hb,index_eq_card,hfive] at hh
    exact hh.symm
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes Y P hn
  refine ⟨b+(c-d),Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) d) ?_⟩
  calc
    2^d * Nat.card (Y ⊔ P : Subgroup C) = Nat.card Y * Nat.card P := by
      rw [hd] at he
      exact he.symm
    _ = (2^b * 5) * 2^c := by rw [hY,hc]
    _ = 2^d * (2^(b+(c-d)) * 5) := by
      have hec : 2^c = 2^(c-d) * 2^d := by
        rw [←pow_add,Nat.sub_add_cancel hdc]
      rw [hec,pow_add]
      ring

/-- The inverse image under literal conjugation retains the entire
quintic action and is normalized by the supplied component Sylow image. -/
theorem coreCentral_inner_quintic_subgroup
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (K : Set G))
    (hXp : IsPPerfect 2 X) (hsolv : Group.IsSolvable X)
    (hfive : Nat.card (X ⧸ pCore 2 X) = 5)
    (himage : 5 ∣ Nat.card (coreCentralActorImage K X))
    (hz : center (coreCentralQuotient K) = ⊥)
    (hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup (coreCentralQuotient K)) :
    let Y := (coreCentralActorImage K X).comap (MulAut.conj :
      coreCentralQuotient K →* MulAut (coreCentralQuotient K))
    Y.map MulAut.conj = coreCentralActorImage K X ∧
      IsPPerfect 2 Y ∧ Group.IsSolvable Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 5 ∧
      ∃ S : Sylow 2 (coreCentralQuotient K),
        (S : Subgroup (coreCentralQuotient K)) = (U : Subgroup K).map (coreCentralProjection K) ∧
        (S : Subgroup (coreCentralQuotient K)) ≤ normalizer (Y : Set (coreCentralQuotient K)) ∧
        ∃ a : ℕ, Nat.card (Y ⊔ (S : Subgroup (coreCentralQuotient K)) :
          Subgroup (coreCentralQuotient K)) = 2^a * 5 := by
  let C := coreCentralQuotient K
  let q := coreCentralProjection K
  let a := normalizerCoreCentralAction K
  let B := coreCentralActorImage K X
  let c : C →* MulAut C := MulAut.conj
  let Y := B.comap c
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have ha (k : K) : a ⟨k,K.le_normalizer k.property⟩ = MulAut.conj (q k) := by
    ext y
    obtain ⟨x,rfl⟩ := hq y
    rw [normalizerCoreCentralAction_apply,MulAut.conj_apply,←map_inv,←map_mul,←map_mul]
    rfl
  have hc : Function.Injective c := conj_injective_of_center_eq_bot hz
  have hYB : Y.map c = B := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hinner
  let e : Y ≃* B := (Y.equivMapOfInjective c hc).trans (MulEquiv.subgroupCongr hYB)
  let ex := (subgroupOfEquivOfLe hXN).symm
  let f : X →* B := (a.subgroupMap (X.subgroupOf (normalizer (K : Set G)))).comp ex.toMonoidHom
  have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp ex.surjective
  let g : X →* Y := e.symm.toMonoidHom.comp f
  have hg : Function.Surjective g := e.symm.surjective.comp hf
  have hYp : IsPPerfect 2 Y := hXp.of_surjective g hg
  let : Group.IsSolvable X := hsolv
  have hYs : Group.IsSolvable Y := Group.isSolvable_of_surjective (f := g) hg
  have hYn : Nat.card Y ≠ 1 := by
    intro he
    have hh : 5 ∣ Nat.card Y := (Nat.card_congr e.toEquiv).symm ▸ himage
    rw [he] at hh
    norm_num at hh
  have hYfive := image_quintic_quotient g hg hXp hfive hYn
  let S := U.mapSurjective (f := q) hq
  have hSY : (S : Subgroup C) ≤ normalizer (Y : Set C) := by
    rintro z ⟨u,hu,rfl⟩
    apply Y.mem_normalizer_iff.mpr
    intro y
    change c y ∈ B ↔ c (q u * y * (q u)⁻¹) ∈ B
    rw [map_mul,map_mul,map_inv]
    have hn : a ⟨u,K.le_normalizer u.property⟩ ∈ normalizer (B : Set (MulAut C)) := by
      apply (X.subgroupOf (normalizer (K : Set G))).le_normalizer_map a
      apply mem_map_of_mem
      apply mem_normalizer_iff.mpr
      intro x
      exact mem_normalizer_iff.mp (hUX (mem_map_of_mem K.subtype hu)) (x : G)
    rw [ha] at hn
    exact mem_normalizer_iff.mp hn (c y)
  exact ⟨hYB,hYp,hYs,hYfive,S,rfl,hSY,
    quintic_normalized_join_card Y S S.isPGroup' hSY hYfive⟩

end Theory.GroupTheory
