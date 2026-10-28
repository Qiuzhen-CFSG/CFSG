module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureScalars
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTrialityPlacement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.Descent
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived

/-!
# Triality scalar exclusion for the original pure-line component

The fixed highest-root parameters of the faithful sixteen produce at least
fifteen scalar units. Their displacement lies in the same component Sylow,
so they normalize the actual ambient two-core. Its normalizer lies in M.
The literal pure-line action has order dividing 24, forcing this odd scalar
group to have order at most three. This excludes the Triality component without
assuming that it centralizes the paired plane.

The scalar and automorphism calculations adapt DoubledBinaryTrialityExclusion;
all original Sylow and inner-action maps are retained. Source: Aschbacher–Smith
7.7.3 H1 argument, printed pp.705–706, and 7.7.4, printed p.704.
The G₂ model uses the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The triality model uses GLS3 §§2.4 and 2.5.
-/

public noncomputable section
open CFSG.Quasithin.Chapter7.NormalizedSource
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.ConcreteBruhat.FixedDescent
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
open Triality.Standard.PositiveCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.EvenField.NormalForm.UnipotentCocycle
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureTrialityExclusion

private def scalar (P : Parameters) (hp : P.prime = 2) : (fixedField P)ˣ →* Carrier P :=
  ((torus P).subtype.comp (TorusCoordinates.torusMulEquiv P hp).toMonoidHom).comp
    (MonoidHom.inr (ExtensionField P)ˣ (fixedField P)ˣ)

private theorem scalar_split (P : Parameters) (hp : P.prime = 2) (t : (fixedField P)ˣ) :
    carrierToSplit P hp (scalar P hp t) = torusWord P 1 (TorusCoordinates.fixedUnit P t) := by
  change carrierToSplit P hp ((TorusCoordinates.torusMulEquiv P hp (1,t)).val) = _
  rw [TorusCoordinates.torusMulEquiv_val,carrierToSplit_toCarrier,
    TorusCoordinates.inclusion_orbitElementary]
  simp [TorusCoordinates.product,TorusCoordinates.expand,TorusCoordinates.torusWord_one P hp]

private theorem coefficient_weyl (P : Parameters) (σ : CoefficientAut P)
    (i : Fin 4) (t : ExtensionField P) :
    coefficientSplit P σ (weylWord P i t) = weylWord P i (σ t) := by
  simp only [weylWord,map_mul,positiveRoot,negativeRoot,
    coefficientSplit_positive,coefficientSplit_negative,map_neg,map_inv₀]

private theorem coefficient_scalar (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) (t : (fixedField P)ˣ)
    (ht : coefficientFixedField P σ (t : fixedField P) = t) :
    coefficientAction P σ (scalar P hp t) = scalar P hp t := by
  have ht' : σ ((t : fixedField P) : ExtensionField P) = t.val.val :=
    congrArg Subtype.val ht
  apply carrierToSplit_injective P hp
  simp only [carrierToSplit_coefficient,scalar_split]
  unfold torusWord
  rw [map_mul,coefficient_weyl,coefficient_weyl]
  have htunit : σ (TorusCoordinates.fixedUnit P t).val = (TorusCoordinates.fixedUnit P t).val := ht'
  rw [htunit,map_neg,map_one]


private theorem coefficient_highest (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) (t : fixedField P) :
    coefficientAction P σ (highestHom P hp (Multiplicative.ofAdd t)) =
      highestHom P hp (Multiplicative.ofAdd (coefficientFixedField P σ t)) := by
  apply carrierToSplit_injective P hp
  rw [carrierToSplit_coefficient]
  simp only [highestHom,MonoidHom.comp_apply,carrierToSplit_toCarrier,
    elementaryHighestHom_val,coefficientSplit_curve]
  rfl

private theorem coefficient_unipotent (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) :
    (unipotent P).map (coefficientAction P σ).toMonoidHom = unipotent P := by
  have preserves (f : CoefficientAut P) {x : Carrier P} (hx : x ∈ unipotent P) :
      coefficientAction P f x ∈ unipotent P := by
    apply (mem_descend_iff P hp (positiveSubgroup P) _).mpr
    rw [carrierToSplit_coefficient]
    exact (coefficientSplit_positiveSubgroup P f).le
      ⟨_,(mem_descend_iff P hp (positiveSubgroup P) x).mp hx,rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact preserves σ hx
  · intro x hx
    refine ⟨coefficientAction P σ⁻¹ x,preserves σ⁻¹ hx,?_⟩
    change (coefficientAction P σ * coefficientAction P σ⁻¹) x = x
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl

private theorem stabilizing_factorization (n : ℕ) (hn : 0 < n)
    (α : MulAut (BinaryCarrier n hn))
    (hα : (unipotent (binaryParameters n hn)).map α.toMonoidHom = unipotent _) :
    ∃ b : borel (binaryParameters n hn), ∃ σ : CoefficientAut (binaryParameters n hn),
      α = MulAut.conj b.val * coefficientAction _ σ := by
  let P := binaryParameters n hn
  obtain ⟨b,σ,he⟩ := binary_inner_coefficient n hn α
  refine ⟨⟨b,?_⟩,σ,he⟩
  rw [←normalizer_unipotent_eq_borel P rfl]
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    (unipotent P).map (MulAut.conj b).toMonoidHom =
        ((unipotent P).map (coefficientAction P σ).toMonoidHom).map
          (MulAut.conj b).toMonoidHom := by rw [coefficient_unipotent P rfl]
    _ = (unipotent P).map α.toMonoidHom := by rw [map_map,he]; rfl
    _ = unipotent P := hα

private theorem scalar_borel_displacement (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (b : borel P) :
    scalar P hp t * (b.val * scalar P hp t * b.val⁻¹)⁻¹ ∈ unipotent P := by
  obtain ⟨u,hu,d,hd,hprod⟩ := (borel_eq_mul P hp).le b.property
  have ht : scalar P hp t ∈ torus P := (TorusCoordinates.torusMulEquiv P hp (1,t)).property
  have hdt : Commute d (scalar P hp t) := by
    obtain ⟨a,ha⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective ⟨d,hd⟩
    have hh := (Commute.all a (1,t)).map
      ((torus P).subtype.comp (TorusCoordinates.torusMulEquiv P hp).toMonoidHom)
    change Commute (TorusCoordinates.torusMulEquiv P hp a).val (scalar P hp t) at hh
    exact (congrArg (fun z : torus P => Commute z.val (scalar P hp t)) ha).mp hh
  have hn : scalar P hp t ∈ normalizer (unipotent P : Set (Carrier P)) := by
    rw [normalizer_unipotent_eq_borel P hp]
    exact torus_le_borel P ht
  have hmem := (unipotent P).mul_mem (((mem_normalizer_iff.mp hn) u).mp hu)
    ((unipotent P).inv_mem hu)
  rw [←hprod]
  have he : (u*d) * scalar P hp t * (u*d)⁻¹ = u * scalar P hp t * u⁻¹ := by
    calc
      _ = u * (d * scalar P hp t * d⁻¹) * u⁻¹ := by group
      _ = _ := by rw [hdt.mul_inv_cancel]
  rw [he]
  convert hmem using 1
  group

private def fixedUnits {F : Type*} [Field F] {X : Type*} (σ : X → F ≃+* F) : Subgroup Fˣ where
  carrier := {t | ∀ x, σ x (t : F) = t}
  one_mem' := by intro x; exact map_one (σ x)
  mul_mem' := by intro a b ha hb x; simp only [Units.val_mul,map_mul,ha x,hb x]
  inv_mem' := by intro a ha x; simp only [Units.val_inv_eq_inv_val,map_inv₀,ha x]

private def rootEquiv (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (fixedField P) ≃* highestRoot P :=
  (MonoidHom.ofInjective (highestHom_injective P hp)).trans
    (MulEquiv.subgroupCongr (highestHom_range P hp))

private theorem fixed_root_scalar_normalizers {X : Type*} (n : ℕ) (hn : 0 < n)
    (α : X → MulAut (BinaryCarrier n hn))
    (hα : ∀ x, (unipotent (binaryParameters n hn)).map (α x).toMonoidHom = unipotent _)
    (A : Subgroup (BinaryCarrier n hn)) (hAZ : A ≤ highestRoot (binaryParameters n hn)) (hA : A ≠ ⊥)
    (hfix : ∀ x, ∀ a ∈ A, α x a = a) :
    ∃ B : Subgroup (fixedField (binaryParameters n hn))ˣ, Nat.card A - 1 ≤ Nat.card B ∧
      ∀ t : B, ∀ x, scalar _ rfl t.val * (α x (scalar _ rfl t.val))⁻¹ ∈ unipotent _ := by
  classical
  let P := binaryParameters n hn
  choose b σ he using fun x => stabilizing_factorization n hn (α x) (hα x)
  choose l hl using fun x => NormalizedRootCentralizers.borel_conjugate_highestHom P rfl
    (b x).val (b x).property
  let τ : X → fixedField P ≃+* fixedField P := fun x => coefficientFixedField P (σ x)
  let B := fixedUnits τ
  let c : A → fixedField P := fun a => ((rootEquiv P rfl).symm ⟨a.val,hAZ a.property⟩).toAdd
  have hc (a : A) : highestHom P rfl (Multiplicative.ofAdd (c a)) = a.val :=
    congrArg Subtype.val ((rootEquiv P rfl).apply_symm_apply ⟨a.val,hAZ a.property⟩)
  have hci : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    exact (hc a).symm.trans ((congrArg (fun z => highestHom P rfl (Multiplicative.ofAdd z)) hab).trans (hc b))
  have hc1 : c 1 = 0 := by
    apply Multiplicative.ofAdd.injective
    apply highestHom_injective P rfl
    exact (hc 1).trans (map_one _).symm
  have hcz (a : A) (ha : a ≠ 1) : c a ≠ 0 := by
    intro hz
    exact ha (hci (hz.trans hc1.symm))
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hA
  let a₀ : A := ⟨a,ha⟩
  have hc0 : c a₀ ≠ 0 := hcz a₀ (fun hh => hane (congrArg Subtype.val hh))
  have hscalar (x : X) (a : A) : (l x : fixedField P) * τ x (c a) = c a := by
    apply Multiplicative.ofAdd.injective
    apply highestHom_injective P rfl
    rw [←hl x]
    have hhcoeff := coefficient_highest P rfl (σ x) (c a)
    change coefficientAction P (σ x) (highestHom P rfl (Multiplicative.ofAdd (c a))) =
      highestHom P rfl (Multiplicative.ofAdd (τ x (c a))) at hhcoeff
    rw [←hhcoeff]
    have hh := hfix x a.val a.property
    rw [he x] at hh
    change b x * coefficientAction P (σ x) a.val * (b x : Carrier P)⁻¹ = a.val at hh
    simpa only [hc] using hh
  let r : {a : A // a ≠ 1} → B := fun a =>
    ⟨Units.mk0 (c a.val / c a₀) (div_ne_zero (hcz a.val a.property) hc0),by
      intro x
      change τ x (c a.val / c a₀) = c a.val / c a₀
      rw [map_div₀]
      have hh : ((l x : fixedField P)*τ x (c a.val)) / ((l x : fixedField P)*τ x (c a₀)) =
          c a.val / c a₀ := by rw [hscalar,hscalar]
      simpa only [mul_div_mul_left _ _ (Units.ne_zero (l x))] using hh⟩
  have hr : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    apply hci
    have hh := congrArg (fun z : B => (z.val : fixedField P)) hab
    exact (div_left_inj' hc0).mp hh
  have hcard : Nat.card {a : A // a ≠ 1} = Nat.card A - 1 := by
    let := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  refine ⟨B,hcard ▸ Nat.card_le_card_of_injective r hr,?_⟩
  intro t x
  have hfield := coefficient_scalar P rfl (σ x) t.val (t.property x)
  have hact : α x (scalar P rfl t.val) = b x * scalar P rfl t.val * (b x : Carrier P)⁻¹ := by
    rw [he x]
    change b x * coefficientAction P (σ x) (scalar P rfl t.val) * (b x : Carrier P)⁻¹ = _
    rw [hfield]
  rw [hact]
  exact scalar_borel_displacement P rfl t.val (b x)

/-- Scalar displacements in the concrete Sylow lift to normalizers of the
original ambient two-group, retaining the original component embedding. -/
private theorem ambient_scalar_normalizers {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 0 < n) (K Q : Subgroup G) (hQN : Q ≤ normalizer (K : Set G))
    (e : K ≃* BinaryCarrier n hn)
    (hU : (Q.subgroupOf K).map e.toMonoidHom = unipotent (binaryParameters n hn))
    (A : Subgroup K) (hA : Nat.card A = 16)
    (hAZ : A.map e.toMonoidHom ≤ highestRoot (binaryParameters n hn))
    (hQA : Q ≤ centralizer (A.map K.subtype : Set G)) :
    ∃ B : Subgroup (fixedField (binaryParameters n hn))ˣ, 15 ≤ Nat.card B ∧
      ∀ t : B, (e.symm (scalar (binaryParameters n hn) rfl t.val) : G) ∈ normalizer (Q : Set G) := by
  let α : Q → MulAut (BinaryCarrier n hn) := fun q =>
    e.symm.trans ((K.normalizerMonoidHom ⟨q.val,hQN q.property⟩).trans e)
  have hα (q : Q) : (unipotent (binaryParameters n hn)).map (α q).toMonoidHom = unipotent (binaryParameters n hn) := by
    have hle : (unipotent (binaryParameters n hn)).map (α q).toMonoidHom ≤ unipotent (binaryParameters n hn) := by
      rintro x ⟨y,hy,rfl⟩
      rw [←hU] at hy ⊢
      obtain ⟨k,hk,rfl⟩ := hy
      refine ⟨K.normalizerMonoidHom ⟨q.val,hQN q.property⟩ k,?_,?_⟩
      · change (K.normalizerMonoidHom ⟨q.val,hQN q.property⟩ k : G) ∈ Q
        rw [normalizerMonoidHom_apply_apply_coe]
        exact Q.mul_mem (Q.mul_mem q.property hk) (Q.inv_mem q.property)
      · change e _ = e (K.normalizerMonoidHom _ (e.symm (e k)))
        rw [e.symm_apply_apply]
    apply eq_of_le_of_card_ge hle
    exact (card_map_of_injective (α q).injective).ge
  have hfix (q : Q) (a : BinaryCarrier n hn) (ha : a ∈ A.map e.toMonoidHom) : α q a = a := by
    obtain ⟨a,ha,rfl⟩ := ha
    change e (K.normalizerMonoidHom _ (e.symm (e a))) = e a
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr
      ((mem_centralizer_iff.mp (hQA q.property) a (mem_map_of_mem K.subtype ha)).symm)
  have hcard : Nat.card (A.map e.toMonoidHom) = 16 := (card_map_of_injective e.injective).trans hA
  have hne : A.map e.toMonoidHom ≠ ⊥ := by intro hh; rw [hh,card_bot] at hcard; omega
  obtain ⟨B,hB,hd⟩ := fixed_root_scalar_normalizers n hn α hα
    (A.map e.toMonoidHom) hAZ hne hfix
  refine ⟨B,by simpa only [hcard] using hB,?_⟩
  intro t
  let k : K := e.symm (scalar (binaryParameters n hn) rfl t.val)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro x ⟨q,hq,rfl⟩
    let q₀ : Q := ⟨q,hq⟩
    let β := K.normalizerMonoidHom ⟨q,hQN hq⟩
    have hmem : e (k * (β k)⁻¹) ∈ unipotent (binaryParameters n hn) := by
      have hh := hd t q₀
      change scalar (binaryParameters n hn) rfl t.val * (e (β (e.symm (scalar (binaryParameters n hn) rfl t.val))))⁻¹ ∈ unipotent (binaryParameters n hn) at hh
      simpa only [map_mul,map_inv,k,e.apply_symm_apply] using hh
    rw [←hU] at hmem
    obtain ⟨y,hy,he⟩ := hmem
    have hdisp : k * (β k)⁻¹ ∈ Q.subgroupOf K := (e.injective he) ▸ hy
    have hh := Q.mul_mem hdisp hq
    change (k : G) * (β k : K).val⁻¹ * q ∈ Q at hh
    rw [normalizerMonoidHom_apply_apply_coe] at hh
    change (k : G) * q * (k : G)⁻¹ ∈ Q
    simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  · exact (card_map_of_injective (MulAut.conj (k : G)).injective).ge

open Theory.GroupTheory DoubledBinaryPureScalars

/-- The actual scalar normalizers contradict the pure-line image bound. -/
theorem triality_exclusion
    {G : Type*} [Group G] [Finite G] (W U K A Q : Subgroup G)
    (hAW : A ≤ W) (hKC : K ≤ centralizer (U : Set G))
    (hAN : A ≤ normalizer (K : Set G)) (hQN : Q ≤ normalizer (K : Set G))
    (hQW : Q ≤ centralizer (W : Set G)) (hp : IsPGroup 2 Q)
    (hNQ : normalizer (Q : Set G) ≤ normalizer (W : Set G))
    (he : Nat.card (ChapterE.inducedAutomizer W (centralizer (U : Set G))) ∣ 24)
    (j : A →* K ⧸ center K) (hj : Nat.card j.range = 16)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    (hAP : j.range ≤ (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _))
    (hi : ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
      (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _)).index ≤ 2)
    (hz : center K = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hm : IsTrialityGroupAt (2^n) (K ⧸ center K)) : False := by
  have hn0 : 0 < n := by omega
  have hcentral := DoubledBinaryTrialityPlacement.triality_centralizes hn hm _ j.range hAP hi
  obtain ⟨em⟩ := (isTrialityGroupAt_binary_iff _ n hn0).mp hm
  let R₀ := binaryParameters n hn0
  let c := centerlessQuotient hz
  let e₀ := c.trans em
  let R := P.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (BinaryCarrier n hn0) R (unipotentSylow R₀ rfl)
  let e := e₀.trans (MulAut.conj g)
  have hP : (P : Subgroup K).map e.toMonoidHom = unipotent R₀ := by
    change (P : Subgroup K).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom)=_
    rw [←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hQP : Q.subgroupOf K = (P : Subgroup K) := by
    apply P.is_maximal' hp.comap_subtype
    intro k hk
    exact hPQ (mem_map_of_mem K.subtype hk)
  let A₀ := j.range.map c.symm.toMonoidHom
  have hA₀ : Nat.card A₀ = 16 := (card_map_of_injective c.symm.injective).trans hj
  have hA₀map : A₀.map c.toMonoidHom = j.range := by
    change (j.range.map c.symm.toMonoidHom).map c.toMonoidHom = _
    rw [map_map]
    rw [show c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id _ by
      ext x; exact c.apply_symm_apply x,map_id]
  have hAZ : A₀ ≤ (center P).map (P : Subgroup K).subtype := by
    apply (map_le_map_iff_of_injective (f := c.toMonoidHom) c.injective).mp
    rw [hA₀map]
    have hh := map_embeddedCenter (P : Subgroup K) c.toMonoidHom c.injective
    rw [hh]
    exact hcentral
  have hAZe : A₀.map e.toMonoidHom ≤ highestRoot R₀ := by
    have hh := map_mono (f := e.toMonoidHom) hAZ
    rwa [map_embeddedCenter _ _ e.injective,hP,embedded_center_unipotent R₀ rfl] at hh
  obtain ⟨B,hB,hBQ⟩ := ambient_scalar_normalizers n hn0 K Q hQN e
    (by rw [hQP,hP]) A₀ hA₀ hAZe
    (original_fixed_inner_image K A Q hz hAN hQN
      (hQW.trans (centralizer_le hAW)) j hact)
  let b : B →* K := e.symm.toMonoidHom.comp ((scalar R₀ rfl).comp B.subtype)
  have hb (t : B) : e (b t) = scalar R₀ rfl t.val := e.apply_symm_apply _
  have hBW : b.range.map K.subtype ≤ normalizer (W : Set G) := by
    rintro x ⟨k,⟨t,rfl⟩,rfl⟩
    exact hNQ (hBQ t)
  have hne : j.range ≠ ⊥ := by intro hh; rw [hh,card_bot] at hj; omega
  obtain ⟨z,hz,hzne⟩ := j.range.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨a,rfl⟩ := hz
  have haRoot : e (c.symm (j a)) ∈ highestRoot R₀ :=
    hAZe (mem_map_of_mem e.toMonoidHom (mem_map_of_mem c.symm.toMonoidHom
      (show j a ∈ j.range from ⟨a,rfl⟩)))
  rw [←highestHom_range R₀ rfl] at haRoot
  obtain ⟨s,hs⟩ := haRoot
  have hs0 : s.toAdd ≠ 0 := by
    intro hh
    have h1 : e (c.symm (j a)) = 1 := by
      rw [←hs]; change highestHom R₀ rfl s = 1
      have he : s = 1 := hh
      rw [he,map_one]
    exact hzne (c.symm.injective ((e.injective (h1.trans (map_one e).symm)).trans (map_one c.symm).symm))
  have hbound := torus_card_dvd W U K A hAW hKC hAN he j hact b hBW a (by
    intro t ht
    have hh := (ht.map c.symm.toMonoidHom).map e.toMonoidHom
    have hq : c.symm ((QuotientGroup.mk' (center K)) (b t)) = b t := c.symm_apply_apply _
    change Commute (e (c.symm (j a))) (e (c.symm ((QuotientGroup.mk' (center K)) (b t)))) at hh
    rw [hq,hb,←hs] at hh
    change Commute (highestHom R₀ rfl s) (scalar R₀ rfl t.val) at hh
    have hfix := hh.symm.mul_inv_cancel
    have hscl := NormalizedRootCentralizers.torus_conjugate_highestHom R₀ rfl (1,t.val) s.toAdd
    change scalar R₀ rfl t.val * highestHom R₀ rfl s * (scalar R₀ rfl t.val)⁻¹ = _ at hscl
    have ht' : (t.val : fixedField R₀) * s.toAdd = s.toAdd :=
      congrArg Multiplicative.toAdd (highestHom_injective R₀ rfl (hscl.symm.trans hfix))
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hs0 (ht'.trans (one_mul _).symm))))
  have hfield : Nat.card (fixedField R₀) = 2^n := card_fixedField R₀
  have hsmall := scalar_card_le_three hfield hn0 B hbound
  exact (by decide : ¬ (15 : ℕ) ≤ 3) (hB.trans hsmall)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureTrialityExclusion
