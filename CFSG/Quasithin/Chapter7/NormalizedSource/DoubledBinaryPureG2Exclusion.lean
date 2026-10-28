module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureScalars
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryG2Placement
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelAction
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription


/-!
# G2 scalar exclusion for the original pure-line component

The fixed highest-root parameters of the faithful sixteen produce at least
fifteen scalar units. Their displacement lies in the same component Sylow,
so they normalize the actual ambient two-core. Its normalizer lies in M.
The literal pure-line action has order dividing 24, forcing this odd scalar
group to have order at most three. This excludes the G2 component without
assuming that it centralizes the paired plane.

The scalar and automorphism calculations adapt DoubledBinaryG2Exclusion;
all original Sylow and inner-action maps are retained. Source: Aschbacher–Smith
7.7.3 H1 argument, printed pp.705–706, and 7.7.4, printed p.704.
The G₂ model uses the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The triality model uses GLS3 §§2.4 and 2.5.
-/

public noncomputable section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions Atlas.G2.EvenBorelTorus
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureG2Exclusion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem borel_root_scalar (g : borel (K := F)) :
    ∃ l : Fˣ, ∀ a : F, g.val * rootA a * g.val⁻¹ = rootA ((l : F) * a) := by
  obtain ⟨⟨u,t⟩,hp⟩ := (borelProductEquiv (K := F)).surjective g
  obtain ⟨⟨l,m⟩,ht⟩ := t.property
  have hprod : u.val * torus l m = g.val := by
    have hh : u.val * t.val = g.val := congrArg Subtype.val hp
    change torus l m = t.val at ht
    rwa [ht]
  refine ⟨l*m,fun a => ?_⟩
  rw [←hprod,mul_inv_rev]
  have hc : Commute u.val (rootA (((l : F)*(m : F))*a)) := by
    have hu : u.val ∈ unipotentRange := by simpa only [unipotent_eq_range] using u.property
    obtain ⟨v,hv⟩ := hu
    rw [←hv]
    exact unipotentProduct_commute_rootA v _
  calc
    u.val * torus l m * rootA a * ((torus l m)⁻¹ * u.val⁻¹) =
        u.val * (torus l m * rootA a * (torus l m)⁻¹) * u.val⁻¹ := by group
    _ = rootA (((l : F)*(m : F))*a) := by rw [torus_rootA]; exact hc.mul_inv_cancel
    _ = rootA (((l*m : Fˣ) : F)*a) := rfl

private def fixedUnits {X : Type*} (σ : X → F ≃+* F) : Subgroup Fˣ where
  carrier := {t | ∀ x, σ x (t : F) = t}
  one_mem' := by intro x; exact map_one (σ x)
  mul_mem' := by intro a b ha hb x; simp only [Units.val_mul,map_mul,ha x,hb x]
  inv_mem' := by intro a ha x; simp only [Units.val_inv_eq_inv_val,map_inv₀,ha x]

/-- Ratios of the fixed root parameters supply many scalar actors that commute
with every prescribed field part modulo the original unipotent subgroup. -/
private theorem fixed_root_scalar_normalizers {X : Type*} (hq : 2 < Nat.card F)
    (α : X → MulAut (Model F))
    (hα : ∀ x, (unipotent (K := F)).map (α x).toMonoidHom = unipotent)
    (A : Subgroup (Model F)) (hAZ : A ≤ highestRoot (F := F)) (hA : A ≠ ⊥)
    (hfix : ∀ x, ∀ a ∈ A, α x a = a) :
    ∃ B : Subgroup Fˣ, Nat.card A - 1 ≤ Nat.card B ∧
      ∀ t : B, ∀ x, torus t.val 1 * (α x (torus t.val 1))⁻¹ ∈ unipotent (K := F) := by
  classical
  choose b σ he using fun x => stabilizing_actor_factorization
    (semilinearAction_surjective hq) (α x) (hα x)
  choose l hl using fun x => borel_root_scalar (b x)
  let B := fixedUnits σ
  let c : A → F := fun a => (highestRootEquiv.symm ⟨a.val,hAZ a.property⟩).toAdd
  have hc (a : A) : rootA (c a) = a.val :=
    congrArg Subtype.val (highestRootEquiv.apply_symm_apply ⟨a.val,hAZ a.property⟩)
  have hci : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    exact (hc a).symm.trans ((congrArg rootA hab).trans (hc b))
  have hc1 : c 1 = 0 := by
    apply rootA_injective
    rw [hc,rootA_zero]
    rfl
  have hcz (a : A) (ha : a ≠ 1) : c a ≠ 0 := by
    intro hz
    exact ha (hci (hz.trans hc1.symm))
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hA
  let a₀ : A := ⟨a,ha⟩
  have hc0 : c a₀ ≠ 0 := hcz a₀ (fun hh => hane (congrArg Subtype.val hh))
  have hscalar (x : X) (a : A) : (l x : F) * σ x (c a) = c a := by
    apply rootA_injective
    rw [←hl x,←fieldEquiv_rootA (σ x)]
    have hh := hfix x a.val a.property
    rw [he x] at hh
    change b x * fieldEquiv (σ x) a.val * (b x : Model F)⁻¹ = a.val at hh
    simpa only [hc] using hh
  let r : {a : A // a ≠ 1} → B := fun a =>
    ⟨Units.mk0 (c a.val / c a₀) (div_ne_zero (hcz a.val a.property) hc0),by
      intro x
      change σ x (c a.val / c a₀) = c a.val / c a₀
      rw [map_div₀]
      have hh : ((l x : F)*σ x (c a.val)) / ((l x : F)*σ x (c a₀)) =
          c a.val / c a₀ := by rw [hscalar,hscalar]
      simpa only [mul_div_mul_left _ _ (Units.ne_zero (l x))] using hh⟩
  have hr : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    apply hci
    have hh := congrArg (fun z : B => (z.val : F)) hab
    exact (div_left_inj' hc0).mp hh
  have hcard : Nat.card {a : A // a ≠ 1} = Nat.card A - 1 := by
    let := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  refine ⟨B,hcard ▸ Nat.card_le_card_of_injective r hr,?_⟩
  intro t x
  let u : borel (K := F) := torusSection (t.val,1)
  have hfield : fieldEquiv (σ x) (torus t.val 1) = torus t.val 1 := by
    rw [field_torus]
    congr 1
    · exact Units.ext (t.property x)
    · exact map_one _
  have hact : α x (torus t.val 1) = b x * (torus t.val 1) * (b x : Model F)⁻¹ := by
    rw [he x]
    change b x * fieldEquiv (σ x) (torus t.val 1) * (b x : Model F)⁻¹ = _
    rw [hfield]
  rw [hact]
  change (u * (b x * u * (b x)⁻¹)⁻¹ : borel (K := F)) ∈ radical
  rw [←projection_ker]
  change projection (u * (b x * u * (b x)⁻¹)⁻¹) = 1
  rw [map_mul,map_inv,projection_conj,mul_inv_cancel]

/-- Scalar displacements in the concrete Sylow lift to normalizers of the
original ambient two-group, retaining the original component embedding. -/
private theorem ambient_scalar_normalizers {G : Type*} [Group G] [Finite G]
    (K Q : Subgroup G) (hQN : Q ≤ normalizer (K : Set G))
    (e : K ≃* Model F) (hq : 2 < Nat.card F)
    (hU : (Q.subgroupOf K).map e.toMonoidHom = unipotent)
    (A : Subgroup K) (hA : Nat.card A = 16)
    (hAZ : A.map e.toMonoidHom ≤ highestRoot (F := F))
    (hQA : Q ≤ centralizer (A.map K.subtype : Set G)) :
    ∃ B : Subgroup Fˣ, 15 ≤ Nat.card B ∧
      ∀ t : B, (e.symm (torus t.val 1) : G) ∈ normalizer (Q : Set G) := by
  let α : Q → MulAut (Model F) := fun q =>
    e.symm.trans ((K.normalizerMonoidHom ⟨q.val,hQN q.property⟩).trans e)
  have hα (q : Q) : unipotent.map (α q).toMonoidHom = unipotent := by
    have hle : unipotent.map (α q).toMonoidHom ≤ unipotent := by
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
  have hfix (q : Q) (a : Model F) (ha : a ∈ A.map e.toMonoidHom) : α q a = a := by
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
  obtain ⟨B,hB,hd⟩ := fixed_root_scalar_normalizers hq α hα
    (A.map e.toMonoidHom) hAZ hne hfix
  refine ⟨B,by simpa only [hcard] using hB,?_⟩
  intro t
  let k : K := e.symm (torus t.val 1)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro x ⟨q,hq,rfl⟩
    let q₀ : Q := ⟨q,hq⟩
    let β := K.normalizerMonoidHom ⟨q,hQN hq⟩
    have hmem : e (k * (β k)⁻¹) ∈ unipotent := by
      have hh := hd t q₀
      change torus t.val 1 * (e (β (e.symm (torus t.val 1))))⁻¹ ∈ unipotent at hh
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
theorem g2_exclusion
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
    [IsQuasisimple K] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2^n)) : False := by
  have hn4 := DoubledBinaryG2Placement.g2_degree_ge_four hn hm _ j.range hj hAP hi
  have hz := DoubledBinaryG2Placement.g2_center_eq_bot hn4 hm
  have hcentral := DoubledBinaryG2Placement.g2_centralizes hn hm _ j.range hAP hi
  obtain ⟨F,_,_,hF,⟨em⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hbig : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  let c := centerlessQuotient hz
  let e₀ := c.trans em
  let R := P.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) R (sylow (F := F))
  let e := e₀.trans (MulAut.conj g)
  have hP : (P : Subgroup K).map e.toMonoidHom = unipotent (K := F) := by
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
  have hAZe : A₀.map e.toMonoidHom ≤ highestRoot (F := F) := by
    have hh := map_mono (f := e.toMonoidHom) hAZ
    rwa [map_embeddedCenter _ _ e.injective,hP,unipotent_center] at hh
  obtain ⟨B,hB,hBQ⟩ := ambient_scalar_normalizers K Q hQN e hbig
    (by rw [hQP,hP]) A₀ hA₀ hAZe
    (original_fixed_inner_image K A Q hz hAN hQN
      (hQW.trans (centralizer_le hAW)) j hact)
  let b : B →* K := e.symm.toMonoidHom.comp
    (((torusHom (K := F)).comp (MonoidHom.inl Fˣ Fˣ)).comp B.subtype)
  have hb (t : B) : e (b t) = torus t.val 1 := e.apply_symm_apply _
  have hBW : b.range.map K.subtype ≤ normalizer (W : Set G) := by
    rintro x ⟨k,⟨t,rfl⟩,rfl⟩
    exact hNQ (hBQ t)
  have hne : j.range ≠ ⊥ := by intro hh; rw [hh,card_bot] at hj; omega
  obtain ⟨z,hz,hzne⟩ := j.range.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨a,rfl⟩ := hz
  have haRoot : e (c.symm (j a)) ∈ highestRoot (F := F) :=
    hAZe (mem_map_of_mem e.toMonoidHom (mem_map_of_mem c.symm.toMonoidHom
      (show j a ∈ j.range from ⟨a,rfl⟩)))
  obtain ⟨s,hs⟩ := haRoot
  have hs0 : s.toAdd ≠ 0 := by
    intro hh
    have h1 : e (c.symm (j a)) = 1 := by
      rw [←hs]; change rootA s.toAdd = 1; rw [hh,rootA_zero]
    exact hzne (c.symm.injective ((e.injective (h1.trans (map_one e).symm)).trans (map_one c.symm).symm))
  have hbound := torus_card_dvd W U K A hAW hKC hAN he j hact b hBW a (by
    intro t ht
    have hh := (ht.map c.symm.toMonoidHom).map e.toMonoidHom
    have hq : c.symm ((QuotientGroup.mk' (center K)) (b t)) = b t := c.symm_apply_apply _
    change Commute (e (c.symm (j a))) (e (c.symm ((QuotientGroup.mk' (center K)) (b t)))) at hh
    rw [hq,hb,←hs] at hh
    change Commute (rootA s.toAdd) (torus t.val 1) at hh
    have hfix := hh.symm.mul_inv_cancel
    rw [torus_rootA] at hfix
    have ht' : (t.val : F) * s.toAdd = s.toAdd := by simpa using rootA_injective hfix
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hs0 (ht'.trans (one_mul _).symm))))
  have hsmall := scalar_card_le_three hF (by omega : 0 < n) B hbound
  exact (by decide : ¬ (15 : ℕ) ≤ 3) (hB.trans hsmall)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureG2Exclusion
