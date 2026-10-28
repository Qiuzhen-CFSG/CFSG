module

public import Glauberman.SylowAutomorphisms.NormalComplement.FusionGeometry.Setup
public import Stellmacher.OmegaOneCenterMap

/-!
# Local fusion geometry in the generated semidirect product

Transport Q and its odd mover from H = G ⋊ U to K = G ⋊ ⟨U,x⟩.
The local group is literally J = N_K(Q) ∩ N_K(C_T(Q)); its invariant
subgroups are V = Ω₁(Z(C_T(Q))) and W = V ∩ G = V ∩ S. We prove
that U and W are complementary inside V, that J normalizes V and W,
and that the actor belongs to J and centralizes W. The actual Sylow
subgroup of J is a separate index-and-normalizer construction.

Source: Glauberman, Math. Z. 93 (1966), Theorem 1(b), p.158,
DOI 10.1007/BF01111033. The ambient omega-center API uses its standard
intrinsic definition followed by the actual subgroup inclusion.
-/

public section
namespace Glauberman.SylowAutomorphisms.NormalComplement.FusionGeometry
open Subgroup SemidirectProduct
open scoped IsMulCommutative
universe u
variable {G A : Type u} [Group G] [Group A]

@[expose] def actorImage (φ : A →* MulAut G) (d : OddDisplacement A) :
    Subgroup (Extension φ d) :=
  (restrictedDisplacement d).subgroup.map (inr : actors d →* Extension φ d)

@[expose] def sylowImage (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s) :
    Subgroup (Extension φ d) := (twoSylow φ d S hfix).map (inclusion φ d)

@[expose] def localCentralizer (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) : Subgroup (Extension φ d) :=
  sylowImage φ d S hfix ⊓ centralizer (Q.map (inclusion φ d) : Set (Extension φ d))

@[expose] def localNormalizer (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) : Subgroup (Extension φ d) :=
  normalizer (Q.map (inclusion φ d) : Set (Extension φ d)) ⊓
    normalizer (localCentralizer φ d S hfix Q : Set (Extension φ d))

@[expose] noncomputable def omegaCenter (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) : Subgroup (Extension φ d) :=
  Stellmacher.omegaOneCenterAmbient (localCentralizer φ d S hfix Q)

@[expose] noncomputable def basePart (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) : Subgroup (Extension φ d) :=
  omegaCenter φ d S hfix Q ⊓ (inl : G →* Extension φ d).range

theorem actors_le_normalizer (d : OddDisplacement A) :
    actors d ≤ normalizer (d.subgroup : Set A) :=
  sup_le d.subgroup.le_normalizer (zpowers_le.mpr d.normalizes)

theorem restricted_subgroup_normal (d : OddDisplacement A) :
    (restrictedDisplacement d).subgroup.Normal :=
  normal_subgroupOf_of_le_normalizer (actors_le_normalizer d)

theorem mem_sylowImage (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (k : Extension φ d) :
    k ∈ sylowImage φ d S hfix ↔ k.left ∈ S ∧ (k.right : A) ∈ d.subgroup := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, h.right.property⟩
  · rintro ⟨hl, hr⟩
    exact ⟨⟨k.left, ⟨k.right, hr⟩⟩, hl, SemidirectProduct.ext rfl (Subtype.ext rfl)⟩

theorem localCentralizer_eq_map (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) :
    localCentralizer φ d S hfix Q =
      ((twoSylow φ d S hfix : Subgroup (TwoExtension φ d)) ⊓
        centralizer (Q : Set (TwoExtension φ d))).map (inclusion φ d) := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hk, rfl⟩, hc⟩
    refine ⟨k, ⟨hk, mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro q hq
    apply inclusion_injective φ d
    simpa only [map_mul] using mem_centralizer_iff.mp hc _ (mem_map.mpr ⟨q, hq, rfl⟩)
  · rintro _ ⟨k, ⟨hk, hc⟩, rfl⟩
    refine ⟨⟨k, hk, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    simpa only [map_mul] using congrArg (inclusion φ d) (mem_centralizer_iff.mp hc q hq)

theorem actor_mem_center_twoSylow (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (a : d.subgroup) : (inr a : TwoExtension φ d) ∈
      (center (twoSylow φ d S hfix)).map
        (twoSylow φ d S hfix : Subgroup (TwoExtension φ d)).subtype := by
  refine ⟨⟨inr a, S.one_mem⟩, mem_center_iff.mpr ?_, rfl⟩
  intro k
  exact Subtype.ext (actor_central_in_twoSylow φ d S hfix a k k.property)

theorem mover_mem_localNormalizer (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (t : d.subgroup) (w : SylowCentralFusion.Witness (twoSylow φ d S hfix) (inr t)) :
    inclusion φ d w.mover ∈ localNormalizer φ d S hfix w.subgroup := by
  constructor
  · exact w.subgroup.le_normalizer_map (inclusion φ d) ⟨w.mover, w.normalizes, rfl⟩
  · rw [localCentralizer_eq_map]
    exact ((twoSylow φ d S hfix : Subgroup (TwoExtension φ d)) ⊓
      centralizer (w.subgroup : Set (TwoExtension φ d))).le_normalizer_map
        (inclusion φ d) ⟨w.mover, w.normalizes_centralizer, rfl⟩

theorem mover_mem_base (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (t : d.subgroup) (w : SylowCentralFusion.Witness (twoSylow φ d S hfix) (inr t)) :
    inclusion φ d w.mover ∈ (inl : G →* Extension φ d).range := by
  obtain ⟨g, hg⟩ := odd_mem_base φ d w.mover w.odd_order
  exact ⟨g, (inclusion_inl φ d g).symm.trans (congrArg (inclusion φ d) hg)⟩

theorem mover_moves (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (t : d.subgroup) (w : SylowCentralFusion.Witness (twoSylow φ d S hfix) (inr t)) :
    inclusion φ d w.mover * inr (⟨t, mem_sup_left t.property⟩ : actors d) *
      (inclusion φ d w.mover)⁻¹ ≠ inr (⟨t, mem_sup_left t.property⟩ : actors d) := by
  intro he
  apply w.moves
  apply inclusion_injective φ d
  simpa only [map_mul, map_inv, inclusion_inr] using he

theorem sylowImage_commutes_actor (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (a : actors d) (ha : a ∈ (restrictedDisplacement d).subgroup)
    (k : Extension φ d) (hk : k ∈ sylowImage φ d S hfix) :
    k * inr a = inr a * k := by
  obtain ⟨h, hh, rfl⟩ := hk
  have he := congrArg (inclusion φ d)
    (actor_central_in_twoSylow φ d S hfix (⟨a, ha⟩ : d.subgroup) h hh)
  simpa only [map_mul, inclusion_inr] using he

theorem actorImage_le_omegaCenter (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) (hQ : Q ≤ twoSylow φ d S hfix) :
    actorImage φ d ≤ omegaCenter φ d S hfix Q := by
  let _ := (restrictedDisplacement d).elementary
  rintro _ ⟨a, ha, rfl⟩
  apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (mem_sylowImage φ d S hfix _).mpr ⟨S.one_mem, ha⟩
  · apply mem_centralizer_iff.mpr
    intro q hq
    exact sylowImage_commutes_actor φ d S hfix a ha q (map_mono hQ hq)
  · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha, map_one]
  · intro q hq
    exact sylowImage_commutes_actor φ d S hfix a ha q hq.1

theorem omegaCenter_le_sylowImage (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) :
    omegaCenter φ d S hfix Q ≤ sylowImage φ d S hfix := by
  intro k hk
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hk).1.1

theorem localNormalizer_normalizes_omegaCenter (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) :
    localNormalizer φ d S hfix Q ≤ normalizer (omegaCenter φ d S hfix Q : Set _) := by
  intro j hj
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Stellmacher.omegaOneCenterAmbient _).map _ = Stellmacher.omegaOneCenterAmbient _
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective
    (MulAut.conj j : Extension φ d →* Extension φ d) (MulAut.conj j).injective,
    mem_normalizer_iff_map_conj_eq.mp hj.2]

theorem localNormalizer_normalizes_basePart (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) :
    localNormalizer φ d S hfix Q ≤ normalizer (basePart φ d S hfix Q : Set _) := by
  have hN : (inl : G →* Extension φ d).range.Normal := by
    rw [range_inl_eq_ker_rightHom]
    infer_instance
  exact (le_inf (localNormalizer_normalizes_omegaCenter φ d S hfix Q)
    (show localNormalizer φ d S hfix Q ≤ normalizer
      ((inl : G →* Extension φ d).range : Set _) from le_normalizer_of_normal)).trans
        inf_normalizer_le_normalizer_inf

theorem basePart_eq_inf_sylow (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) :
    basePart φ d S hfix Q = omegaCenter φ d S hfix Q ⊓
      (S : Subgroup G).map (inl : G →* Extension φ d) := by
  apply le_antisymm
  · rintro k ⟨hk, ⟨g, rfl⟩⟩
    refine ⟨hk, g, ?_, rfl⟩
    exact ((mem_sylowImage φ d S hfix _).mp (omegaCenter_le_sylowImage φ d S hfix Q hk)).1
  · rintro k ⟨hk, g, hg, rfl⟩
    exact ⟨hk, g, rfl⟩

theorem basePart_isCompl_actorImage (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) (hQ : Q ≤ twoSylow φ d S hfix) :
    IsCompl ((basePart φ d S hfix Q).subgroupOf (omegaCenter φ d S hfix Q))
      ((actorImage φ d).subgroupOf (omegaCenter φ d S hfix Q)) := by
  let V := omegaCenter φ d S hfix Q
  let W := basePart φ d S hfix Q
  have hUV := actorImage_le_omegaCenter φ d S hfix Q hQ
  refine ⟨disjoint_iff_inf_le.mpr ?_, codisjoint_iff_le_sup.mpr ?_⟩
  · intro v hv
    change v = 1
    apply Subtype.ext
    obtain ⟨a, ha, he⟩ := hv.2
    have hr : (rightHom : Extension φ d →* actors d) (v : Extension φ d) = 1 := by
      have hb := hv.1.2
      rwa [range_inl_eq_ker_rightHom] at hb
    have ha1 : a = 1 := by
      simpa only [rightHom_inr] using (congrArg rightHom he).trans hr
    exact he.symm.trans (by rw [ha1, map_one]; rfl)
  · intro v _
    have hvT := (mem_sylowImage φ d S hfix _).mp (omegaCenter_le_sylowImage φ d S hfix Q v.property)
    have hu : (inr v.val.right : Extension φ d) ∈ actorImage φ d :=
      ⟨v.val.right, hvT.2, rfl⟩
    let u : V := ⟨inr v.val.right, hUV hu⟩
    let w : V := v * u⁻¹
    have hw : (w : Extension φ d) ∈ W := by
      refine ⟨w.property, ?_⟩
      rw [range_inl_eq_ker_rightHom]
      change (v.val * (inr v.val.right)⁻¹).right = 1
      simp
    have he : v = w * u := by simp [w]
    rw [he]
    exact mul_mem_sup (show w ∈ W.subgroupOf V from hw)
      (show u ∈ (actorImage φ d).subgroupOf V from hu)

theorem actor_centralizes_basePart (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) (a : actors d) :
    (inr a : Extension φ d) ∈ centralizer (basePart φ d S hfix Q : Set _) := by
  apply mem_centralizer_iff.mpr
  intro w hw
  rw [basePart_eq_inf_sylow] at hw
  obtain ⟨g, hg, rfl⟩ := hw.2
  apply SemidirectProduct.ext
  · change g * (extensionAction φ d) 1 1 = 1 * (extensionAction φ d) a g
    rw [map_one, mul_one, one_mul]
    exact (hfix a g hg).symm
  · simp

private theorem actor_conj_mem_of_between (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (R : Subgroup (Extension φ d)) (hUR : actorImage φ d ≤ R)
    (hRT : R ≤ sylowImage φ d S hfix) (a : actors d) (k : Extension φ d) (hk : k ∈ R) :
    inr a * k * (inr a)⁻¹ ∈ R := by
  have hkT := (mem_sylowImage φ d S hfix k).mp (hRT hk)
  have hu : (inr k.right : Extension φ d) ∈ R := hUR ⟨k.right, hkT.2, rfl⟩
  have hl : (inl k.left : Extension φ d) ∈ R := by
    have he : k * (inr k.right)⁻¹ = inl k.left :=
      mul_inv_eq_iff_eq_mul.mpr (inl_left_mul_inr_right k).symm
    exact he ▸ R.mul_mem hk (R.inv_mem hu)
  have hc : a * k.right * a⁻¹ ∈ (restrictedDisplacement d).subgroup :=
    (mem_normalizer_iff.mp (actors_le_normalizer d a.property) (k.right : A)).mp hkT.2
  have he : inr a * k * (inr a)⁻¹ = inl k.left * inr (a * k.right * a⁻¹) := by
    apply SemidirectProduct.ext
    · change (1 * (extensionAction φ d) a k.left) *
        (extensionAction φ d) (a * k.right) ((extensionAction φ d) a⁻¹ 1⁻¹) =
        k.left * (extensionAction φ d) 1 1
      simp only [inv_one, map_one, mul_one, one_mul]
      exact hfix a k.left hkT.1
    · simp
  rw [he]
  exact R.mul_mem hl (hUR ⟨a * k.right * a⁻¹, hc, rfl⟩)

theorem actor_normalizes_of_between (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (R : Subgroup (Extension φ d)) (hUR : actorImage φ d ≤ R)
    (hRT : R ≤ sylowImage φ d S hfix) (a : actors d) :
    (inr a : Extension φ d) ∈ normalizer (R : Set _) := by
  apply mem_normalizer_iff.mpr
  intro k
  constructor
  · exact actor_conj_mem_of_between φ d S hfix R hUR hRT a k
  · intro hk
    have he := actor_conj_mem_of_between φ d S hfix R hUR hRT a⁻¹ _ hk
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using he

theorem actor_mem_localNormalizer (φ : A →* MulAut G) (d : OddDisplacement A)
    (S : Sylow 2 G) (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (Q : Subgroup (TwoExtension φ d)) (hQ : Q ≤ twoSylow φ d S hfix)
    (hZ : (center (twoSylow φ d S hfix)).map
      (twoSylow φ d S hfix : Subgroup (TwoExtension φ d)).subtype ≤ Q)
    (a : actors d) : (inr a : Extension φ d) ∈ localNormalizer φ d S hfix Q := by
  have hUQ : actorImage φ d ≤ Q.map (inclusion φ d) := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨inr (⟨b, hb⟩ : d.subgroup), hZ (actor_mem_center_twoSylow φ d S hfix _), ?_⟩
    rfl
  refine ⟨actor_normalizes_of_between φ d S hfix _ hUQ (map_mono hQ) a,
    actor_normalizes_of_between φ d S hfix _ ?_ inf_le_left a⟩
  intro k hk
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp
    (actorImage_le_omegaCenter φ d S hfix Q hQ hk)).1

end Glauberman.SylowAutomorphisms.NormalComplement.FusionGeometry
