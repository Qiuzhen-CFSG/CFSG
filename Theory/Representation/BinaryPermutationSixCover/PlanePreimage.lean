module
public import Theory.Representation.BinaryPermutationSixCover.Facts
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Plane preimages in the five-dimensional A₆ augmentation module

A two-perfect group acts on a binary plane through an odd group, so its
normal two-core fixes the plane. An even involution on six letters has a
fixed letter. At that letter, a displacement belonging to the constant
line vanishes, and therefore every lift of a fixed natural vector is fixed.
Together these facts show that the two-core of an actual A₄ actor fixes
the entire augmentation preimage of any invariant natural plane.

Source: Aschbacher–Smith, Lemma 13.3.14(g), printed p.893. The module here
is the actual five-dimensional augmentation core for A₆.
-/

public section
open Subgroup Representation
namespace BinaryPermutation.SixCover
private theorem twoCore_le_ker_permThree {G : Type*} [Group G] [Finite G]
    (hG : IsPPerfect 2 G) (f : G →* Equiv.Perm (Fin 3)) : pCore 2 G ≤ f.ker := by
  have hres : f.range ≤ pResidual 2 (Equiv.Perm (Fin 3)) := by
    have h := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 G).mpr hG] at h
    rintro x ⟨g,rfl⟩
    exact h ⟨g,trivial,rfl⟩
  have halt : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  let P := (pCore 2 G).map f
  have hP : P ≤ alternatingGroup (Fin 3) := (map_le_range _ _).trans (hres.trans halt)
  have hp : IsPGroup 2 P := pCore_isPGroup.map f
  have hc : Nat.card P ∣ 3 := by
    have h := card_dvd_of_le hP
    have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    rwa [hthree] at h
  have hbot : P = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases hp.card_eq_or_dvd with he | he
    · exact he
    · have := he.trans hc
      norm_num at this
  exact (Subgroup.map_eq_bot_iff _).mp hbot

private theorem twoCore_fixes_card_four {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hG : IsPPerfect 2 G) (ρ : Representation (ZMod 2) G W)
    (hc : Nat.card W = 4) (g : G) (hg : g ∈ pCore 2 G) (v : W) : ρ g v = v := by
  classical
  let _ := Fintype.ofFinite W
  let Q := {v : W // v ≠ 0}
  have hQ : Nat.card Q = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hc]
  let e : Q ≃ Fin 3 := (Finite.equivFin Q).trans (finCongr hQ)
  let p : G →* Equiv.Perm W := {
    toFun g := {
      toFun := ρ g
      invFun := ρ g⁻¹
      left_inv v := by simp [← Module.End.mul_apply, ← map_mul]
      right_inv v := by simp [← Module.End.mul_apply, ← map_mul] }
    map_one' := by ext v; simp
    map_mul' g h := by ext v; simp }
  let q : G →* Equiv.Perm Q := {
    toFun g := Equiv.Perm.subtypePerm (p g) (fun v => by
      change ρ g v ≠ 0 ↔ v ≠ 0
      exact not_congr (by
        constructor
        · intro hv
          have hh := congrArg (ρ g⁻¹) hv
          simpa [← Module.End.mul_apply, ← map_mul] using hh
        · intro hv; simp [hv]))
    map_one' := by ext v; change ρ 1 v.val = v.val; simp
    map_mul' g h := by ext v; change ρ (g*h) v.val = ρ g (ρ h v.val); simp }
  let f := e.permCongrHom.toMonoidHom.comp q
  have hfg : f g = 1 := twoCore_le_ker_permThree hG f hg
  have hqg : q g = 1 := e.permCongrHom.injective (hfg.trans (map_one e.permCongrHom.toMonoidHom).symm)
  by_cases hv : v = 0
  · simp [hv]
  exact congrArg Subtype.val (Equiv.congr_fun hqg (⟨v,hv⟩ : Q))


theorem core_fixed_of_natural_fixed_of_fixed_point
    (g : Equiv.Perm (Fin 6)) (i : Fin 6) (hi : g i = i)
    (v : core (Fin 6))
    (hv : naturalRepresentation (Fin 6) g (coreToNatural (Fin 6) v) = coreToNatural (Fin 6) v) :
    coreRepresentation (Fin 6) g v = v := by
  have he := congrArg (fun w : natural (Fin 6) => w.val) hv
  have hc : representation (Fin 6) g v.val - v.val ∈ constants (Fin 6) :=
    (Submodule.Quotient.eq _).mp he
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  have hii : g.symm i = i := by
    apply g.injective
    simpa using hi.symm
  have hci := congrFun hc i
  have hc0 : c = 0 := by
    simpa only [Pi.smul_apply,smul_eq_mul,allOne,mul_one,Pi.sub_apply,
      representation_apply,hii,sub_self] using hci
  apply Subtype.ext
  apply sub_eq_zero.mp
  change representation (Fin 6) g v.val - v.val = 0
  rw [← hc,hc0,zero_smul]

private theorem even_six_involution_fixed_point
    (g : alternatingGroup (Fin 6)) (hg : g ^ 2 = 1) :
    ∃ i : Fin 6, g.val i = i := by
  classical
  by_contra hf
  push Not at hf
  have hne : g ≠ 1 := by
    intro he
    have := hf 0
    simp [he] at this
  have ho : orderOf (g : Equiv.Perm (Fin 6)) = 2 :=
    (Subgroup.orderOf_coe g).trans (orderOf_eq_prime hg hne)
  obtain ⟨r, hr⟩ := Equiv.Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hr
  have hs : (g : Equiv.Perm (Fin 6)).support = Finset.univ := by
    ext i
    simp [Equiv.Perm.mem_support, hf i]
  have hsum := (g : Equiv.Perm (Fin 6)).sum_cycleType
  rw [hr, hs] at hsum
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    Finset.card_univ, Fintype.card_fin] at hsum
  have hr2 : r = 2 := by omega
  have hsign := Equiv.Perm.mem_alternatingGroup.mp g.property
  rw [Equiv.Perm.sign_of_cycleType', hr, hr2] at hsign
  norm_num at hsign


theorem core_plane_preimage_fixed {D : Type*} [Group D] [Finite D]
    (hD : IsPPerfect 2 D) (f : D →* alternatingGroup (Fin 6))
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hE : Nat.card E = 4)
    (hinv : ∀ g : D, ∀ v ∈ E, alternatingNaturalRepresentation (Fin 6) (f g) v ∈ E)
    (g : D) (hg : g ∈ pCore 2 D) (hg2 : f g ^ 2 = 1)
    (v : core (Fin 6)) (hv : coreToNatural (Fin 6) v ∈ E) :
    alternatingCoreRepresentation (Fin 6) (f g) v = v := by
  let σ := (alternatingNaturalRepresentation (Fin 6)).comp f
  let q : D →* Representation.BinaryOffender.subspaceStabilizer σ E :=
    (MonoidHom.id D).codRestrict _ (fun g =>
      Representation.BinaryOffender.le_subspaceStabilizer σ E
        (A := ⊤) (fun a _ v hv => hinv a v hv) (mem_top g))
  let τ := (Representation.BinaryOffender.stabilizerRepresentation σ E).comp q
  have hfix := twoCore_fixes_card_four hD τ hE g hg
    (⟨coreToNatural (Fin 6) v,hv⟩ : E)
  have hvfix : naturalRepresentation (Fin 6) (f g).val (coreToNatural (Fin 6) v) =
      coreToNatural (Fin 6) v := congrArg Subtype.val hfix
  obtain ⟨i,hi⟩ := even_six_involution_fixed_point (f g) hg2
  exact core_fixed_of_natural_fixed_of_fixed_point (f g).val i hi v hvfix

private theorem core_image_square_of_four {D : Type*} [Group D] [Finite D]
    (f : D →* alternatingGroup (Fin 6))
    (e : f.range ≃* alternatingGroup (Fin 4))
    (g : D) (hg : g ∈ pCore 2 D) : f g ^ 2 = 1 := by
  let q := e.toMonoidHom.comp f.rangeRestrict
  have hq : Function.Surjective q := e.surjective.comp f.rangeRestrict_surjective
  have hn : ((pCore 2 D).map q).Normal := Normal.map inferInstance q hq
  have hp : IsPGroup 2 ((pCore 2 D).map q) := pCore_isPGroup.map q
  have hle : (pCore 2 D).map q ≤ pCore 2 (alternatingGroup (Fin 4)) :=
    le_sSup ⟨hn,hp⟩
  have hqg := hle (mem_map_of_mem q hg)
  rw [AlternatingFourPair.twoCore_eq_kleinFour] at hqg
  have hpow := Subgroup.pow_exponent_eq_one hqg
  rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by norm_num)] at hpow
  have hx : (f.rangeRestrict g) ^ 2 = 1 := e.injective (by simpa [q] using hpow)
  exact congrArg Subtype.val hx

theorem four_actor_core_plane_preimage_fixed {D : Type*} [Group D] [Finite D]
    (hD : IsPPerfect 2 D) (f : D →* alternatingGroup (Fin 6))
    (e : f.range ≃* alternatingGroup (Fin 4))
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hE : Nat.card E = 4)
    (hinv : ∀ g : D, ∀ v ∈ E, alternatingNaturalRepresentation (Fin 6) (f g) v ∈ E)
    (g : D) (hg : g ∈ pCore 2 D)
    (v : core (Fin 6)) (hv : coreToNatural (Fin 6) v ∈ E) :
    alternatingCoreRepresentation (Fin 6) (f g) v = v :=
  core_plane_preimage_fixed hD f E hE hinv g hg (core_image_square_of_four f e g hg) v hv
end BinaryPermutation.SixCover
