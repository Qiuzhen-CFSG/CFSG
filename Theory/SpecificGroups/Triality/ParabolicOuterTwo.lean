module
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Stabilizer
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LocalKernel
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PCoreKernelRange

/-!
# Local quotient actions in triality automorphism extensions

The original two-core quotients are centerless through their proved root Levi
identifications. This remains true under any faithful embedding of the carrier.
For a two-group normalizing an embedded local factor, the kernel of conjugation
on that factor's literal two-core quotient is therefore the extended two-core.
If a Sylow subgroup acts by inner automorphisms, it is the product of this core
and its intersection with the local factor, with all images in one ambient group.

The coefficient actions, actual stabilizers and exhaustive q = 2 extension
exclusion are re-exported. The normalizer and semilinear calculations detect
every two-element in the local action kernel as local conjugation. Faithful
conjugation in an actual normal extension therefore identifies its extended
core with the original embedded local core, and hence with the embedded root
radical. Both nodes and all positive binary exponents are covered. The source
factorization follows with this same local core; no core equality or extra
semilinear-action premise remains in the normal-extension application.

Source: Aschbacher–Smith F.1.12, printed p.264 (`refs/quasithin.pdf`), and
GLS3 §§2.5–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics Subgroup
open scoped MatrixGroups

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv, Subgroup.map_bot, hz]

/-- Both actual local two-core quotients are centerless, including at q = 2. -/
theorem localQuotient_center_eq_bot (P : Parameters) (hp : P.prime = 2) (a : Node) :
    center (LocalTwoQuotient P a) = ⊥ := by
  cases a with
  | arms =>
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    exact center_eq_bot_of_equiv
      ((localFactorArmsQuotientEquivPSL2 P hp).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      (Theory.PSL2.sl2_center_eq_bot _)
  | central =>
    let : CharP (GaloisField P.prime P.exponent) 2 :=
      hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    exact center_eq_bot_of_equiv
      ((localFactorCentralQuotientEquivPSL2 P hp).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      (Theory.PSL2.sl2_center_eq_bot _)

/-- Centerlessness is retained through the literal embedding in an ambient extension. -/
theorem embeddedLocalQuotient_center_eq_bot {E : Type*} [Group E]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* E) (hι : Function.Injective ι) :
    center (((localFactor P a).map ι) ⧸ pCore 2 ((localFactor P a).map ι)) = ⊥ := by
  let e := (localFactor P a).equivMapOfInjective ι hι
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact center_eq_bot_of_equiv q.symm (localQuotient_center_eq_bot P hp a)

/-- The original local two-core in the very same ambient extension is the embedded
root radical. The two embeddings are composed explicitly. -/
theorem embeddedLocal_core {E : Type*} [Group E]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* E) (hι : Function.Injective ι) :
    ((localFactor P a).map ι).pCoreIn 2 = (radical P a).map ι := by
  let f := ι.comp (localFactor P a).subtype
  have hrange : f.range = (localFactor P a).map ι := by
    rw [MonoidHom.range_comp, range_subtype]
  have h := pCoreIn_range_of_injective 2 f
    (hι.comp (localFactor P a).subtype_injective)
  rw [hrange] at h
  exact h.trans ((Subgroup.map_map (pCore 2 (localFactor P a))
    ι (localFactor P a).subtype).symm.trans
      (congrArg (Subgroup.map ι) (localFactor_twoCore_map P hp a)))

/-- The kernel of the actual local action is the extended two-core. -/
theorem embeddedLocalAction_kernel {E : Type*} [Group E]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* E) (hι : Function.Injective ι)
    (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor P a).map ι)) :
    (pCoreJoinAction 2 hSL).ker = pCore 2 ((localFactor P a).map ι ⊔ S : Subgroup E) :=
  pCoreJoinAction_kernel 2 hSL hS (embeddedLocalQuotient_center_eq_bot P hp a ι hι)

/-- Inner action on a local quotient gives the source Sylow factorization, with all
three subgroups embedded in E. This general embedding lemma does not need a
faithful action of the whole ambient group on the triality carrier. -/
theorem embeddedLocal_sylow_factorization {E : Type*} [Group E] [Finite E]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* E) (hι : Function.Injective ι)
    (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor P a).map ι))
    (T : Sylow 2 ((localFactor P a).map ι ⊔ S : Subgroup E))
    (hinner : (T : Subgroup _).map (pCoreJoinAction 2 hSL) ≤
      MulAut.innerSubgroup (((localFactor P a).map ι) ⧸ pCore 2 ((localFactor P a).map ι))) :
    (T : Subgroup _).map ((localFactor P a).map ι ⊔ S).subtype =
      ((localFactor P a).map ι ⊔ S).pCoreIn 2 ⊔
        ((T : Subgroup _).map ((localFactor P a).map ι ⊔ S).subtype ⊓ (localFactor P a).map ι) := by
  let L := (localFactor P a).map ι
  let H := L ⊔ S
  let f := pCoreJoinAction 2 hSL
  have hkernel : f.ker = pCore 2 H := embeddedLocalAction_kernel P hp a ι hι S hS hSL
  have hLimage : (L.subgroupOf H).map f = MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    apply le_antisymm
    · rintro σ ⟨l, hl, rfl⟩
      let l₀ : L := ⟨l.val, hl⟩
      have he : inclusion (show L ≤ H from le_sup_left) l₀ = l := Subtype.ext rfl
      rw [← he, pCoreJoinAction_on_component]
      exact ⟨_, rfl⟩
    · rintro σ ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
      exact ⟨inclusion le_sup_left l, l.property, pCoreJoinAction_on_component 2 hSL l⟩
  have hfact := f.sylow_eq_pCore_sup_inf_of_image_le T (L.subgroupOf H)
    (hkernel.symm ▸ (pCore_isPGroup (p := 2) (G := H)))
    (pCore_range_eq_bot_of_ker_eq_pCore 2 f hkernel) (hinner.trans hLimage.ge)
  have hmap := congrArg (Subgroup.map H.subtype) hfact
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)] at hmap
  exact hmap

/-- The source S = O₂(LᵢS)(S ∩ Lᵢ), when the given S is the Sylow image.
The join is the subgroup product, since the first factor is normal in LᵢS. -/
theorem embeddedLocal_source_factorization {E : Type*} [Group E] [Finite E]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* E) (hι : Function.Injective ι)
    (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor P a).map ι))
    (T : Sylow 2 ((localFactor P a).map ι ⊔ S : Subgroup E))
    (hT : (T : Subgroup _).map ((localFactor P a).map ι ⊔ S).subtype = S)
    (hinner : (T : Subgroup _).map (pCoreJoinAction 2 hSL) ≤
      MulAut.innerSubgroup (((localFactor P a).map ι) ⧸ pCore 2 ((localFactor P a).map ι))) :
    S = ((localFactor P a).map ι ⊔ S).pCoreIn 2 ⊔ (S ⊓ (localFactor P a).map ι) := by
  simpa only [hT] using embeddedLocal_sylow_factorization P hp a ι hι S hS hSL T hinner

/-- Cores agree in any faithful, compatible automorphism extension. -/
theorem embeddedLocal_twoCore_eq_of_action {E : Type*} [Group E]
    (n : ℕ) (hn : 0 < n) (a : Node)
    (ι : BinaryCarrier n hn →* E) (hι : Function.Injective ι)
    (ρ : E →* MulAut (BinaryCarrier n hn)) (hρ : Function.Injective ρ)
    (hc : ∀ x g, ι (ρ x g) = x * ι g * x⁻¹)
    (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor (binaryParameters n hn) a).map ι)) :
    ((localFactor (binaryParameters n hn) a).map ι ⊔ S).pCoreIn 2 =
      ((localFactor (binaryParameters n hn) a).map ι).pCoreIn 2 := by
  let P := binaryParameters n hn
  let L := (localFactor P a).map ι
  let H := L ⊔ S
  have hHL : H ≤ normalizer L := sup_le L.le_normalizer hSL
  let : (L.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHL
  have hiρ (g : Carrier P) : ρ (ι g) = MulAut.conj g := by
    ext y
    apply hι
    rw [hc, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hstab (x : H) : ρ x.val ∈ localStabilizer P a := by
    apply (mem_localStabilizer P a _).mpr
    apply map_injective hι
    have hf : ι.comp (ρ x.val).toMonoidHom = (MulAut.conj x.val).toMonoidHom.comp ι := by
      ext g
      exact hc x.val g
    rw [map_map, hf, ← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hHL x.property)
  let r : H →* localStabilizer P a := (ρ.comp H.subtype).codRestrict _ hstab
  let e := (localFactor P a).equivMapOfInjective ι hι
  let Q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let f := pCoreJoinAction 2 hSL
  have equivariance (x : H) (z : LocalTwoQuotient P a) :
      Q (localQuotientAction P a (r x) z) = f x (Q z) := by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (localFactor P a)) z
    rw [localQuotientAction_mk]
    change QuotientGroup.mk' (pCore 2 L) (e (localRestriction P a (r x) l)) =
      f x (QuotientGroup.mk' (pCore 2 L) (e l))
    rw [pCoreJoinAction_mk]
    apply congrArg (QuotientGroup.mk' (pCore 2 L))
    apply Subtype.ext
    exact hc x.val l.val
  have hker : f.ker = pCore 2 H := embeddedLocalAction_kernel P rfl a ι hι S hS hSL
  have hkle : f.ker ≤ L.subgroupOf H := by
    intro x hx
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨x, hker ▸ hx⟩
    have hrpow : r x ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      exact (congrArg r (congrArg Subtype.val hk)).trans (map_one r)
    have hact : localQuotientAction P a (r x) = 1 := by
      ext z
      apply Q.injective
      rw [equivariance, show f x = 1 from hx]
      rfl
    obtain ⟨l, hl⟩ := local_inner_twoElement n hn a (r x) k hrpow
      (hact ▸ (MulAut.innerSubgroup (LocalTwoQuotient P a)).one_mem)
    have he : ι l.val = x.val := by
      apply hρ
      rw [hiρ]
      exact congrArg Subtype.val hl
    exact ⟨l.val, l.property, he⟩
  exact pCoreIn_eq_of_action_kernel_le 2 L H le_sup_left f
    (hker.symm ▸ (pCore_isPGroup (p := 2) (G := H)))
    (pCore_range_eq_bot_of_ker_eq_pCore 2 f hker) hkle

/-- The actual normal-copy source extension: no additional action or core premise. -/
theorem normalExtension_local_twoCore_eq {E : Type*} [Group E]
    (K : Subgroup E) [K.Normal] (n : ℕ) (hn : 0 < n)
    (e : K ≃* BinaryCarrier n hn) (hC : centralizer (K : Set E) = ⊥)
    (a : Node) (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom))) :
    ((localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom) ⊔ S).pCoreIn 2 =
      ((localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)).pCoreIn 2 := by
  apply embeddedLocal_twoCore_eq_of_action n hn a _
    (K.subtype_injective.comp e.symm.injective) (normalExtensionAction K n hn e)
    (normalExtensionAction_injective K n hn e hC) _ S hS hSL
  intro x g
  change (e.symm (e (MulAut.conjNormal x (e.symm g))) : E) = _
  rw [e.symm_apply_apply]
  rfl

/-- Both core images are the same embedded root radical. -/
theorem normalExtension_local_twoCore_radical {E : Type*} [Group E]
    (K : Subgroup E) [K.Normal] (n : ℕ) (hn : 0 < n)
    (e : K ≃* BinaryCarrier n hn) (hC : centralizer (K : Set E) = ⊥)
    (a : Node) (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom))) :
    ((localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom) ⊔ S).pCoreIn 2 =
      (radical (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom) :=
  (normalExtension_local_twoCore_eq K n hn e hC a S hS hSL).trans
    (embeddedLocal_core _ rfl a _ (K.subtype_injective.comp e.symm.injective))

open Theory.GroupTheory.AutomorphismExtensionBorel

/-- Literal subgroups of the full automorphism group use their original inner embedding. -/
theorem automorphismExtension_local_twoCore_eq (n : ℕ) (hn : 0 < n)
    (E : Subgroup (MulAut (BinaryCarrier n hn)))
    (hE : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ E)
    (a : Node) (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor (binaryParameters n hn) a).map (innerEmbedding E hE))) :
    ((localFactor (binaryParameters n hn) a).map (innerEmbedding E hE) ⊔ S).pCoreIn 2 =
      ((localFactor (binaryParameters n hn) a).map (innerEmbedding E hE)).pCoreIn 2 := by
  apply embeddedLocal_twoCore_eq_of_action n hn a _ (carrierEmbedding_injective n hn E hE)
    E.subtype E.subtype_injective _ S hS hSL
  intro x g
  apply Subtype.ext
  ext y
  simp [innerEmbedding]

/-- Local inner action gives the source factorization with the original local core. -/
theorem normalExtension_source_factorization {E : Type*} [Group E] [Finite E]
    (K : Subgroup E) [K.Normal] (n : ℕ) (hn : 0 < n)
    (e : K ≃* BinaryCarrier n hn) (hC : centralizer (K : Set E) = ⊥)
    (a : Node) (S : Subgroup E) (hS : IsPGroup 2 S)
    (hSL : S ≤ normalizer ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom)))
    (T : Sylow 2 ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom) ⊔ S : Subgroup E))
    (hT : (T : Subgroup _).map ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom) ⊔ S).subtype = S)
    (hinner : (T : Subgroup _).map (pCoreJoinAction 2 hSL) ≤
      MulAut.innerSubgroup (((localFactor (binaryParameters n hn) a).map
        (K.subtype.comp e.symm.toMonoidHom)) ⧸
          pCore 2 ((localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)))) :
    S = ((localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)).pCoreIn 2 ⊔
      (S ⊓ (localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)) := by
  rw [← normalExtension_local_twoCore_eq K n hn e hC a S hS hSL]
  exact embeddedLocal_source_factorization _ rfl a _ (K.subtype_injective.comp e.symm.injective)
    S hS hSL T hT hinner

end Triality.Standard.ParabolicOuterTwo
